{-# LANGUAGE LambdaCase, OverloadedStrings,TupleSections #-}
module Main where
import CCS
import Debug.Trace
import Text.Parsec
import Data.Foldable(toList)
import System.Environment ( getArgs )
import Text.Read hiding (step)
import System.Console.Haskeline
import Control.Monad.Catch
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as LB
import qualified Data.Aeson as A
import qualified Data.Aeson.Types as A
import qualified Data.HashMap.Strict as H
import qualified Data.Vector as V
import qualified Data.Text as T
import System.IO
import System.Process 

main :: IO ()
main = getArgs >>= \case
  [fn,proc,check] -> do
    text <- readFile fn
    case parse parser fn text of 
      Left e -> print e
      Right decls -> do
        putStrLn (unlines (map prettyDecl decls))
        let envs = toEnvs decls
        case parse (white >> process) "<input>" proc of 
          Left e -> print e
          Right prc -> do 
            (Just o, Just i, _, _ ) <- createProcess (shell check){std_in = CreatePipe, std_out = CreatePipe}
            checkerLoop envs prc i o
  [fn] -> do
    text <- readFile fn
    case parse parser fn text of 
      Left e -> print e
      Right decls -> do
        putStrLn (unlines (map prettyDecl decls))
        let envs = toEnvs decls
        runInputT defaultSettings $ mainLoop envs Nothing
  _ -> runInputT defaultSettings $ mainLoop (toEnvs []) Nothing


actionJSON ss fs (Action (N _ n) es) = A.object ["id" A..= T.pack n, "args" A..= map (valueJSON . evaluate ss fs) es]
actionJSON ss fs (Coaction (N _ n) xs) = A.object ["id" A..= T.pack ('\'':n), "args" A..= ([] :: [Integer]) ]
actionJSON ss fs Tau = A.object ["id" A..= ("tau" :: T.Text), "args" A..= ([] :: [Integer]) ]

valueJSON (I i) = A.Number (fromIntegral i)
valueJSON (B b) = A.Bool b
valueJSON (S s) = A.String (T.pack s)
valueJSON (Null) = A.Null

jsonValue (A.Number n) = (I $ read $ show n)
jsonValue (A.Bool b) = B b
jsonValue (A.String s) = S (T.unpack s)
jsonValue _ = Null

entag tag obj = A.object ["tag" A..= (tag :: T.Text), "contents" A..= obj]

checkerLoop envs prc i o = flip catch (\(E e) -> putStrLn e) $ do
  bytes <- B.hGetLine i
  let Just (A.Object val) = A.decodeStrict bytes
  let Just (A.Object deps) = H.lookup "dependencies" val
  let vars = H.keys deps
  let parseVar "available" = Right ("available",Right ())
      parseVar body = (body,) . Left <$> parse (white >> expression) "<input>" (T.unpack body)
  case mapM parseVar vars of
    Left e -> print e
    Right vars' -> do 
      let getStateFor ss fs prc k = case k of 
            Right () -> A.Array (V.fromList (map (actionJSON ss fs) (available envs prc)))
            Left exp -> valueJSON (evaluate ss fs exp)
      let getState ss fs prc = H.fromList (map (fmap $ getStateFor ss fs prc) vars')
      let go envs@(es,fs,ss) prc version = do
            bytes <- B.hGetLine i
            print (bytes, version)
            let (Just (A.Object val)) = A.decodeStrict bytes
            let (Just (A.String t)) = H.lookup "tag" val
            case t of
              "End" -> print "Completed"
              "RequestAction" -> do
                let (Just v') = A.parseMaybe A.parseJSON =<< H.lookup "version" val
                if v' /= version then go envs prc version else do
                  let (Just act) = H.lookup "action" val
                  let actions = available envs prc
                  case matchAction ss fs  act actions of 
                    Nothing -> go envs prc version
                    Just action -> case step (es,fs) (ss,prc) action of
                      [] -> go envs prc version
                      ((ss',p'):_) -> do
                        B.hPutStrLn o . LB.toStrict $ A.encode $ entag "Performed" $  getState ss' fs p'
                        hFlush o
                        go (es,fs,ss') p' (succ version)
                      --ms -> chooseNext ms
      let (_,fs,ss) = envs
      B.hPutStrLn o . LB.toStrict $ A.encode $ entag "Event" $ A.Array $ V.fromList [ A.object ["tag" A..= ("Action" :: T.Text), "id" A..= ("ready" :: T.Text), "args" A..= ([] :: [()]), "isEvent" A..= True ], A.Object $ getState ss fs prc ]
      hFlush o
      go envs prc (0 :: Integer)

matchAction :: CCS.State -> Functions -> A.Value -> [Action] -> Maybe Step
matchAction ss fs (A.Object v) (Tau:rest) | H.lookup "id" v == Just "tau" = Just Tau
matchAction ss fs (A.Object v) (a@(Action (N p n) args):rest) | A.Object v' <- actionJSON ss fs a, H.isSubmapOf v' v = Just $ Action (N p n) (map (evaluate ss fs) args)
matchAction ss fs (A.Object v) (a@(Coaction (N p n) args):rest) | H.lookup "id" v == Just (A.String (T.pack n)), Just (A.Array args') <- H.lookup "args" v , length args == length args'
                                                = Just $ Coaction (N p n) (map jsonValue $ toList args')
matchAction ss fs v (_:rest) = matchAction ss fs v rest
matchAction ss fs v [] = Nothing
mainLoop envs@(es,fs,ss) proc = flip catch (\(E e) -> outputStrLn e >> mainLoop envs proc) $ do
  command' <- getInputLine "> "
  flip (maybe $ pure ()) command' $ \command -> do
    let body = dropWhile (/= ' ') command
    let initialCommand = case takeWhile (/= ' ') command of 
                           ":start" -> ":start"
                           ":s" -> ":start"
                           ":available" -> ":available"
                           ":a" -> ":available"
                           ":eval" -> ":eval"
                           ":e" -> ":eval"
                           ":" -> ":eval"
                           ":q" -> ":quit"
                           ":quit" -> ":quit"
                           e   -> e
    case initialCommand of
      ":quit" -> pure ()
      ":start" -> case parse (white >> process) "<input>" body of 
          Left e -> outputStrLn (show e) >> mainLoop envs proc
          Right proc -> outputStrLn (pretty proc) >> mainLoop envs (Just proc)
      ":available" -> case proc of 
          Just p -> outputStrLn (unwords (map prettyAction (available (es,fs,ss) p))) >> mainLoop envs proc
          Nothing -> outputStrLn "No process started" >> mainLoop envs proc
      ":eval" -> case parse (white >> expression) "<input>" body of 
          Left e ->  outputStrLn (show e) >> mainLoop envs proc
          Right exp -> outputStrLn (prettyLit (evaluate ss fs exp)) >> mainLoop envs proc
      _ -> case proc of
          Nothing -> outputStrLn "No process started" >> mainLoop envs proc
          Just p -> case parse (white >> valAction) "<input>" command of
            Left e -> outputStrLn (show e) >> mainLoop envs proc
            Right act -> let act' = evalAction ss fs act in case step (es,fs) (ss,p) act' of
              [] -> outputStrLn "Cannot take action." >> mainLoop envs proc
              [(ss',p')] -> outputStrLn (pretty p') >> mainLoop (es,fs,ss') (Just p')
              ms -> chooseNext ms
  where
    chooseNext ms = do
      outputStrLn "Multiple outcomes, please pick one:"
      outputStrLn $ unlines (zipWith (\n p -> show n ++ ": " ++ pretty (snd p)) [0..] ms)
      number' <- getInputLine "? "
      case readMaybe =<< number' of 
        Just n | n < length ms -> let (ss',p') = ms !! n in outputStrLn (pretty p') >> mainLoop (es,fs,ss') (Just p')
        _ -> chooseNext ms
 
