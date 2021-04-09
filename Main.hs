module Main where
import CCS
import Text.Parsec
import System.Environment
import Text.Read hiding (step)
import System.Console.Haskeline
import Control.Monad.Catch

main :: IO ()
main = getArgs >>= \args ->
 case args of 
   [fn] -> do
      text <- readFile fn
      case parse parser fn text of 
        Left e -> print e
        Right decls -> do
          putStrLn (unlines (map prettyDecl decls))
          let envs = toEnvs decls
          runInputT defaultSettings $ mainLoop envs Nothing
   _ -> runInputT defaultSettings $ mainLoop (toEnvs []) Nothing


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
          Just p -> outputStrLn (unwords (map prettyAction (available (es,ss,fs) p))) >> mainLoop envs proc
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
      outputStrLn $ unlines (map (\(n, p) -> show n ++ ": " ++ pretty (snd p)) (zip [0..] ms))
      number' <- getInputLine "? "
      case maybe Nothing readMaybe number' of 
        Just n | n < length ms -> let (ss',p') = ms !! n in outputStrLn (pretty p') >> mainLoop (es,fs,ss') (Just p')
        _ -> chooseNext ms
 
