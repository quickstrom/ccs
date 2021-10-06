{-# LANGUAGE LambdaCase #-}
module CCS where
import qualified Data.Map as M
import Data.List
import Text.Parsec hiding (State)
import qualified Text.Parsec.Token as T
import qualified Data.Char as C
import Text.Parsec.Language
import Text.Parsec.Expr
import Control.Monad(guard)
import Control.Exception (throw, Exception)

data Action' e n = Action Name [e]
                 | Coaction Name [n]
                 | Tau
                 deriving (Show)

type Position = SourcePos

type Action = Action' Expr Name

data Name = N Position String deriving (Show)

nameOf :: Name -> String
nameOf (N _ s) = s

posOf :: Name -> Position
posOf (N p _) = p


newtype CCSError = E String deriving (Show)

instance Exception CCSError

eerror :: String -> a
eerror = throw . E


data Value = I Integer | B Bool | S String | Null deriving (Eq, Show)
data Op = Plus | Minus | Times | Divide | Modulo | LessEq | Less | GreaterEq | Greater | NotEqual | Equal | And | Or | Not | Concat deriving (Show)

data Expr = Lit Value | Prim Position Op [Expr] | Call Name [Expr] | If Position Expr Expr Expr | Var Name
          deriving (Show)

data CCS = Act Action CCS 
         | Guard Expr CCS 
         | Assignment Name Expr CCS 
         | Choice CCS CCS 
         | Parallel CCS CCS
         | Restrict CCS Name
         | Relabel CCS Name Name
         | Process Name [Expr]
         | Stop
          deriving (Show)


data Decl = Equation Name [Name] CCS
          | StateVar Name Expr
          | Function Name [Name] Expr
          deriving (Show)

prettyAction :: Action -> String
prettyAction (Action n []) = nameOf n
prettyAction (Coaction n []) = "'" ++ nameOf n
prettyAction Tau = "tau"
prettyAction (Action n args) = nameOf n ++ "(" ++ intercalate ", " (map prettyExpr args) ++ ")"
prettyAction (Coaction n args) = "'" ++  nameOf n ++ "(" ++ intercalate ", " (map nameOf args) ++ ")"

prettyExpr :: Expr -> String
prettyExpr (Lit l) = prettyLit l
prettyExpr (Prim p Not [e]) = "!" ++ prettyExpr e
prettyExpr (Prim p o [e1,e2]) = "(" ++ prettyExpr e1 ++ " " ++ opSym o ++ " " ++ prettyExpr e2 ++ ")" 
  where 
    opSym x = case x of 
      Plus -> "+" 
      Minus -> "-" 
      Times -> "*" 
      Divide -> "/" 
      Modulo -> "%" 
      LessEq -> "<=" 
      Less -> "<" 
      GreaterEq -> ">=" 
      Greater -> ">" 
      NotEqual -> "!=" 
      Equal -> "==" 
      And -> "&&" 
      Or -> "||" 
      Concat -> "." 
      Not -> "!"
prettyExpr (Call n es) = nameOf n ++ "(" ++ intercalate ", " (map prettyExpr es)  ++ ")"
prettyExpr (If _ e1 e2 e3) = "(if " ++ prettyExpr e1 ++ " then " ++ prettyExpr e2 ++ " else " ++ prettyExpr e3 ++ ")" 
prettyExpr (Var n) = nameOf n

prettyLit (I i) = show i
prettyLit (B b) = if b then "true" else "false"
prettyLit (S s) = show s

pretty :: CCS -> String
pretty (Act act p) = prettyAction act ++ "." ++ pretty p
pretty (Guard e p) = "[" ++ prettyExpr e ++ "]" ++ pretty p
pretty (Assignment n e p) = "{" ++ nameOf n ++ " := " ++ prettyExpr e ++ "}" ++ pretty p
pretty (Choice p q) = "(" ++ pretty p ++ " + " ++ pretty q ++ ")"
pretty (Parallel p q) = "(" ++ pretty p ++ " | " ++ pretty q ++ ")"
pretty (Restrict p n) = pretty p ++ "\\" ++ nameOf n
pretty (Relabel p n m) = pretty p ++ "[" ++ nameOf n ++ "/" ++ nameOf m ++ "]"
pretty (Process n []) = nameOf n
pretty (Process n es) = nameOf n ++ "(" ++ intercalate ", " (map prettyExpr es)  ++ ")"
pretty Stop = "0"

prettyDecl :: Decl -> String
prettyDecl (Equation n [] p) = nameOf n ++ " = " ++ pretty p  ++ ";"
prettyDecl (Equation n ns p) = nameOf n ++ "(" ++ intercalate ", " (map nameOf ns)  ++ ") = " ++ pretty p  ++ ";"
prettyDecl (StateVar n e) = "var " ++ nameOf n ++ " = " ++ prettyExpr e ++ ";"
prettyDecl (Function n ns p) = "fun " ++ nameOf n ++ "(" ++ intercalate  ", " (map nameOf ns)  ++ ") = " ++ prettyExpr p  ++ ";"

type State = M.Map String Value
type Functions = M.Map String ([Name], Expr)
type Equations = M.Map String ([Name], CCS)

evaluate :: State -> Functions -> Expr -> Value
evaluate s fs (Lit v) = v
evaluate s fs (Prim pos o es) = case (o, map (evaluate s fs) es) of
  (Plus, [I i, I j]) -> I (i + j)
  (Minus, [I i, I j]) -> I (i - j)
  (Times, [I i, I j]) -> I (i * j)
  (Divide, [I i, I j]) -> I (i `div` j)
  (Modulo, [I i, I j]) -> I (i `mod` j)
  (LessEq, [I i, I j]) -> B (i <= j)
  (GreaterEq, [I i, I j]) -> B (i >= j)
  (Less, [I i, I j]) -> B (i < j)
  (Greater, [I i, I j]) -> B (i > j)
  (And, [B i, B j]) -> B (i && j)
  (Or, [B i, B j]) -> B (i || j)
  (Not, [B i]) -> B (not i)
  (Concat, [S i, S j]) -> S (i ++ j)
  (Equal, [i, j]) -> B (i == j)
  (NotEqual, [i, j]) -> B (i /= j)
  (o, args) -> eerror $ show pos ++ ": Type error, primop " ++ show o ++ " cannot take arguments " ++ intercalate ", " (map prettyLit args)
evaluate s fs (Call n es) = case M.lookup (nameOf n) fs of 
  Nothing -> eerror $ show (posOf n) ++ ": Function " ++ show (nameOf n) ++ " not found"
  Just (args,body) | length args == length es -> 
                         let s' = M.union (M.fromList (zip (map nameOf args) (map (evaluate s fs) es))) s 
                          in evaluate s' fs body
                   | otherwise -> eerror $ show (posOf n) ++ ": Incorrect number of parameters for function " ++ show (nameOf n)
evaluate s fs (If pos e1 e2 e3) = case evaluate s fs e1 of 
  B True -> evaluate s fs e2
  B False -> evaluate s fs e3
  _       -> eerror $ show pos ++ ": If expects a boolean condition."
evaluate s fs (Var n) = case M.lookup (nameOf n) s of 
  Just v -> v
  Nothing -> eerror $ show (posOf n) ++ ": Variable " ++ show (nameOf n) ++ " not found"

isComm (Action a ls) (Coaction a' ts) = nameOf a == nameOf a' && length ls == length ts
isComm (Coaction a ls) (Action a' ts) = nameOf a == nameOf a' && length ls == length ts
isComm _ _ = False

available :: (Equations, Functions, State) -> CCS -> [Action]
available (_,fs,s) (Act (Action n es)  _) = [Action n (map (Lit . evaluate s fs) es)]
available _ (Act a _) = [a]
available env@(_, fs, s) (Guard g p) = case evaluate s fs g of
  B True -> available env p
  _      -> []
available env@(es, fs, s) (Assignment n e p) = if M.member (nameOf n) s then
   available (es,fs,M.insert (nameOf n) (evaluate s fs e) s) p
 else eerror (show (posOf n) ++ ": State variable " ++ nameOf n ++ " not declared/initialised")
available env (Choice p q) = available env p ++ available env q
available env (Parallel p q) = 
  let a1 = available env p 
      a2 = available env q
      comm = map (const Tau) (filter (uncurry isComm) ((,) <$> a1 <*> a2))
   in a1 ++ a2 ++ comm
available env (Restrict p n) = filter (restrict (nameOf n)) (available env p)
  where
   restrict n (Action a _) | n == nameOf a = False
   restrict n (Coaction a _) | n == nameOf a = False
   restrict _ _ = True
available env (Relabel p n m) = map (rename (nameOf m)) (available env p)
  where
   rename m (Action a args) | m == nameOf a = Action n args
   rename m (Coaction a args) | m == nameOf a = Coaction n args
   rename _ a = a
available (es,fs,s) (Process n args) = case M.lookup (nameOf n) es of
   Nothing -> eerror $ show (posOf n) ++ ": cannot find process " ++ nameOf n
   Just (names,body)
     | length names /= length args -> eerror $ show (posOf n) ++ ": process " ++ nameOf n ++ " takes a different number of arguments"
     | otherwise -> available (es,fs,s) $ substitute (zip (map nameOf names) (map (Lit . evaluate s fs) args)) body
        
available _ Stop = []

type Step = Action' Value Value

substituteAction :: [(String, Expr)] -> Action -> Action
substituteAction s (Action n es) = Action n (map (substituteExpr s) es)
substituteAction s a = a

substituteExpr s (Prim pos o es) = Prim pos o (map (substituteExpr s) es)
substituteExpr s (Call n es) = Call n (map (substituteExpr s) es)
substituteExpr s (If pos e1 e2 e3)  = If pos (substituteExpr s e1) (substituteExpr s e2) (substituteExpr s e3)
substituteExpr s (Var n) = case lookup (nameOf n) s of
  Just val -> val
  _        -> Var n
substituteExpr s e = e



substitute :: [(String, Expr)] -> CCS -> CCS
substitute s (Act a p) = Act (substituteAction s a) (substitute (deshadow s) p)
  where
    names = case a of Coaction _ ns ->  map nameOf ns; _ -> []
    deshadow = filter ((`notElem` names) . fst)
substitute s (Guard e p) = Guard (substituteExpr s e) (substitute s p)
substitute s (Assignment n e p) = Assignment n (substituteExpr s e) (substitute s p)
substitute s (Choice p q) = Choice (substitute s p) (substitute s q)
substitute s (Parallel p q) = Parallel (substitute s p) (substitute s q)
substitute s (Restrict p n) = Restrict (substitute s p) n
substitute s (Relabel p n m) = Relabel (substitute s p) n m
substitute s (Process n es) = Process n (map (substituteExpr s) es)
substitute s Stop = Stop

evalAction :: State -> Functions -> Action' Expr Expr -> Step
evalAction s fs (Action n es) = Action n (map (evaluate s fs) es)
evalAction s fs (Coaction n es) = Coaction n (map (evaluate s fs) es)
evalAction s fs Tau = Tau

step :: (Equations, Functions) -> (State, CCS) -> Step -> [(State, CCS)] 
step (_,fs) (s, Act (Action a exprs) p) (Action a' vals)
  | nameOf a == nameOf a' && map (evaluate s fs) exprs == vals = [(s,p)]
  | otherwise = []
step (_,fs) (s, Act (Coaction a names) p) (Coaction a' vals)
  | nameOf a == nameOf a' && length names == length vals = [(s, substitute (zip (map nameOf names) (map Lit vals)) p)]
  | otherwise = []
step _ (_, Act {}) _ = []
step env@(_, fs) (s, Guard g p) act = case evaluate s fs g of
  B True -> step env (s, p) act
  _      -> []
step env@(_,fs) (s, Assignment n e p) act = if M.member (nameOf n) s then
   step env (M.insert (nameOf n) (evaluate s fs e) s, p) act
 else eerror (show (posOf n) ++ ": State variable " ++ nameOf n ++ " not declared/initialised")
step env (s, Choice a b) act = step env (s,a) act ++ step env (s,b) act
step env@(es,fs) (s, Parallel a b) act
   = map (fmap (`Parallel` b)) (step env (s,a) act)
  ++ map (fmap (a `Parallel`)) (step env (s,b) act)
  ++ case act of Tau -> communication ; _ -> []
 where
  a1 = available (es,fs,s) a 
  a2 = available (es,fs,s) b
  communication = concatMap communicate $ filter (uncurry isComm) ((,) <$> a1 <*> a2)
  communicate (Action n es, Coaction m ns) = do
       let vals = map (evaluate s fs) es
       (s', a') <- step env (s, a) (Action n vals)
       (s'', b') <- step env (s', b) (Coaction m vals)
       pure (s'', Parallel a' b')
  communicate (Coaction n ns, Action m es) = do
       let vals = map (evaluate s fs) es
       (s', a') <- step env (s, a) (Coaction n vals)
       (s'', b') <- step env (s', b) (Action m vals)
       pure (s'', Parallel a' b')
  communicate _ = error "impossible"
step env (s, Restrict p n) act = case act of
   Action n' _ | nameOf n == nameOf n' -> [] 
   Coaction n' _ | nameOf n == nameOf n' -> [] 
   _ -> map (fmap (`Restrict` n)) (step env (s,p) act)
step env (s, Relabel p n m) (Action n' args ) | nameOf n == nameOf n' = map (fmap (\p -> Relabel p n m)) (step env (s,p) (Action m args))
step env (s, Relabel p n m) (Coaction n' args ) | nameOf n == nameOf n' = map (fmap (\p -> Relabel p n m)) (step env (s,p) (Coaction m args))
step env (s, Relabel p n m) act = map (fmap (\p -> Relabel p n m)) (step env (s,p) act)
step env@(es,fs) (s, Process n args) act = case M.lookup (nameOf n) es of 
   Nothing -> eerror $ show (posOf n) ++ ": Process not found " ++ nameOf n
   Just (ns, body) | length ns /= length args -> eerror $ show (posOf n) ++ ": Process " ++ nameOf n ++ " doesn't have the right number of arguments"
   Just (ns, body) -> let vals = map (evaluate s fs) args in step env (s, substitute (zip (map nameOf ns) (map Lit vals)) body) act
step _ (_, Stop) _ = []
--step _ (_, p) a = error $ show (p,a)

toEnvs :: [Decl] -> (Equations, Functions, State)
toEnvs ds = let es = foldMap (\case Equation n args b -> M.fromList [(nameOf n,(args,b))]; _ -> M.empty) ds
                fs = foldMap (\case Function n args b -> M.fromList [(nameOf n,(args,b))]; _ -> M.empty) ds
                ss = foldMap (\case StateVar n e -> M.fromList [(nameOf n, evaluate ss fs e)]; _ -> M.empty) ds
             in (es,fs,ss)


(white, parser, expression, process, valAction) = (ws, tl, expr, ccs, action')
  where
    tl = do ws
            ds <- many decl
            eof
            return ds
    ws = T.whiteSpace lexer
    decl =  Equation <$> upperName <*> argList <* equals <*> ccs <* semi
        <|> StateVar <$ keyword "var" <*> upperName <* equals <*> expr <* semi
        <|> Function <$ keyword "fun" <*> lowerName <*> argList' <* equals <*> expr <* semi
        <?> "declaration"

    argList =  T.parens lexer (T.commaSep lexer lowerName)
           <|> pure []
           <?> "argument list"

    argList' =  T.parens lexer (T.commaSep lexer lowerName)
            <?> "argument list"

    exprList =  T.parens lexer (T.commaSep lexer expr)
            <|> pure []
            <?> "expression list"

    exprList' =  T.parens lexer (T.commaSep lexer expr)
             <?> "expression list"

    expr = buildExpressionParser exprTable exprTerm
        <|> If <$> getPosition <* keyword "if" <*> expr <* keyword "then" <*> expr <* keyword "else" <*> expr
        <?> "expression"

    exprTerm = T.parens lexer expr
        <|> Var <$> upperName
        <|> try (Call <$> lowerName <*> exprList')
        <|> Var <$> lowerName 
        <|> Lit <$> literal
        <?> "simple expression"

    literal =  I <$> T.integer lexer
           <|> B True <$ keyword "true"
           <|> B False <$ keyword "false"
           <|> Null <$ keyword "null"
           <|> S <$> T.stringLiteral lexer

    exprTable = [ [Prefix $ do pos <- getPosition; T.reservedOp lexer "!"; return (\x -> Prim pos Not [x]) ]
                , [primop "*" Times AssocLeft, primop "/" Divide AssocLeft, primop "%" Modulo AssocLeft]
                , [primop "+" Plus AssocLeft, primop "-" Minus AssocLeft]
                , [primop "." Concat AssocLeft]
                , [ primop "==" Equal AssocNone
                  , primop "!=" NotEqual AssocNone
                  , primop "<=" LessEq AssocNone
                  , primop "<" Less AssocNone 
                  , primop ">=" GreaterEq AssocNone
                  , primop ">" Greater AssocNone
                  ]
                , [primop "&&" And AssocLeft]
                , [primop "||" Or AssocLeft]
                ]

    ccs = buildExpressionParser ccsTable (ccsSubterm >>= ccsTerm)
       <?> "process expression"

    ccsAtom = T.parens lexer ccs
        <|> Process <$> upperName <*> exprList
        <|> Stop <$ T.symbol lexer "0"
        <?> "simple expression"


    ccsSubterm = do
         Act <$> action <* T.reservedOp lexer "." <*> ccsSubterm
     <|> Guard <$> T.brackets lexer expr <*> ccsSubterm
     <|> T.braces lexer (Assignment <$> upperName <* T.reservedOp lexer ":=" <*> expr) <*> ccsSubterm
     <|> ccsAtom

    ccsTerm st = do
      (restrictPostfix st >>= ccsTerm) <|> (renamePostfix st >>= ccsTerm) <|> pure st

    ccsTable = [ 
                 [binary "+" Choice AssocLeft]
               , [binary "|" Parallel AssocLeft]
               ]

    action' = Tau <$ keyword "tau"
          <|> Action <$> lowerName <*> exprList
          <|> Coaction <$ T.reservedOp lexer "'" <*> lowerName <*> exprList
          <?> "action"

    action = Tau <$ keyword "tau"
          <|> Action <$> lowerName <*> exprList
          <|> Coaction <$ T.reservedOp lexer "'" <*> lowerName <*> argList
          <?> "action"

    restrictPostfix st = Restrict st <$ T.reservedOp lexer "\\" <*> lowerName
    renamePostfix st = T.brackets lexer (Relabel st <$> lowerName <* T.reservedOp lexer "/" <*> lowerName)

    primop name fun assoc = Infix (do{ pos <- getPosition; T.reservedOp lexer name; return (\a b -> Prim pos fun [a,b]) }) assoc
    binary name fun assoc = Infix (do{ T.reservedOp lexer name; return fun }) assoc

    equals = T.reservedOp lexer "="
    semi = T.semi lexer
    keyword = T.reserved lexer
    lowerName = try $ do
       pos <- getPosition
       str@(c:cs) <- T.identifier lexer
       guard $ C.isLower c
       pure (N pos str)

    upperName = try $ do
       pos <- getPosition
       str@(c:cs) <- T.identifier lexer
       guard $ C.isUpper c
       pure (N pos str)
   
    
    lexer = T.makeTokenParser javaStyle { 
              T.reservedNames = ["var", "fun", "tau", "if","then", "else", "true","false", "null"], 
              T.reservedOpNames = ["+","-","!","*","%","==","!=",">=","<=","<",">","||","|","&&","/","\\",":=","'", "=", "."] 
            }


