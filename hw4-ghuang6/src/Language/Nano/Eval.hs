--------------------------
-- | Geoff Huang      | --
-- | ghuang6@ucsc.edu | --
--------------------------

{-# LANGUAGE OverloadedStrings #-}

module Language.Nano.Eval
  ( execFile, execString, execExpr
  , eval, lookupId, prelude
  , parse
  , env0
  )
  where

import Control.Exception (throw, catch)
import Language.Nano.Types
import Language.Nano.Parser

--------------------------------------------------------------------------------
execFile :: FilePath -> IO Value
--------------------------------------------------------------------------------
execFile f = (readFile f >>= execString) `catch` exitError

--------------------------------------------------------------------------------
execString :: String -> IO Value
--------------------------------------------------------------------------------
execString s = execExpr (parseExpr s) `catch` exitError

--------------------------------------------------------------------------------
execExpr :: Expr -> IO Value
--------------------------------------------------------------------------------
execExpr e = return (eval prelude e) `catch` exitError

--------------------------------------------------------------------------------
-- | `parse s` returns the Expr representation of the String s
--
-- >>> parse "True"
-- EBool True
--
-- >>> parse "False"
-- EBool False
--
-- >>> parse "123"
-- EInt 123
--
-- >>> parse "foo"
-- EVar "foo"
--
-- >>> parse "x + y"
-- EBin Plus (EVar "x") (EVar "y")
--
-- >>> parse "if x <= 4 then a || b else a && b"
-- EIf (EBin Le (EVar "x") (EInt 4)) (EBin Or (EVar "a") (EVar "b")) (EBin And (EVar "a") (EVar "b"))
--
-- >>> parse "if 4 <= z then 1 - z else 4 * z"
-- EIf (EBin Le (EInt 4) (EVar "z")) (EBin Minus (EInt 1) (EVar "z")) (EBin Mul (EInt 4) (EVar "z"))
--
-- >>> parse "let a = 6 * 2 in a /= 11"
-- ELet "a" (EBin Mul (EInt 6) (EInt 2)) (EBin Ne (EVar "a") (EInt 11))
--
-- >>> parseTokens "() (  )"
-- Right [LPAREN (AlexPn 0 1 1),RPAREN (AlexPn 1 1 2),LPAREN (AlexPn 3 1 4),RPAREN (AlexPn 6 1 7)]
--
-- >>> parse "f x"
-- EApp (EVar "f") (EVar "x")
--
-- >>> parse "(\\ x -> x + x) (3 * 3)"
-- EApp (ELam "x" (EBin Plus (EVar "x") (EVar "x"))) (EBin Mul (EInt 3) (EInt 3))
--
-- >>> parse "(((add3 (x)) y) z)"
-- EApp (EApp (EApp (EVar "add3") (EVar "x")) (EVar "y")) (EVar "z")
--
-- >>> parse <$> readFile "tests/input/t1.hs"
-- EBin Mul (EBin Plus (EInt 2) (EInt 3)) (EBin Plus (EInt 4) (EInt 5))
--
-- >>> parse <$> readFile "tests/input/t2.hs"
-- ELet "z" (EInt 3) (ELet "y" (EInt 2) (ELet "x" (EInt 1) (ELet "z1" (EInt 0) (EBin Minus (EBin Plus (EVar "x") (EVar "y")) (EBin Plus (EVar "z") (EVar "z1"))))))
--
-- >>> parse "1-2-3"
-- EBin Minus (EBin Minus (EInt 1) (EInt 2)) (EInt 3)
-- >>> parse "1+a&&b||c+d*e-f-g x"
-- EBin Or (EBin And (EBin Plus (EInt 1) (EVar "a")) (EVar "b")) (EBin Minus (EBin Minus (EBin Plus (EVar "c") (EBin Mul (EVar "d") (EVar "e"))) (EVar "f")) (EApp (EVar "g") (EVar "x")))
--
-- >>> parse "1:3:5:[]"
-- EBin Cons (EInt 1) (EBin Cons (EInt 3) (EBin Cons (EInt 5) ENil))
--
-- >>> parse "[1,3,5]"
-- EBin Cons (EInt 1) (EBin Cons (EInt 3) (EBin Cons (EInt 5) ENil))

--------------------------------------------------------------------------------
parse :: String -> Expr
--------------------------------------------------------------------------------
parse = parseExpr

exitError :: Error -> IO Value
exitError (Error msg) = return (VErr msg)

--------------------------------------------------------------------------------
-- | `eval env e` evaluates the Nano expression `e` in the environment `env`
--   (i.e. uses `env` for the values of the **free variables** in `e`),
--   and throws an `Error "unbound variable"` if the expression contains
--   a free variable that is **not bound** in `env`.
--
-- part (a)
--
-- >>> eval env0 (EBin Minus (EBin Plus "x" "y") (EBin Plus "z" "z1"))
-- 0
--
-- >>> eval env0 "p"
-- *** Exception: Error {errMsg = "unbound variable: p"}
--
-- part (b)
--
-- >>> eval []  (EBin Le (EInt 2) (EInt 3))
-- True
--
-- >>> eval []  (EBin Eq (EInt 2) (EInt 3))
-- False
--
-- >>> eval []  (EBin Eq (EInt 2) (EBool True))
-- *** Exception: Error {errMsg = "type error: binop"}
--
-- >>> eval []  (EBin Lt (EInt 2) (EBool True))
-- *** Exception: Error {errMsg = "type error: binop"}
--
-- >>> let e1 = EIf (EBin Lt "z1" "x") (EBin Ne "y" "z") (EBool False)
-- >>> eval env0 e1
-- True
--
-- >>> let e2 = EIf (EBin Eq "z1" "x") (EBin Le "y" "z") (EBin Le "z" "y")
-- >>> eval env0 e2
-- False
--
-- part (c)
--
-- >>> let e1 = EBin Plus "x" "y"
-- >>> let e2 = ELet "x" (EInt 1) (ELet "y" (EInt 2) e1)
-- >>> eval [] e2
-- 3
--
-- part (d)
--
-- >>> eval [] (EApp (ELam "x" (EBin Plus "x" "x")) (EInt 3))
-- 6
--
-- >>> let e3 = ELet "h" (ELam "y" (EBin Plus "x" "y")) (EApp "f" "h")
-- >>> let e2 = ELet "x" (EInt 100) e3
-- >>> let e1 = ELet "f" (ELam "g" (ELet "x" (EInt 0) (EApp "g" (EInt 2)))) e2
-- >>> eval [] e1
-- 102
--
-- part (e)
-- |
-- >>> :{
-- eval [] (ELet "fac" (ELam "n" (EIf (EBin Eq "n" (EInt 0))
--                                  (EInt 1)
--                                  (EBin Mul "n" (EApp "fac" (EBin Minus "n" (EInt 1))))))
--             (EApp "fac" (EInt 10)))
-- :}
-- 3628800
--
-- previous test but in one line:
-- eval [] (ELet "fac" (ELam "n" (EIf (EBin Eq (EVar "n") (EInt 0)) (EInt 1) (EBin Mul (EVar "n") (EApp (EVar "fac") (EBin Minus (EVar "n") (EInt 1)))))) (EApp (EVar "fac") (EInt 10)))
--
-- part (f)
--
-- >>> let el = EBin Cons (EInt 1) (EBin Cons (EInt 2) ENil)
-- >>> execExpr el
-- (1 : (2 : []))
-- >>> execExpr (EApp "head" el)
-- 1
-- >>> execExpr (EApp "tail" el)
-- (2 : [])
--------------------------------------------------------------------------------
eval :: Env -> Expr -> Value
--------------------------------------------------------------------------------
eval env e = 
  case e of
    EInt i            -> VInt i
    EBool b           -> VBool b
    ENil              -> VNil
    EVar x            -> lookupId x env
    EBin binop e1 e2  -> evalOp binop (eval env e1) (eval env e2)
    EIf e1 e2 e3      ->
      case (eval env e1) of
        (VBool True)  -> eval env e2
        (VBool False) -> eval env e3
        _             -> throw (Error ("type error: " ++ show e1 ++ " does not evaluate to a bool"))
    ELet x e1 e2      -> eval env' e2
      where
        env' = ((x, eval env' e1) : env)
    ELam x e          -> VClos env x e
    EApp e1 e2        -> 
      case (eval env e1) of 
        (VClos closEnv x body) -> eval ((x, eval env e2) : closEnv) body
        (VPrim prim)           -> prim (eval env e2)
        _                      -> throw (Error ("type error: " ++ show e1 ++ " does not evaluate to a function"))

    -- another way to write EIf using guards
    -- EIf e1 e2 e3
    --   | predicate == VBool True  -> eval env e2
    --   | predicate == VBool False -> eval env e3
    --   | otherwise                -> throw (Error ("type error: " ++ show e1 ++ " does not evaluate to a bool"))
    --   where
    --     predicate = eval env e1

-- alternate way to write the same thing using multiple function declarations:
-- eval _   (EInt i)           = VInt i
-- eval _   (EBool b)          = VBool b
-- eval _   (ENil)             = VNil
-- eval env (EVar id)          = lookupId id env
-- eval env (EBin op e1 e2)    = evalOp op (eval env e1) (eval env e2)
-- eval env (EIf e1 e2 e3)     = case eval env e1 of
--                               (VBool True)  -> eval env e2
--                               (VBool False) -> eval env e3
--                               _             -> throw (Error ("type error: " ++ show e1 ++ " does not evaluate to a bool"))
-- eval env (ELet id e1 e2)    = eval env' e2
--                               where
--                                 env' = (id, (eval env' e1)):env
-- eval env (ELam id e)        = VClos env id e
-- eval env (EApp f a)         = case eval env f of
--                               (VClos cenv id body) -> eval ((id, (eval env a)):cenv) body
--                               (VPrim p)            -> p (eval env a)
--                               _                    -> throw (Error ("type error: " ++ show e1 ++ " does not evaluate to a function"))

--------------------------------------------------------------------------------
evalOp :: Binop -> Value -> Value -> Value
--------------------------------------------------------------------------------
evalOp Plus  (VInt i1)   (VInt i2)   = VInt  (i1 + i2)
evalOp Minus (VInt i1)   (VInt i2)   = VInt  (i1 - i2)
evalOp Mul   (VInt i1)   (VInt i2)   = VInt  (i1 * i2)
evalOp Div   (VInt i1)   (VInt i2)   = VInt  (i1 `div` i2)
evalOp Eq    (VInt i1)   (VInt i2)   = VBool (i1 == i2)
evalOp Eq    (VBool b1)  (VBool b2)  = VBool (b1 == b2)
evalOp Eq    VNil        VNil        = VBool True
evalOp Eq    VNil        (VPair _ _) = VBool False
evalOp Eq    (VPair _ _) VNil        = VBool False
evalOp Eq    (VPair a b) (VPair x y) = evalOp And (evalOp Eq a x) (evalOp Eq b y)
evalOp Ne    x           y           = if (evalOp Eq x y == VBool True) then VBool False else VBool True
evalOp Lt    (VInt i1)   (VInt i2)   = VBool (i1 < i2)
evalOp Le    (VInt i1)   (VInt i2)   = VBool (i1 <= i2)
evalOp And   (VBool b1)  (VBool b2)  = VBool (b1 && b2)
evalOp Or    (VBool b1)  (VBool b2)  = VBool (b1 || b2)
evalOp Cons  elem        VNil        = VPair elem VNil
evalOp Cons  elem        (VPair h t) = if validList (type_ elem) newList then newList else throw (Error ("type error: " ++ show newList ++ " is not a valid list"))
  where
    newList = VPair elem (VPair h t)
evalOp _     _           _           = throw (Error ("type error: binop"))

-- note: the test cases don't actually check for valid usage of the Cons operator, so you can just have the below implementation from Eval.hs for hw5
-- note that TypeCheck.hs from hw5 will actually catch these incorrect usages of Cons (even though the test cases don't specifically test for it)
-- evalOp Cons  elem        list        = VPair elem list

-- helper function that checks if a Nano Pair is a valid list (all elements have same type t)
validList :: String -> Value -> Bool
validList _ (VNil)   = True
validList t (VPair head tail)
  | type_ head == t  = validList t tail
  | otherwise        = False
validList _ _        = False

-- helper function that returns the type of a Value (as a string)
type_ :: Value -> String
type_ (VInt _)      = "Int"
type_ (VBool _)     = "Bool"
type_ (VPair _ _)   = "Pair"
type_ (VClos _ _ _) = "Clos"
type_ (VNil)        = "Nil"
type_ (VErr _)      = "Err"
type_ (VPrim _)     = "Prim"

--------------------------------------------------------------------------------
-- | `lookupId x env` returns the most recent
--   binding for the variable `x` (i.e. the first
--   from the left) in the list representing the
--   environment, and throws an `Error` otherwise.
--
-- >>> lookupId "z1" env0
-- 0
-- >>> lookupId "x" env0
-- 1
-- >>> lookupId "y" env0
-- 2
-- >>> lookupId "mickey" env0
-- *** Exception: Error {errMsg = "unbound variable: mickey"}
--------------------------------------------------------------------------------
lookupId :: Id -> Env -> Value
--------------------------------------------------------------------------------
lookupId x [] = throw (Error ("unbound variable: " ++ x))
lookupId x ((id, val) : envs)
  | x == id   = val
  | otherwise = lookupId x envs
-- note: almost the same code as assoc from hw2 TailRecursion

prelude :: Env
prelude =
  [ -- HINT: you may extend this "built-in" environment
    -- with some "operators" that you find useful...
    ("head", VPrim (\(VPair h _) -> h))
  , ("tail", VPrim (\(VPair _ t) -> t))
  ]

env0 :: Env
env0 =  [ ("z1", VInt 0)
        , ("x" , VInt 1)
        , ("y" , VInt 2)
        , ("z" , VInt 3)
        , ("z1", VInt 4)
        ]

-- note: if you don't want to use lambda expressions, you can write out functions for head and tail in prelude, shown below

-- head_ :: Value -> Value
-- head_ (VPair a _) = a

-- tail_ :: Value -> Value
-- tail_ (VPair _ b) = b

-- prelude :: Env
-- prelude =
--   [ -- HINT: you may extend this "built-in" environment
--     -- with some "operators" that you find useful...
--     ("head", VPrim head_),
--     ("tail", VPrim tail_)
--   ]

--------------------------------------------------------------------------------