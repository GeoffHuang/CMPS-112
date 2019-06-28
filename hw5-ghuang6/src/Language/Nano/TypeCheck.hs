--------------------------
-- | Geoff Huang      | --
-- | ghuang6@ucsc.edu | --
--------------------------

{-# LANGUAGE FlexibleInstances, OverloadedStrings, BangPatterns #-}

module Language.Nano.TypeCheck where

import Language.Nano.Types
import Language.Nano.Parser

import qualified Data.List as L
import           Text.Printf (printf)  
import           Control.Exception (throw)

--------------------------------------------------------------------------------
typeOfFile :: FilePath -> IO Type
typeOfFile f = readFile f >>= typeOfString

typeOfString :: String -> IO Type
typeOfString s = typeOfExpr (parseExpr s)

typeOfExpr :: Expr -> IO Type
typeOfExpr e = do
  let (!st, t) = infer initInferState preludeTypes e
  if (length (stSub st)) < 0 then throw (Error ("count Negative: " ++ show (stCnt st)))
  else return t

--------------------------------------------------------------------------------
-- Problem 1: Warm-up
--------------------------------------------------------------------------------

-- | Things that have free type variables
class HasTVars a where
  freeTVars :: a -> [TVar]

-- | Type variables of a type
instance HasTVars Type where
  freeTVars TInt        = []
  freeTVars TBool       = []
  freeTVars (t1 :=> t2) = L.nub (freeTVars t1 ++ freeTVars t2)
  freeTVars (TVar id)   = [id]
  freeTVars (TList t)   = freeTVars t

-- | Free type variables of a poly-type (remove forall-bound vars)
instance HasTVars Poly where
  freeTVars (Mono t)      = freeTVars t
  freeTVars (Forall id t) = L.delete id (freeTVars t)

-- | Free type variables of a type environment
instance HasTVars TypeEnv where
  freeTVars gamma   = concat [freeTVars s | (_, s) <- gamma]  
  
-- | Lookup a variable in the type environment  
lookupVarType :: Id -> TypeEnv -> Poly
lookupVarType x [] = throw (Error ("unbound variable: " ++ x))
lookupVarType x ((y, s) : gamma)
  | x == y    = s
  | otherwise = lookupVarType x gamma

-- | Extend the type environment with a new biding
extendTypeEnv :: Id -> Poly -> TypeEnv -> TypeEnv
extendTypeEnv x s gamma = (x,s) : gamma  

-- | Lookup a type variable in a substitution;
--   if not present, return the variable unchanged
lookupTVar :: TVar -> Subst -> Type
lookupTVar a [] = TVar a
lookupTVar a ((id, t) : subs)
  | a == id   = t
  | otherwise = lookupTVar a subs

-- | Remove a type variable from a substitution
removeTVar :: TVar -> Subst -> Subst
removeTVar a sub
  | t == TVar a  = sub
  | otherwise    = L.delete (a, t) sub
  where t = lookupTVar a sub

-- alternate method without using L.delete
-- removeTVar :: TVar -> Subst -> Subst
-- removeTVar _ [] = []
-- removeTVar a ((id, t) : subs)
--   | a == id   = subs
--   | otherwise = (id, t) : removeTVar a subs
     
-- | Things to which type substitutions can be apply
class Substitutable a where
  apply :: Subst -> a -> a
  
-- | Apply substitution to type
instance Substitutable Type where  
  apply _   TInt        = TInt
  apply _   TBool       = TBool
  apply sub (t1 :=> t2) = (apply sub t1) :=> (apply sub t2)
  apply sub (TVar id)   = lookupTVar id sub
  apply sub (TList t)   = TList (apply sub t)

-- | Apply substitution to poly-type
instance Substitutable Poly where    
  apply sub (Mono t)      = Mono (apply sub t)
  apply sub (Forall id t) = Forall id (apply sub' t)
    where
      sub' = removeTVar id sub

-- | Apply substitution to (all poly-types in) another substitution
instance Substitutable Subst where  
  apply sub subst = zip keys $ map (apply sub) vals
    where
      (keys, vals) = unzip subst
  -- below is another (more runtime efficient) way to write this
  -- apply sub subst = map (\(x, y) -> (x, apply sub y)) subst
      
-- | Apply substitution to a type environment
instance Substitutable TypeEnv where  
  apply sub gamma = zip keys $ map (apply sub) vals
    where
      (keys, vals) = unzip gamma
      
-- | Extend substitution with a new type assignment
extendSubst :: Subst -> TVar -> Type -> Subst
extendSubst sub a t = (a, t) : apply [(a, t)] sub

-- another way to do it using map (or just rewrite "apply sub subst" using map)
-- extendSubst :: Subst -> TVar -> Type -> Subst
-- extendSubst sub a t = (a, t) : sub'
--   where
--     sub' = map (\(x, y) -> (x, apply [(a, t)] y)) sub

-- alternate method (without using higher order functions):
-- extendSubst :: Subst -> TVar -> Type -> Subst
-- extendSubst sub a t = (a, t) : helper sub
--   where
--     helper [] = []
--     helper ((id, t') : sub') = (id, apply [(a, t)] t') : helper sub'

-- note: I also saw working implementations using foldl'
      
--------------------------------------------------------------------------------
-- Problem 2: Unification
--------------------------------------------------------------------------------
      
-- | State of the type inference algorithm      
data InferState = InferState { 
    stSub :: Subst -- ^ current substitution
  , stCnt :: Int   -- ^ number of fresh type variables generated so far
} deriving Show

-- | Initial state: empty substitution; 0 type variables
initInferState = InferState [] 0

-- | Fresh type variable number n
freshTV n = TVar $ "a" ++ show n      
    
-- | Extend the current substitution of a state with a new type assignment   
extendState :: InferState -> TVar -> Type -> InferState
extendState (InferState sub n) a t = InferState (extendSubst sub a t) n
        
-- | Unify a type variable with a type; 
--   if successful return an updated state, otherwise throw an error
unifyTVar :: InferState -> TVar -> Type -> InferState
unifyTVar st a t
  | t == TVar a           = st
  | a `elem` freeTVars t  = throw (Error ("type error: cannot unify " ++ a ++ " and " ++ show t ++ " (occurs check)")) 
  | otherwise             = extendState st a t
-- Note: do NOT call unifyTVar directly (doesn't handle edge case)
-- ex: unifyTVar (InferState [("a", TInt)] 0) "a" (TVar "b") 
-- "correct" output: [("b", TInt), ("a", TInt)]
-- "incorrect" output: [("a", b), ("a", TInt)]
-- The way I wrote it, unify takes care of these cases, so unifyTVar should only be called as a result of calling unify
    
-- | Unify two types;
--   if successful return an updated state, otherwise throw an error
unify :: InferState -> Type -> Type -> InferState
unify st t1 t2 = helper st t1' t2'
  where
    t1' = apply (stSub st) t1  -- guarantee that t1 does not appear in the domain of stSub st
    t2' = apply (stSub st) t2  -- guarantee that t2 does not appear in the domain of stSub st
    helper st (TVar a)    t2          = unifyTVar st a t2
    helper st t1          (TVar a)    = unifyTVar st a t1
    helper st TInt        TInt        = st
    helper st TBool       TBool       = st
    helper st (t1 :=> t2) (t3 :=> t4) = unify (unify st t1 t3) t2 t4
    helper st (TList t1)  (TList t2)  = unify st t1 t2
    helper _  t1          t2          = throw (Error ("type error: cannot unify " ++ show t1 ++ " and " ++ show t2))

-- Note: here is an alternate way to do unifyTVar and unify:
-- (The guaranteed property is handled in unifyTVar instead of unify)
-- unifyTVar :: InferState -> TVar -> Type -> InferState
-- unifyTVar st a t
--   | t == TVar a           = st
--   | a `elem` freeTVars t  = throw (Error ("type error: cannot unify " ++ a ++ " and " ++ show t ++ " (occurs check)")) 
--   | TVar a  /= lookupTVar a (stSub st) = unify st (lookupTVar a (stSub st)) t
--   | otherwise             = extendState st a (apply (stSub st) t)

-- unify :: InferState -> Type -> Type -> InferState
-- unify st (TVar a)    t2          = unifyTVar st a t2
-- unify st t1          (TVar a)    = unifyTVar st a t1
-- unify st TInt        TInt        = st
-- unify st TBool       TBool       = st
-- unify st (t1 :=> t2) (t3 :=> t4) = unify (unify st t1 t3) t2 t4
-- unify st (TList t1)  (TList t2)  = unify st t1 t2
-- unify _  t1          t2          = throw (Error ("type error: cannot unify " ++ show t1 ++ " and " ++ show t2))

-- Note: another alternate way is to handle this in infer (and make sure you apply the substitution environment to both types before you unify)

--------------------------------------------------------------------------------
-- Problem 3: Type Inference
--------------------------------------------------------------------------------    
  
infer :: InferState -> TypeEnv -> Expr -> (InferState, Type)
infer st _     (EInt _)        = (st, TInt)
infer st _     (EBool _)       = (st, TBool)
infer st gamma (EVar x)        = (st', t)
  where
    (n, t) = instantiate (stCnt st) (lookupVarType x gamma)
    st'    = InferState (stSub st) n
infer st gamma (ELam x body)   = (st2, tX' :=> tBody)
  where
    tX           = freshTV (stCnt st)                      -- 1. Create a new fresh TV for the input parameter
    gamma'       = extendTypeEnv x (Mono tX) gamma         -- 2. Add it to the environment for recursive calls of infer
    st1          = InferState (stSub st) (stCnt st + 1)    -- 3. Increment count
    (st2, tBody) = infer st1 gamma' body                   -- 4. Infer the type of the body
    tX'          = apply (stSub st2) tX                    -- 5. Maybe the body restricts the type of the input parameter
infer st gamma (EApp e1 e2)    = (st4, t)
  where
    (st1, tFunc) = infer st gamma e1                       -- 1. Infer the type of e1 (note: should be a function type)
    (st2, tArg)  = infer st1 gamma e2                      -- 2. Infer the type of the argument     
    tBody        = freshTV (stCnt st2)                     -- 3. Create a fresh variable to represent the type of the body in the function
    st3          = InferState (stSub st2) (stCnt st2 + 1)  -- 4. Increment count
    st4          = unify st3 tFunc (tArg :=> tBody)        -- 5. Make sure that e1 is a function type with input type that matches e2's type
    t            = apply (stSub st4) tBody                 -- 6. Maybe the input type restricts the type of the function body
infer st gamma (ELet x e1 e2)  = infer st3 gamma3 e2
  where
    tX           = freshTV (stCnt st)                      -- 1. Create a new fresh TV for x (so that we can access x in e2; recursion)
    gamma1       = extendTypeEnv x (Mono tX) gamma         -- 2. Add it to the environment
    st1          = InferState (stSub st) (stCnt st + 1)    -- 3. Increment count
    (st2, t1)    = infer st1 gamma1 e1                     -- 4. Infer the type of e1
    st3          = unify st2 tX t1                         -- 5. Make sure recursive calls of x match the inferred type of e1
    gamma2       = apply (stSub st2) gamma1                -- 6. Apply the substitution to the type environment (context)
    s1           = generalize gamma1 t1                    -- 7. Generalize the type of e1 (in case it is used differently in multiple places)
    gamma3       = extendTypeEnv x s1 gamma2               -- 8. Add this generalization to the type environment
                                                           -- Note: steps 1, 2, 3, and 5 were added to support recursion
infer st gamma (EBin op e1 e2) = infer st gamma asApp
  where
    asApp = EApp (EApp opVar e1) e2
    opVar = EVar (show op)
infer st gamma (EIf c e1 e2) = infer st gamma asApp
  where
    asApp = EApp (EApp (EApp ifVar c) e1) e2
    ifVar = EVar "if"    
infer st gamma ENil = infer st gamma (EVar "[]")

-- Side note in case people have the same problem as my first attempt in implementing EApp:
-- If you attempt to do it like below it is wrong because of recursive function calls in let statements (e1 could have a fresh type that is not t1 :=> t2 yet)
-- (only 3 tests should fail)
-- infer st gamma (EApp e1 e2)    = case (infer st gamma e1) of
--   (st1, t1 :=> t2) -> (st3, t)
--     where
--       (st2, tArg)  = infer st1 gamma e2 
--       st3          = unify st2 t1 tArg
--       t            = apply (stSub st3) t2 
--   _ -> throw (Error ("type error: " ++ show e1 ++ " does not have a function type"))

-- You will discover that you need to handle a case for e1 to have a fresh type, in which case you might write the below implementation:
-- But then you will discover that the second case covers all cases, so you can delete the first and third cases, and you will get the uncommented implementation above
-- infer st gamma (EApp e1 e2)    = case (infer st gamma e1) of
--   (st1, t1 :=> t2) -> (st3, t)
--     where
--       (st2, tArg)  = infer st1 gamma e2 
--       st3          = unify st2 t1 tArg
--       t            = apply (stSub st3) t2 
--   (st1, tFunc) -> (st4, t)
--     where 
--       (st2, tArg)  = infer st1 gamma e2    
--       tBody        = freshTV (stCnt st2)
--       st3          = InferState (stSub st2) (stCnt st2 + 1)
--       st4          = unify st3 tFunc (tArg :=> tBody)
--       t            = apply (stSub st4) tBody 
--   _ -> throw (Error ("type error: " ++ show e1 ++ " does not have a function type"))

-- | Generalize type variables inside a type
generalize :: TypeEnv -> Type -> Poly
generalize gamma t = helper (freeTVars t L.\\ freeTVars gamma)
  where
    helper []     = Mono t
    helper (x:xs) = Forall x (helper xs)
    
-- | Instantiate a polymorphic type into a mono-type with fresh type variables
instantiate :: Int -> Poly -> (Int, Type)
instantiate n s = helper [] n s
  where
    helper sub n (Mono t) = (n, apply sub t)
    helper sub n (Forall id t) = helper (extendSubst sub id (freshTV n)) (n+1) t
      
-- | Types of built-in operators and functions      
preludeTypes :: TypeEnv
preludeTypes =
  [ ("+",    Mono $ TInt :=> TInt :=> TInt)
  , ("-",    Mono $ TInt :=> TInt :=> TInt)
  , ("*",    Mono $ TInt :=> TInt :=> TInt)
  , ("/",    Mono $ TInt :=> TInt :=> TInt)
  , ("==",   Forall "a" $ Mono $ TVar "a" :=> TVar "a" :=> TBool)
  , ("!=",   Forall "a" $ Mono $ TVar "a" :=> TVar "a" :=> TBool)
  , ("<",    Mono $ TInt :=> TInt :=> TBool)
  , ("<=",   Mono $ TInt :=> TInt :=> TBool)
  , ("&&",   Mono $ TBool :=> TBool :=> TBool)
  , ("||",   Mono $ TBool :=> TBool :=> TBool)
  , ("if",   Forall "a" $ Mono $ TBool :=> TVar "a" :=> TVar "a" :=> TVar "a")
  -- lists: 
  , ("[]",   Forall "a" $ Mono $ TList (TVar "a"))
  , (":",    Forall "a" $ Mono $ TVar "a" :=> TList (TVar "a") :=> TList (TVar "a"))
  , ("head", Forall "a" $ Mono $ TList (TVar "a") :=> TVar "a")
  , ("tail", Forall "a" $ Mono $ TList (TVar "a") :=> TList (TVar "a"))
  ]

-- same thing, but replaced $ with corresponding parentheses
-- preludeTypes :: TypeEnv
-- preludeTypes =
--   [ ("+",    Mono (TInt :=> TInt :=> TInt))
--   , ("-",    Mono (TInt :=> TInt :=> TInt))
--   , ("*",    Mono (TInt :=> TInt :=> TInt))
--   , ("/",    Mono (TInt :=> TInt :=> TInt))
--   , ("==",   Forall "a" (Mono (TVar "a" :=> TVar "a" :=> TBool)))
--   , ("!=",   Forall "a" (Mono (TVar "a" :=> TVar "a" :=> TBool)))
--   , ("<",    Mono (TInt :=> TInt :=> TBool))
--   , ("<=",   Mono (TInt :=> TInt :=> TBool))
--   , ("&&",   Mono (TBool :=> TBool :=> TBool))
--   , ("||",   Mono (TBool :=> TBool :=> TBool))
--   , ("if",   Forall "a" (Mono (TBool :=> TVar "a" :=> TVar "a" :=> TVar "a")))
--   -- lists: 
--   , ("[]",   Forall "a" (Mono (TList (TVar "a"))))
--   , (":",    Forall "a" (Mono (TVar "a" :=> TList (TVar "a") :=> TList (TVar "a"))))
--   , ("head", Forall "a" (Mono ((TList (TVar "a")) :=> TVar "a")))
--   , ("tail", Forall "a" (Mono ((TList (TVar "a")) :=> (TList (TVar "a")))))
--   ]
