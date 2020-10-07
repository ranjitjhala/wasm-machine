-- https://gist.github.com/ranjitjhala/b8b49b133b5dca572db3334021c8e714

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--no-adt"     @-}

module Language.WM.Expr where 

import Language.Haskell.Liquid.ProofCombinators
----------------------------------------------------------------------------
-- | Source Expressions 
-----------------------------------------------------------------------------

{-@ type Id = Nat @-}
type IdT = Int 

type Val = Int

data Expr = Var Int IdT 
          | Con Int Val
          | Add Int Expr Expr
          | Let Int Expr Expr

{-@  data Expr 
       = Var { bnd :: Nat, eVar :: {v:Nat| v < bnd} }
       | Con { bnd :: Nat, eCon :: Int }
       | Add { bnd :: Nat, eOp1 :: Exp bnd, eOp2 :: Exp bnd }
       | Let { bnd :: Nat, eOp1 :: Exp bnd, eOp2 :: Exp {bnd + 1} } 
  @-}

{-@ measure free @-}
{-@ free :: Expr -> Nat @-}
free :: Expr -> Int 
free (Var b _)   = b
free (Con b _)   = b
free (Add b _ _) = b
free (Let b _ _) = b

{-@ type Exp N = {e:Expr | free e == N} @-}


-----------------------------------------------------------------------------
-- | Evaluating Source Expressions 
-----------------------------------------------------------------------------
type State = IdT -> Val

{-@ reflect get @-}
get :: State -> IdT -> Val
get s x = s x

{-@ reflect set @-}
set :: State -> IdT -> Val -> State 
set s x v y = if y == x then v else s y

-----------------------------------------------------------------------------
-- | Evaluating Source Expressions 
-----------------------------------------------------------------------------

{-@ reflect eval @-}
eval :: State -> Expr -> Int
eval s (Var _ x)     = get s x
eval s (Con _ n)     = n
eval s (Add _ e1 e2) = eval s e1 + eval s e2
eval s (Let x e1 e2) = eval (set s x (eval s e1)) e2


-----------------------------------------------------------------------------
-- | Proposition that two states are "equal" upto N
-----------------------------------------------------------------------------
{-@ type StateEq N S1 S2 = x:{Nat| x < N} -> { get S1 x = get S2 x} @-}
type StateEqT = Int -> ()

-----------------------------------------------------------------------------
-- | Lemma that n-equiv expressions eval to same value on n-equiv states
-----------------------------------------------------------------------------
{-@ lem_eval_N :: n:Nat -> s1:State -> s2:State -> StateEq n s1 s2 -> e:Exp n -> 
                  { eval s1 e == eval s2 e }
  @-}
lem_eval_N :: Int -> State -> State -> StateEqT -> Expr -> () 
lem_eval_N n s1 s2 eq (Con _ k)     = () 
lem_eval_N n s1 s2 eq (Var _ x)     = eq x
lem_eval_N n s1 s2 eq (Add _ e1 e2) = lem_eval_N n s1 s2 eq e1 &&& lem_eval_N n s1 s2 eq e2
lem_eval_N n s1 s2 eq (Let _ e1 e2) = lem_eval_N (n + 1) s1' s2' eq' e2
  where
      v   = eval s1 e1 
      s1' = set s1 n v 
      s2' = set s2 n v 
      eq' = lem_upd n s1 s2 eq (v ? lem_eval_N n s1 s2 eq e1)

{-@ lem_upd :: n:Nat -> s1:State -> s2:State -> StateEq n s1 s2 -> v:Val -> StateEq {n+1} {set s1 n v} {set s2 n v} @-}
lem_upd :: Int -> State -> State -> StateEqT -> Val -> StateEqT
lem_upd n s1 s2 eq v z = if z < n then eq z else ()
