module Evaluate where

import Term

-- Evaluation

type Env = [Value]

eval :: TermI -> Value
eval e = evalI e []

evalI :: TermI -> Env -> Value
evalI (Ann e _) d = evalC e d
evalI (Free x)  _ = vfree x
evalI (Bound i) d = d !! i
evalI (e :@: e') d = vapp (evalI e d) (evalC e' d)

vapp :: Value -> Value -> Value
vapp (VLam f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)


evalC :: TermC -> Env -> Value
evalC (Inf i) d = evalI i d
evalC (Lam e) d = VLam (\v -> evalC e (v:d))
