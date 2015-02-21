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
evalI Star _ = VStar
evalI (Pi t t') d = VPi (evalC t d) (\x -> evalC t' (x:d))
evalI Nat _ = VNat
evalI Zero _ = VZero
evalI (Succ k) d = VSucc (evalC k d)
evalI (NatElim m mz ms k) d = recur (evalC k d)
  where recur kVal =
          case kVal of
            VZero -> mzVal
            VSucc l -> msVal `vapp` l `vapp` recur l
            VNeutral k' ->
              VNeutral (NNatElim (evalC m d) mzVal msVal k')
            _ -> error "internal: eval natElim"
        mzVal = evalC mz d
        msVal = evalC ms d


vapp :: Value -> Value -> Value
vapp (VLam f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)
vapp _ _ = undefined

evalC :: TermC -> Env -> Value
evalC (Inf i) d = evalI i d
evalC (Lam e) d = VLam (\v -> evalC e (v:d))
