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
evalI (Vec t1 t2) d = VVec (evalC t1 d) (evalC t2 d)
evalI (Nil t) d = VNil (evalC t d)
evalI (Cons a k x xs) d =
  VCons (evalC a d)
        (evalC k d)
        (evalC x d)
        (evalC xs d)
evalI (VecElim a m mn mc k xs) d =
  recur (evalC k d)
        (evalC xs d)
  where recur kVal xsVal =
          case xsVal of
            VNil _ -> mnVal
            VCons _ l y ys ->
              mcVal `vapp` l `vapp` y `vapp` ys `vapp`
              recur l ys
            VNeutral n ->
              VNeutral (NVecElim (evalC a d)
                                 (evalC m d)
                                 mnVal
                                 mcVal
                                 kVal
                                 n)
            _ -> error "internal: eval vecElim"
        mnVal = evalC mn d
        mcVal = evalC mc d



vapp :: Value -> Value -> Value
vapp (VLam f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)
vapp _ _ = undefined

evalC :: TermC -> Env -> Value
evalC (Inf i) d = evalI i d
evalC (Lam e) d = VLam (\v -> evalC e (v:d))
