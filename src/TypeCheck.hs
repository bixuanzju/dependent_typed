module TypeCheck where

import Term
import Evaluate
import Control.Monad (unless)

-- kindC :: Context -> Type -> Kind -> Result ()
-- kindC cx (TFree x) Star =
--   case lookup x cx of
--     Just (HasKind Star) -> return ()
--     Nothing -> Left "unknown identifier"
-- kindC cx (Fun k k') Star =
--   do kindC cx k Star
--      kindC cx k' Star


typeI0 :: Context -> TermI -> Result Type
typeI0 = typeI 0


typeI :: Int -> Context -> TermI -> Result Type
typeI i cx (Ann e t) =
  do typeC i cx t VStar
     let t' = evalC t []
     typeC i cx e t'
     return t'
typeI _ _ Star = return VStar
typeI _ cx (Free n) =
  case lookup n cx of
    Just t -> return t
    Nothing -> fail "unknown identifier"
typeI i cx (Pi p p') =
  do typeC i cx p VStar
     let t' = evalC p []
     typeC (i + 1) ((Local i, t'):cx) (substC 0 (Free (Local i)) p') VStar
     return VStar
typeI i cx (e :@: e') = do t <- typeI i cx e
                           case t of
                            VPi v f -> do typeC i cx e' v
                                          return (f (evalC e' []))
                            _ -> fail "illegal application"
typeI _ _ Nat = return VStar
typeI _ _ Zero = return VNat
typeI i cx (Succ k) = do typeC i cx k VNat
                         return VNat
typeI i cx (NatElim m mz ms k) =
  do typeC i cx m (VPi VNat (const VStar))
     let mVal = evalC m []
     typeC i cx mz (mVal `vapp` VZero)
     typeC i cx ms (VPi VNat (\l -> VPi (mVal `vapp` l) (const (mVal `vapp` VSucc l))))
     typeC i cx k VNat
     let kVal = evalC k []
     return (mVal `vapp` kVal)
typeI i cx (Vec a k) =
  do typeC i cx a VStar
     typeC i cx k VNat
     return VStar
typeI _ _ (Nil a) =
  do let aVal = evalC a []
     return (VVec aVal VZero)
typeI i cx (Cons a k x xs) =
  do typeC i cx a VStar
     let aVal = evalC a []
     typeC i cx k VNat
     let kVal = evalC k []
     typeC i cx x aVal
     typeC i cx xs (VVec aVal kVal)
     return (VVec aVal (VSucc kVal))
typeI i cx (VecElim a m mn mc k xs) =
  do typeC i cx a VStar
     let aVal = evalC a []
     typeC i
           cx
           m
           (VPi VNat
                (\l ->
                   VPi (VVec aVal l)
                       (const VStar)))
     let mVal = evalC m []
     typeC i
           cx
           mn
           (mVal `vapp` VZero `vapp`
            (VNil aVal))
     typeC i
           cx
           mc
           (VPi VNat
                (\l ->
                   VPi aVal
                       (\x ->
                          VPi (VVec aVal l)
                              (\ys ->
                                 VPi (mVal `vapp` l `vapp` ys)
                                     (const (mVal `vapp`
                                             (VSucc l) `vapp`
                                             (VCons aVal l x ys)))))))
     typeC i cx k VNat
     let kVal = evalC k []
     let xsVal = evalC xs []
     typeC i cx xs (VVec aVal kVal)
     return (mVal `vapp` kVal `vapp` xsVal)
typeI _ _ _ = fail "Impossible"

typeC :: Int -> Context -> TermC -> Type -> Result ()
typeC i cx (Inf e) t = do t' <- typeI i cx e
                          unless (quote0 t' == quote0 t) (fail "type mismatch")
typeC i cx (Lam e) (VPi t f) = typeC (i + 1) ((Local i, t):cx) (substC 0 (Free (Local i)) e) (f (vfree (Local i)))
typeC _ _ _ _ = fail "type mismatch"

substI :: Int -> TermI -> TermI -> TermI
substI i r (Ann e t) = Ann (substC i r e) t
substI i r e@(Bound j) =
  if i == j
     then r
     else e
substI _ _ e@(Free _) = e
substI i r (e1 :@: e2) =
  substI i r e1 :@:
  substC i r e2
substI _ _ Star = Star
substI i r (Pi t t') = Pi (substC i r t) (substC (i + 1) r t')
substI _ _ Nat = Nat
substI _ _ Zero = Zero
substI i r (Succ t) = Succ (substC i r t)
substI i r (NatElim m mz ms k) = NatElim (substC i r m) (substC i r mz) (substC i r ms) (substC i r k)
substI i r (Vec t1 t2) = Vec (substC i r t1) (substC i r t2)
substI i r (Nil t) = Nil (substC i r t)
substI i r (Cons t1 t2 t3 t4) = Cons (substC i r t1) (substC i r t2) (substC i r t3) (substC i r t4)
substI i r (VecElim t1 t2 t3 t4 t5 t6) = VecElim (substC i r t1) (substC i r t2) (substC i r t3) (substC i r t4) (substC i r t5) (substC i r t6)

substC :: Int -> TermI -> TermC -> TermC
substC i r (Inf e) = Inf (substI i r e)
substC i r (Lam e) = Lam (substC (i + 1) r e)

-- test
id' :: TermI
id' = Ann (Lam (Lam (Inf (Bound 0)))) (Inf (Pi (Inf Star) (Inf (Pi (Inf (Bound 0)) (Inf (Bound 1))))))

free :: String -> TermC
free = Inf . Free . Global

term1 :: TermI
term1 = id' :@: (free "Bool")

term2 :: TermI
term2 = term1 :@: (free "False")

env1 :: Context
env1 =
  [(Global "Bool",VStar),(Global "True",vfree (Global "Bool")), (Global "False",vfree (Global "Bool"))]


n2nat :: Int -> TermC
n2nat n = recur n
  where recur num =
          if num == 0
             then (Inf Zero)
             else Inf (Succ (recur (num - 1)))

plus :: Int -> Int -> TermI
plus n m =
  (NatElim (Lam (Inf (Pi (Inf Nat)
                         (Inf Nat))))
           (Lam (Inf (Bound 0)))
           (Lam (Lam (Lam (Inf (Succ (Inf ((Bound 1) :@:
                                           (Inf (Bound 0)))))))))
           (n2nat n)) :@:
  (n2nat m)

vec1 :: TermI
vec1 =
  Cons (free "Bool")
       (n2nat 1)
       (free "False")
       (Inf (Cons (free "Bool")
                  (n2nat 0)
                  (free "True")
                  (Inf (Nil (free "Bool")))))

vec2 :: TermI
vec2 =
  (Cons (free "Bool")
        (n2nat 0)
        (free "False")
        (Inf (Nil (free "Bool"))))

