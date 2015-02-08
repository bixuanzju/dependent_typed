module TypeCheck where

import Term
import Evaluate
import Control.Monad (unless)

kindC :: Context -> Type -> Kind -> Result ()
kindC cx (TFree x) Star =
  case lookup x cx of
    Just (HasKind Star) -> return ()
    Nothing -> Left "unknown identifier"
kindC cx (Fun k k') Star =
  do kindC cx k Star
     kindC cx k' Star


typeI0 :: Context -> TermI -> Result Type
typeI0 = typeI 0


typeI :: Int -> Context -> TermI -> Result Type
typeI i cx (Ann e t) =
  do kindC cx t Star
     typeC i cx e t
     return t
typeI _ cx (Free n) =
  case lookup n cx of
    Just (HasType t) -> return t
    Nothing -> fail "unknown identifier"
typeI i cx (e1 :@: e2) =
  do t <- typeI i cx e1
     case t of
       Fun t1 t2 ->
         do typeC i cx e2 t1
            return t2
       _ -> fail "illegal application"

typeC :: Int -> Context -> TermC -> Type -> Result ()
typeC i cx (Inf e) t =
  do t' <- typeI i cx e
     unless (t' == t)
            (fail "type mismatch")
typeC i cx (Lam e) (Fun t1 t2) =
  typeC (i + 1)
        ((Local i,HasType t1) :
         cx)
        (substC 0 (Free (Local i)) e)
        t2
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

substC :: Int -> TermI -> TermC -> TermC
substC i r (Inf e) = Inf (substI i r e)
substC i r (Lam e) = Lam (substC (i + 1) r e)

-- test
id' = (Lam (Inf (Bound 0)))
const' = Lam (Lam (Inf (Bound 1)))

tfree = TFree . Global
free = Inf . Free . Global

term1 =
  Ann id'
      (Fun (tfree "a")
           (tfree "a")) :@:
  free "y"
term2 =
  Ann const'
      (Fun (Fun (tfree "b")
                (tfree "b"))
           (Fun (tfree "a")
                (Fun (tfree "b")
                     (tfree "b")))) :@:
  id' :@:
  free "y"

env1 =
  [(Global "y",HasType (tfree "a")),(Global "a",HasKind Star)]

env2 = [(Global "b", HasKind Star)] ++ env1
