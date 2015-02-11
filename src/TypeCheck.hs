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

substC :: Int -> TermI -> TermC -> TermC
substC i r (Inf e) = Inf (substI i r e)
substC i r (Lam e) = Lam (substC (i + 1) r e)

-- test
-- id' = (Lam (Inf (Bound 0)))
-- const' = Lam (Lam (Inf (Bound 1)))

-- tfree = TFree . Global
-- free = Inf . Free . Global

-- term1 =
--   Ann id'
--       (Fun (tfree "a")
--            (tfree "a")) :@:
--   free "y"
-- term2 =
--   Ann const'
--       (Fun (Fun (tfree "b")
--                 (tfree "b"))
--            (Fun (tfree "a")
--                 (Fun (tfree "b")
--                      (tfree "b")))) :@:
--   id' :@:
--   free "y"

-- env1 =
--   [(Global "y",HasType (tfree "a")),(Global "a",HasKind Star)]

-- env2 = [(Global "b", HasKind Star)] ++ env1
