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
  [(Global "Bool",VStar),(Global "False",vfree (Global "Bool"))]
