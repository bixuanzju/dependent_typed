module Term where

data TermI = Ann TermC TermC
           | Star
           | Pi TermC TermC
           | Bound Int
           | Free Name
           | TermI :@: TermC
           | Nat
           | NatElim TermC TermC TermC TermC
           | Zero
           | Succ TermC
           | Vec TermC TermC
           | Nil TermC
           | Cons TermC TermC TermC TermC
           | VecElim TermC TermC TermC TermC TermC TermC
           deriving (Show, Eq)

data TermC = Inf TermI
           | Lam TermC
           deriving (Show, Eq)

data Name = Global String
          | Local Int
          | Quote Int
          deriving (Show, Eq)

-- data Type = TFree Name
--           | Fun Type Type
--           deriving (Show, Eq)

type Type = Value

data Value = VLam (Value -> Value)
           | VStar
           | VPi Value (Value -> Value) -- domain and range
                                        -- (represented as function to
                                        -- hint that range is
                                        -- dependent on variable)
           | VNeutral Neutral
           | VNat
           | VZero
           | VSucc Value
           | VNil Value
           | VCons Value Value Value Value
           | VVec Value Value

data Neutral
  = NFree Name
  | NApp Neutral
         Value
  | NNatElim Value
             Value
             Value
             Neutral
  | NVecElim Value
             Value
             Value
             Value
             Value
             Neutral

instance Show Value where
  show = show . quote0

quote0 :: Value -> TermC
quote0 = quote 0

quote :: Int -> Value -> TermC
quote i (VLam f) =
  Lam (quote (i + 1)
             (f (vfree (Quote i))))
quote i (VNeutral n) = Inf (neutralQuote i n)
quote _ VStar = Inf Star
quote i (VPi v f) =
  Inf (Pi (quote i v)
          (quote (i + 1)
                 (f (vfree (Quote i)))))
quote _ VNat = Inf Nat
quote _ VZero = Inf Zero
quote i (VSucc v) = Inf (Succ (quote i v))
quote i (VNil v) = Inf (Nil (quote i v))
quote i (VCons v1 v2 v3 v4) =
  Inf (Cons (quote i v1)
            (quote i v2)
            (quote i v3)
            (quote i v4))
quote i (VVec v1 v2) =
  Inf (Vec (quote i v1)
           (quote i v2))

neutralQuote :: Int -> Neutral -> TermI
neutralQuote i (NFree x) = boundFree i x
neutralQuote i (NApp n v) =
  neutralQuote i n :@:
  quote i v
neutralQuote i (NNatElim m mz ms k) =
  NatElim (quote i m)
          (quote i mz)
          (quote i ms)
          (Inf $
           neutralQuote i k)
neutralQuote i (NVecElim v1 v2 v3 v4 v5 n) =
  VecElim (quote i v1)
          (quote i v2)
          (quote i v3)
          (quote i v4)
          (quote i v5)
          (Inf $
           neutralQuote i n)


boundFree :: Int -> Name -> TermI
boundFree i (Quote x) = Bound (i - x - 1)
boundFree _ x = Free x

vfree :: Name -> Value
vfree  = VNeutral . NFree

-- data Kind = Star deriving (Show)

-- data Info = HasKind Kind
--           | HasType Type
--           deriving (Show)

type Context = [(Name, Type)]

type Result a = Either String a
