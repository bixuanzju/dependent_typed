module Term where

data TermI = Ann TermC Type
           | Bound Int
           | Free Name
           | TermI :@: TermC
           deriving (Show, Eq)

data TermC = Inf TermI
           | Lam TermC
           deriving (Show, Eq)

data Name = Global String
          | Local Int
          | Quote Int
          deriving (Show, Eq)

data Type = TFree Name
          | Fun Type Type
          deriving (Show, Eq)

data Value = VLam (Value -> Value)
           | VNeutral Neutral

data Neutral = NFree Name
             | NApp Neutral Value

instance Show Value where
  show = show . quote0

quote0 :: Value -> TermC
quote0 = quote 0

quote :: Int -> Value -> TermC
quote i (VLam f) = Lam (quote (i + 1) (f (vfree (Quote i))))
quote i (VNeutral n) = Inf (neutralQuote i n)

neutralQuote :: Int -> Neutral -> TermI
neutralQuote i (NFree x) = boundFree i x
neutralQuote i (NApp n v) = neutralQuote i n :@: quote i v


boundFree :: Int -> Name -> TermI
boundFree i (Quote x) = Bound (i - x - 1)
boundFree _ x = Free x

vfree :: Name -> Value
vfree  = VNeutral . NFree

data Kind = Star deriving (Show)

data Info = HasKind Kind
          | HasType Type
          deriving (Show)

type Context = [(Name, Info)]

type Result a = Either String a
