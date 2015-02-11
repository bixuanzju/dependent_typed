module Term where

data TermI = Ann TermC TermC
           | Star
           | Pi TermC TermC
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

data Neutral = NFree Name
             | NApp Neutral Value

instance Show Value where
  show = show . quote0

quote0 :: Value -> TermC
quote0 = quote 0

quote :: Int -> Value -> TermC
quote i (VLam f) = Lam (quote (i + 1) (f (vfree (Quote i))))
quote i (VNeutral n) = Inf (neutralQuote i n)
quote _ VStar = Inf Star
quote i (VPi v f) = Inf (Pi (quote i v) (quote (i + 1) (f (vfree (Quote i)))))

neutralQuote :: Int -> Neutral -> TermI
neutralQuote i (NFree x) = boundFree i x
neutralQuote i (NApp n v) = neutralQuote i n :@: quote i v


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
