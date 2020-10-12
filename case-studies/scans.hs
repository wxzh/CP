{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverlappingInstances, TypeOperators, TypeSynonymInstances #-}

class a :<: b where
  prj :: a -> b
instance a :<: a where
  prj x = x
instance (a, b) :<: a where
  prj = fst
instance (b :<: c) => (a, b) :<: c where
  prj = prj . snd

class Circuit c where
  identity :: Int -> c
  fan      :: Int -> c
  above    :: c -> c -> c
  beside   :: c -> c -> c
  stretch  :: [Int] -> c -> c

newtype Width = W { width :: Int } deriving Show
instance Circuit Width where
  identity n   = W n
  fan n        = W n
  above c1 c2  = c1
  beside c1 c2 = W (width c1 + width c2)
  stretch ns c = W (sum ns)

newtype Depth = D { depth :: Int } deriving Show
instance Circuit Depth where
  identity n   = D 0
  fan n        = D 1
  above c1 c2  = D (depth c1 + depth c2)
  beside c1 c2 = D ((depth c1) `max` (depth c2))
  stretch ns c = c

newtype WellSized = WS { wS :: Bool } deriving Show
instance (Circuit c, c :<: Width) => Circuit (WellSized, c) where
  identity n   = (WS True, identity n)
  fan n        = (WS True, fan n)
  above c1 c2  = (WS (gWS c1 && gWS c2 && gWidth c1 == gWidth c2),
                  above (prj c1) (prj c2))
  beside c1 c2 = (WS (gWS c1 && gWS c2), beside (prj c1) (prj c2))
  stretch ns c = (WS (gWS c && length ns == gWidth c), stretch ns (prj c))

newtype Layout = L { layout :: (Int -> Int) -> [[(Int, Int)]] }
instance (Circuit c, c :<: Width) => Circuit (Layout, c) where
  identity n   = (L (const []), identity n)
  fan n        = (L (\f -> [[(f 0, f i) | i <- [1..n-1]]]), fan n)
  above c1 c2  = (L (\f -> gLayout c1 f ++ gLayout c2 f),
                  above (prj c1) (prj c2))
  beside c1 c2 = (L (\f -> lzw (++) (gLayout c1 f)
                                    (gLayout c2 (f . (gWidth c1 +)))),
                  beside (prj c1) (prj c2))
  stretch ns c = (L (\f -> gLayout c (f . pred . (scanl1 (+) ns !!))),
                  stretch ns (prj c))

lzw :: (a -> a -> a) -> [a] -> [a] -> [a]
lzw _ [] ys = ys
lzw _ xs [] = xs
lzw f (x:xs) (y:ys) = f x y : lzw f xs ys


instance (Circuit i1, Circuit i2) => Circuit (i1,i2) where
  identity n   = (identity n, identity n)
  fan n        = (fan n, fan n)
  above c1 c2  = (above (prj c1) (prj c2), above (prj c1) (prj c2))
  beside c1 c2 = (beside (prj c1) (prj c2), beside (prj c1) (prj c2))
  stretch xs c = (stretch xs (prj c), stretch xs (prj c))

gWidth :: (c :<: Width) => c -> Int
gWidth = width . prj

gDepth :: (c :<: Depth) => c -> Int
gDepth = depth . prj

gWS :: (c :<: WellSized) => c -> Bool
gWS = wS . prj

gLayout :: (c :<: Layout) => c -> (Int -> Int) -> [[(Int, Int)]]
gLayout = layout . prj

brentKung :: Circuit c => c
brentKung = above (beside (fan 2) (fan 2))
              (above (stretch [2, 2] (fan 2))
                (beside (beside (identity 1) (fan 2)) (identity 1)))

class Circuit c => NCircuit c where
  rstretch :: [Int] -> c -> c

instance NCircuit Width where
  rstretch = stretch
instance NCircuit Depth where
  rstretch = stretch
instance (NCircuit c, c :<: Width) => NCircuit (WellSized, c) where
  rstretch = stretch
instance (NCircuit c, c :<: Width) => NCircuit (Layout, c) where
  rstretch ns c = (L (\f -> gLayout c (f . pred . (scanl (+) (last ns) ns !!))),
                  stretch ns (prj c))
instance (NCircuit i1, NCircuit i2) => NCircuit (i1,i2) where
  rstretch xs c = (rstretch xs (prj c), rstretch xs (prj c))

circuit :: NCircuit c => c
circuit = rstretch [2, 2, 2, 2] brentKung

main :: IO ()
main = print $ gLayout (circuit :: (Layout,(WellSized, (Depth, Width)))) (\x -> x)
