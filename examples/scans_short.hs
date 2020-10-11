class Circuit c where
  identity :: Int -> c
  fan      :: Int -> c
  above    :: c -> c -> c
  beside   :: c -> c -> c
  stretch  :: [Int] -> c -> c

data Width = W { width :: Int } deriving Show
instance Circuit Width where
  identity n   = W n
  fan n        = W n
  above c1 c2  = c1
  beside c1 c2 = W (width c1 + width c2)
  stretch ws c = W (sum ws)

data Depth = D { depth :: Int } deriving Show
instance Circuit Depth where
  identity n   = D 0
  fan n        = D 1
  above c1 c2  = D (depth c1 + depth c2)
  beside c1 c2 = D ((depth c1) `max` (depth c2))
  stretch ws c = c

data WellSized = WS { wS :: Bool, w' :: Width } deriving Show
instance Circuit WellSized where
 identity n   = WS True (identity n)
 fan n        = WS True (fan n)
 above c1 c2  = WS (wS c1 && wS c2 && width (w' c1) == width (w' c2))
                   (above (w' c1) (w' c2))
 beside c1 c2 = WS (wS c1 && wS c2) (beside (w' c1) (w' c2))
 stretch ws c = WS (wS c && length ws == width (w' c))
                   (stretch ws (w' c))

data Layout = L { layout :: (Int -> Int) -> [[(Int,Int)]], w'' :: Width }
instance Circuit Layout where
 identity n   = L (const []) (identity n)
 fan n        = L (\f -> [[(f 0, f i) | i <- [1..n-1]]]) (fan n)
 above c1 c2  = L (\f -> layout c1 f ++ layout c2 f)
                  (above (w'' c1) (w'' c2))
 beside c1 c2 = L (\f -> lzw (++) (layout c1 f) (layout c2 (f . (width (w'' c1) +))))
                  (beside (w'' c1) (w'' c2))
 stretch ns c = L (\f -> layout c (f . pred . (scanl1 (+) ns !!)))
                  (stretch ns (w'' c))

lzw :: (a -> a -> a) -> [a] -> [a] -> [a]
lzw _ [] ys = ys
lzw _ xs [] = xs
lzw f (x:xs) (y:ys) = f x y : lzw f xs ys

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
instance NCircuit WellSized where
  rstretch = stretch
instance NCircuit Layout where
  rstretch ns c = L (\f -> layout c (f . pred . (scanl (+) (last ns) ns !!)))
                    (stretch ns (w'' c))

circuit :: NCircuit c => c
circuit = rstretch [2, 2, 2, 2] brentKung

main :: IO ()
main = print $ layout (circuit :: Layout) (\x -> x)
