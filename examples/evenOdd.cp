--> true


{-

An example where we show two mutually dependent traits

-}


type EvenOdd = {
  isEven : Double -> Bool,
  isOdd  : Double -> Bool };
even = trait [self : EvenOdd] => {
  isEven(n : Double)  = if n == 0 then true else self.isOdd(n - 1) };
odd = trait [self : EvenOdd] => {
  isOdd(n : Double)   = if n == 0 then false else self.isEven(n - 1) };
(new even ,, odd).isEven(42) -- Output: true
