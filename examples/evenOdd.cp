--> true


{-

An example where we show two mutually dependent traits

-}


type EvenOdd = {
  isEven : Int -> Bool,
  isOdd  : Int -> Bool };
even = trait [self : EvenOdd] => {
  isEven(n : Int)  = if n == 0 then true else self.isOdd(n - 1) };
odd = trait [self : EvenOdd] => {
  isOdd(n : Int)   = if n == 0 then false else self.isEven(n - 1) };
(new even ,, odd).isEven(42) -- Output: true
