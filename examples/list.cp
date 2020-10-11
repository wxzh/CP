--> 40.0

let l1 = list @Double 5 (\x -> x) in
let l2 = scanl l1 in
let l3 = l1 ++ l2 in
let l4 = lzw @Double (\x -> \y -> x - y) l2 l3 in
sum l4 + length l4 + (l4!!0)
