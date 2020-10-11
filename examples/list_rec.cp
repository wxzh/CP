--> 9.0

type P = { x: Int, y: Int };
f = \(i:Int) -> {x = i, y = i};
l = list @P 10 (\i -> { x = i, y = i });
(l !! 9).x
