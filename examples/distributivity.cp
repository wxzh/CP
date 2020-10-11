--> 2.0

rcd1 = { l = /\ (X * Int) . (\x -> 2) : X -> Int };

rcd2 = { l = /\ (X * Bool) . (\x -> true) : X -> Bool };

(((rcd1 ,, rcd2) : { l : forall (X * Int & Bool) . X -> Int & Bool }).l @String "hello") : Int
