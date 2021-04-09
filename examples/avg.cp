--> 7

type Rcd = {x : Int, y : Int};

avg (R * Rcd) (r : R & Rcd) = r.x + r.y;

avg @Int (4,,{x = 3, y = 4})
