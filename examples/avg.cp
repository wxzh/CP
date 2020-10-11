--> 7.0

type Rcd = {x : Double, y : Double};

avg (R * Rcd) (r : R & Rcd) = r.x + r.y;

avg @Double (4,,{x = 3, y = 4})
