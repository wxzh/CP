--> 2.0

-- shadowing
(l (y: Int) (z: String)).g = "1";
(l (x: Int) (y: String)).f = 1 + x;
(l 1 "1").f
