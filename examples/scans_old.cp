--> 3

max (x : Int) (y : Int) = if x > y then x else y;

-----------------------------------------
-- Object algebra interface of circuits
-----------------------------------------

type Circuit<C> = {
  identity : Int -> C,
  fan : Int -> C,
  beside : C -> C -> C,
  above : C -> C -> C,
  stretch : (List Int) -> C -> C
};

type NCircuit<C> = Circuit<C> & {
  rstretch : (List Int) -> C -> C
};


----------------------------
-- Width of circuit
----------------------------

type Width = { width : Int };
width = {
  (identity n).width = n;
  (fan      n).width = n;
  (beside c1 c2).width = c1.width + c2.width;
  (above  c1 c2).width = c1.width;
  (stretch ws c).width = sum ws;
} : Circuit <Width>;

width2 : NCircuit <Width> = width ,, {
  (rstretch ws c).width = c.width
};

----------------------------
-- Depth of circuit
----------------------------

type Depth = { depth : Int };
depth = {
  (identity n).depth = 0;
  (fan      n).depth = 1;
  (beside c1 c2).depth = max c1.depth c2.depth;
  (above  c1 c2).depth = c1.depth + c2.depth;
  (stretch ws c).depth = c.depth
} : Circuit <Depth>;

circuit C = trait [self: Circuit<C> ] => {
   circuit = 
      above ( beside ( fan 2) ( fan 2))
       ( above ( stretch ( list @Int 2 (\_->2)) ( fan 2))
         ( beside ( beside ( identity 1) ( fan 2)) ( identity 1)));
};

e1 = open width in
   above ( beside ( fan 2) ( fan 2))
    ( above ( stretch ( list @Int 2 (\_->2)) ( fan 2))
      ( beside ( beside ( identity 1) ( fan 2)) ( identity 1)));


brentKung = {
  accept C (l: Circuit<C>) = open l in
     above ( beside ( fan 2) ( fan 2))
      ( above ( stretch ( list @Int 2 (\_->2)) ( fan 2))
        ( beside ( beside ( identity 1) ( fan 2)) ( identity 1)))
};

e1 = brentKung.accept @Width width;
e2 = brentKung.accept @Depth depth;
e3 = brentKung.accept @(Width & Depth) (width ,, depth);

----------------------------------------------------------------
-- Well-formed circuit: illustrating dependent interpretations
----------------------------------------------------------------

type WellSized = { wS : Bool };
wellSized = {
  (above c1 c2).wS = c1.wS && c2.wS && c1.width == c2.width;
  (beside c1 c2).wS = c1.wS && c2.wS;
  (stretch ws c).wS = c.wS && length ws == c.width;
  (identity n).wS = true;
  (fan      n).wS = true;
  -- _.wS = true;
} : Circuit <Width%WellSized>;

-----------------------------------------------------------
-- Layout: illustrating context-sensitive interpretations
-----------------------------------------------------------

type Point = { x : Int, y : Int };
type Layout = { layout : (Int -> Int) -> List (List Point) };

layout = {
  (identity n).layout (f:Int->Int) = list @(List Point) 0 undefined;
  (fan n).layout (f:Int->Int) = list @(List Point) 1
    (\_ -> list @Point n (\i -> { x = 0, y = i+1 }));
  (above c1 c2).layout (f:Int->Int) = c1.layout f ++ c2.layout f;
  (beside c1 c2).layout (f:Int->Int) = lzw @(List Point)
    (\x -> \y -> x ++ y)
    (c1.layout f)
    (c2.layout (\(x:Int) -> f (c1.width + x)));
  (stretch ns c).layout (f:Int->Int) = let vs = scanl ns in
    c.layout (\(x:Int) -> f (vs!!x - 1));
} : Circuit <Width % Layout>;

length ((new (circuit @(WellSized & Width & Layout) ,, trait => (width ,, wellSized ,, layout))).circuit.layout (\(x: Int) -> x))
