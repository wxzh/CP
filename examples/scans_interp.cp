--> "Width = 4; Depth = 3; WellSized = true; length = 3"

max (x: Int) (y: Int) = if x > y then x else y;

----------------------------
-- Width of circuit
----------------------------

-- BEGIN_INTERPRETER_PATTERN
type Width = { width: Int };
identity1 (n: Int)                  = trait implements Width => { width = n; };
fan1      (n: Int)                  = trait implements Width => { width = n; };
above1    (c1: Width) (c2: Width)   = trait implements Width => { width = c1.width; };
beside1   (c1: Width) (c2: Width)   = trait implements Width => { width = c1.width + c2.width; };
stretch1  (ns: List Int) (c: Width) = trait implements Width => { width = sum ns; };
-- END_INTERPRETER_PATTERN

----------------------------
-- Depth of circuit
----------------------------

type Depth = { depth: Int };

identity2 (n: Int) = trait implements Depth => {
  depth = 0;
};
fan2 (n: Int) = trait implements Depth => {
  depth = 1;
};
above2 (c1: Depth) (c2: Depth) = trait implements Depth => {
  depth = c1.depth + c2.depth;
};
beside2 (c1: Depth) (c2: Depth) = trait implements Depth => {
  depth = max c1.depth c2.depth;
};
stretch2 (ns: List Int) (c: Depth) = trait implements Depth => {
  depth = c.depth;
};

----------------------------------------------------------------
-- Well-formed circuit: illustrating dependent interpretations
----------------------------------------------------------------

type WellSized = { wellSized: Bool };

identity3 (n: Int) = trait implements WellSized => {
  wellSized = true;
};
fan3 (n: Int) = trait implements WellSized => {
  wellSized = true;
};
above3 (c1: Width & WellSized) (c2: Width & WellSized) = trait implements WellSized => {
  wellSized = c1.wellSized && c2.wellSized && c1.width == c2.width;
};
beside3 (c1: WellSized) (c2: WellSized) = trait implements WellSized => {
  wellSized = c1.wellSized && c2.wellSized;
};
stretch3 (ns: List Int) (c: Width & WellSized) = trait implements WellSized => {
  wellSized = c.wellSized && length ns == c.width;
};

-----------------------------------------------------------
-- Layout: illustrating context-sensitive interpretations
-----------------------------------------------------------

type Point = { x: Int, y: Int };
type Layout = { layout: (Int -> Int) -> List (List Point) };

identity4 (n: Int) = trait implements Layout => {
  layout (f: Int -> Int) = list @(List Point) 0 undefined;
};
fan4 (n: Int) = trait implements Layout => {
  layout (f: Int -> Int) = list @(List Point) 1
    (\_ -> list @Point n (\i -> { x = 0, y = i+1 }));
};
above4 (c1: Layout) (c2: Layout) = trait implements Layout => {
  layout (f: Int -> Int) = c1.layout f ++ c2.layout f;
};
beside4 (c1: Width & Layout) (c2: Layout) = trait implements Layout => {
  layout (f: Int -> Int) = lzw @(List Point)
    (\x -> \y -> x ++ y)
    (c1.layout f)
    (c2.layout (\(x:Int) -> f (c1.width + x)));
};
stretch4 (ns: List Int) (c: Layout) = trait implements Layout => {
  layout (f: Int -> Int) = let vs = scanl ns in
    c.layout (\(x:Int) -> f (vs!!x - 1));
};

----------------------------
-- Factories and usage
----------------------------

type Circuit = Width & Depth & WellSized & Layout;

identity (n: Int) = identity1 n ,, identity2 n ,, identity3 n ,, identity4 n;
fan (n: Int) = fan1 n ,, fan2 n ,, fan3 n ,, fan4 n;
above (c1: Circuit) (c2: Circuit) = above1 c1 c2 ,, above2 c1 c2 ,, above3 c1 c2 ,, above4 c1 c2;
beside (c1: Circuit) (c2: Circuit) = beside1 c1 c2 ,, beside2 c1 c2 ,, beside3 c1 c2 ,, beside4 c1 c2;
stretch (ns: List Int) (c: Circuit) = stretch1 ns c ,, stretch2 ns c ,, stretch3 ns c ,, stretch4 ns c;

brentKung = new above (new beside (new fan 2) (new fan 2))
  (new above (new stretch (list @Int 2 (\_->2)) (new fan 2))
    (new beside (new beside (new identity 1) (new fan 2)) (new identity 1)));
"Width = " ++ brentKung.width.toString ++ "; " ++
"Depth = " ++ brentKung.depth.toString ++ "; " ++
"WellSized = " ++ brentKung.wellSized.toString ++ "; " ++
"length = " ++ (length (brentKung.layout (\(x:Int) -> x))).toString
