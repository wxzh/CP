type Circuit C = {
  identity : Int -> C,
  fan      : Int -> C,
  above    : C -> C -> C,
  beside   : C -> C -> C,
  stretch  : (List Int) -> C -> C
};

type Width = { width : Int };
width = {
  identity (n:Int) = { width = n },
  fan      (n:Int) = { width = n },
  above  (c1:Width) (c2:Width) = { width = c1.width },
  beside (c1:Width) (c2:Width) = { width = c1.width + c2.width },
  stretch (ns:List Int) (c:Width) = { width = sum ns }
};

type Depth = { depth : Int };
depth = {
  identity (n:Int) = { depth = 0 },
  fan      (n:Int) = { depth = 1 },
  above  (c1:Depth) (c2:Depth) = { depth = c1.depth + c2.depth },
  beside (c1:Depth) (c2:Depth) =
    { depth = if c1.depth > c2.depth then c1.depth else c2.depth },
  stretch (ns:List Int) (c:Depth) = { depth = c.depth }
};

type WellSized = { wS : Bool };
-- BEGIN_SEDEL_WS
wellSized = {
  identity (n : Int) = { wS = true },
  fan      (n : Int) = { wS = true },
  above (c1 : WellSized&Width) (c2 : WellSized&Width) =
    { wS = c1.wS && c2.wS && c1.width == c2.width },
  beside (c1 : WellSized) (c2 : WellSized) = { wS  = c1.wS && c2.wS },
  stretch (ns : List Int) (c : WellSized&Width) =
    { wS = c.wS && length ns == c.width }
};
-- END_SEDEL_WS

type Point = { x : Int, y : Int };
type Layout = { layout : (Int -> Int) -> List (List Point) };
layout = {
  identity (n:Int) = { layout (f:Int->Int) = list @(List Point) 0 undefined },
  fan      (n:Int) = { layout (f:Int->Int) =
    list @(List Point) 1 (\_ -> list @Point n (\i -> { x = 0, y = i+1 })) },
  above  (c1:Layout) (c2:Layout) = { layout (f:Int->Int) =
    c1.layout f ++ c2.layout f },
  beside (c1:Layout&Width) (c2:Layout) = { layout (f:Int->Int) =
    lzw @(List Point) (\x -> \y -> x ++ y)
    (c1.layout f) (c2.layout (\(x:Int) -> f (c1.width + x))) },
  stretch (ns:List Int) (c:Layout) = { layout (f:Int->Int) =
    let vs = scanl ns in c.layout (\(x:Int) -> f (vs!!x - 1)) }
};

brentKung C (f : Circuit C) =
  f.above (f.beside (f.fan 2) (f.fan 2))
    (f.above (f.stretch (list @Int 2 (\_->2)) (f.fan 2))
      (f.beside (f.beside (f.identity 1) (f.fan 2)) (f.identity 1)));

type NCircuit C = Circuit C & {
  rstretch : (List Int) -> C -> C
};

nWidth = width ,, {
  rstretch (ns:List Int) (c:Width) = { width = sum ns }
};
nDepth = depth ,, {
  rstretch (ns:List Int) (c:Depth) = { depth = c.depth }
};
nWellSized = wellSized ,, {
  rstretch (ns:List Int) (c:WellSized&Width) = { wS = c.wS && length ns == c.width }
};
nLayout = layout ,, {
  rstretch (ns:List Int) (c:Layout) = { layout (f:Int->Int) =
    let vs = scanl ns in c.layout (\(x:Int) -> f (vs!!x + ns!!(length ns - 1) - 1)) }
};

circuit C (f : NCircuit C) = f.rstretch (list @Int 4 (\_->2)) (brentKung @C f);

scans = circuit @(Width & Depth & WellSized & Layout)
                (nWidth ,, nDepth ,, nWellSized ,, nLayout);
scans.layout (\(x:Int) -> x)
