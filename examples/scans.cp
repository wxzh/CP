--> <List>

max (x : Int) (y : Int) = if x > y then x else y;

-----------------------------------------
-- Object algebra interface of circuits
-----------------------------------------

-- BEGIN_CIRCUIT_SIG
type CircuitSig<Circuit> = {
  Identity : Int -> Circuit;
  Fan      : Int -> Circuit;
  Above    : Circuit -> Circuit -> Circuit;
  Beside   : Circuit -> Circuit -> Circuit;
  Stretch  : (List Int) -> Circuit -> Circuit;
};
-- END_CIRCUIT_SIG

----------------------------
-- Width of circuit
----------------------------

type Width = { width : Int };

width = trait implements CircuitSig<Width> => {
  (Identity   n).width = n;
  (Fan        n).width = n;
  (Above  c1 c2).width = c1.width;
  (Beside c1 c2).width = c1.width + c2.width;
  (Stretch ns c).width = sum ns;
};

----------------------------
-- Depth of circuit
----------------------------

type Depth = { depth : Int };

depth = trait implements CircuitSig<Depth> => {
  (Identity   n).depth = 0;
  (Fan        n).depth = 1;
  (Above  c1 c2).depth = c1.depth + c2.depth;
  (Beside c1 c2).depth = max c1.depth c2.depth;
  (Stretch ns c).depth = c.depth;
};



----------------------------------------------------------------
-- Well-formed circuit: illustrating dependent interpretations
----------------------------------------------------------------

-- BEGIN_CIRCUIT_WS
type WellSized = { wS : Bool };
wellSized = trait implements CircuitSig<Width%WellSized> => {
  (Identity   n).wS = true;
  (Fan        n).wS = true;
  (Above  c1 c2).wS = c1.wS && c2.wS && c1.width == c2.width;
  (Beside c1 c2).wS = c1.wS && c2.wS;
  (Stretch ns c).wS = c.wS && length ns == c.width;
};
-- END_CIRCUIT_WS

----------------------------------------------------------------
-- layout circuit: illustrating context-sensitive interpretations
----------------------------------------------------------------

-- BEGIN_CIRCUIT_LAYOUT
type Point = { x : Int, y : Int };
type Layout = { layout : (Int -> Int) -> List (List Point) };
layout = trait implements CircuitSig<Width%Layout> => {
  (Identity   n).layout (f:Int->Int) = list @(List Point) 0 undefined;
  (Fan        n).layout (f:Int->Int) = list @(List Point) 1
    (\_ -> list @Point n (\i -> { x = 0, y = i+1 }));
  (Above c1  c2).layout (f:Int->Int) = c1.layout f ++ c2.layout f;
  (Beside c1 c2).layout (f:Int->Int) = lzw @(List Point)
    (\x -> \y -> x ++ y)
    (c1.layout f)
    (c2.layout (\(x:Int) -> f (c1.width + x)));
  (Stretch ns c).layout (f:Int->Int) = let vs = scanl ns in
    c.layout (\(x:Int) -> f (vs!!x - 1));
};
-- END_CIRCUIT_LAYOUT


----------------------------------------------------------------
-- Modular term
----------------------------------------------------------------
-- BEGIN_TERM
brentKung C = trait [self: CircuitSig<C>] => {
  test = new Above (new Beside (new Fan 2) (new Fan 2))
    (new Above (new Stretch (list @Int 2 (\_->2)) (new Fan 2))
      (new Beside (new Beside (new Identity 1) (new Fan 2)) (new Identity 1)));
};
--END_TERM

----------------------------------------------------------------
-- Variant extension
----------------------------------------------------------------

-- BEGIN_NCIRCUIT_SIG
type NCircuitSig<Circuit> extends CircuitSig<Circuit> = {
  RStretch : (List Int) -> Circuit -> Circuit
};
-- END_NCIRCUIT_SIG

nWidth = trait implements NCircuitSig<Width> inherits width => {
  (RStretch ns c).width = sum ns;
};
nDepth = trait implements NCircuitSig<Depth> inherits depth => {
  (RStretch ns c).depth = c.depth;
};
-- BEGIN_NCIRCUIT_WS
nWellSized = trait implements NCircuitSig<Width%WellSized> inherits wellSized => {
  (RStretch ns c).wS = c.wS && length ns == c.width;
};
-- END_NCIRCUIT_WS

-- nWellSized = trait [fself: NCircuitSig<Width%WellSized>] implements NCircuitSig<Width,WellSized> inherits wellSized => {
--   (RStretch ns c [self : Width & WellSized]).wS = ((Stretch ns c) ^ self).wS
-- };

nLayout = trait implements NCircuitSig<Width%Layout> inherits layout => {
  (RStretch ns c).layout (f:Int->Int) = let vs = scanl ns in
    c.layout (\(x:Int) -> f (vs!!x + ns!!(length ns - 1) - 1))
};

circuit C = trait [self : NCircuitSig<C>] inherits brentKung @C => {
  override test = new RStretch (list @Int 4 (\_->2)) super.test;
};
-- BEGIN_COMPOSITION
scans = new nWidth ,, nDepth ,, nWellSized ,, nLayout ,,
            circuit @(Width & Depth & WellSized & Layout);
--END_COMPOSITION
scans.test.layout (\(x:Int) -> x)
