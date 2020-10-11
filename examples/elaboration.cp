--BEGIN_DESUGAR_EXPSIG
type ExpSig Exp OExp =
  { Lit : Double -> Trait[Exp,OExp] } &
  { Add : Exp -> Exp -> Trait[Exp,OExp] };
--END_DESUGAR_EXPSIG

type Eval = { eval : Double };

--BEGIN_DESUGAR_EVALNUM
evalNum = trait [self: Top] implements ExpSig Eval Eval => open self in
  { Lit = \(n: Double) -> trait => { eval = n } } ,,
  { Add = \(e1: Eval) -> \(e2: Eval) -> trait => { eval = e1.eval + e2.eval} };
--END_DESUGAR_EVALNUM

--BEGIN_DESUGAR_EXPADD
expAdd = /\Exp. trait [self: ExpSig Exp Exp] => open self in {
  test = new Add (new Lit 4) (new Lit 8);
};
--END_DESUGAR_EXPADD


--BEGIN_DESUGAR_MULSIG
type MulSig Exp OExp =
  { Lit : Double -> Trait[Exp,OExp] } &
  { Add : Exp -> Exp -> Trait[Exp,OExp] } &
  { Mul : Exp -> Exp -> Trait[Exp,OExp] };
--END_DESUGAR_MULSIG

--BEGIN_DESUGAR_EVALMUL
evalMul = trait implements MulSig Eval Eval inherits evalNum => {
  Mul e1 e2 = trait => { eval = e1.eval * e2.eval};
};
--END_DESUGAR_EVALMUL
type Print = { print : String };

--BEGIN_DESUGAR_PRINTCHILD
printChild = trait [self: Top] implements ExpSig (Eval&Print) Print => open self in
  { Lit (n: Double) = trait => { print = n.toString } } ,,
  { Add (e1: Eval&Print) (e2: Eval&Print) =
    { print = if e2.eval == 0 then e1.print
              else "(" ++ e1.print ++ "+" ++ e2.print ++ ")" } };
--END_DESUGAR_PRINTCHILD

--BEGIN_DESUGAR_EXPMUL
evalMul = /\Exp. trait [self : MulSig<Exp>] inherits expAdd @Exp => {
  override test = new Mul super.test (new Lit 4);
};
--END_DESUGAR_EXPMUL
trait implements (ExpSig (Eval&Print) Print) => {
  (Lit     n).print = n.toString;
  (Add e1 e2).print = if e2.eval == 0 then e1.print
                      else "(" ++ e1.print ++ "+" ++ e2.print ++ ")";
}

-- (new printChild ,, evalNum ,, expAdd @Eval).test.eval
-- evalNum
