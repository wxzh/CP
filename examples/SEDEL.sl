--BEGIN_SEDEL_EXPALG
type GExpAlg[E,OE] = {
  lit : Int -> OE,
  add : E -> E -> OE
};
type ExpAlg[E] = GExpAlg[E,E];
--END_SEDEL_EXPALG

--BEGIN_SEDEL_EVAL
trait evalAlg => {
  lit (n: Int) = { eval = n };
  add (e1: IEval) (e2: IEval) = { eval = e1.eval + e2.eval }
} : ExpAlg[IEval];
--END_SEDEL_EVAL

--BEGIN_SEDEL_COMPOSED
merge A B C [D * B] (f : Trait[GExpAlg[A,B]]) (g : Trait[GExpAlg[C,D]]) =
  trait inherits f & g => {};
mergedAlg = merge IEval IEval IEval&IPrint IPrint evalAlg dprintAlg;
--END_SEDEL_COMPOSED

--BEGIN_FIP_EVAL
eval = {
  lit (n: Int) = { eval = n },
  add (e1: IEval) (e2: IEval) = { eval = e1.eval + e2.eval }
};
--END_FIP_EVAL

--BEGIN_SEDEL_DPRINT
type IPrint = { print : String };
trait dprintAlg => {
  lit (n: Int) = { print = n.toString };
  add (e1: IPrint & IEval) (e2: IPrint & IEval) = {
    print = if (e1.eval == 0) then e2.print else e1.print ++ "+" ++ e2.print
  }
} : GExpAlg[IEval & IPrint, IPrint];
--END_SEDEL_DPRINT

--BEGIN_FIP_PRINT
print = {
  lit (n: Int) = { print = n.toString },
  add (e1: IPrint & IEval) (e2: IPrint & IEval) = {
    print = if (e1.eval == 0) then e2.print
            else e1.print + "+" + e2.print
  }
};
--END_FIP_PRINT

--BEGIN_SEDEL_EXPEXT
type ExpExtAlg[E] = ExpAlg[E] & {
  mul : E -> E -> E
};
--END_SEDEL_EXPEXT

trait negIEvalAlg inherits evalAlg => {
  neg (x : IIEval) = { eval = 0 - x.eval }
};
trait negIPrintAlg inherits dprintAlg => {
  neg (x : IIPrint) = { print= "-" ++ x.print }
};

--BEGIN_SEDEL_TERM
type Exp = { accept : forall E . ExpAlg[E] -> E };
e1 : Exp = { accept E f = f.add (f.lit 0) (f.lit 1) };
--END_SEDEL_TERM
o = e1.accept (IEval & IPrint) (new[ExpAlg[IEval & IPrint]] combinedAlg);

type ExtExp = { accept: forall E. ExpExtAlg[E] → E };
(eval ,, print) : Exp (IEval & IPrint)