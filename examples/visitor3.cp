--> "((5 - (2 + 3)) + 3) = 3"

type ExpAlg E = {
  lit : Int -> E,
  add : E -> E -> E
};

type Exp = { accept : forall E . ExpAlg E -> E };

type IEval = { eval : Int };

evalAlg = trait => {
  lit (x : Int)   = { eval = x };
  add (x : IEval) (y : IEval) = { eval = x.eval + y.eval }
};


type SubExpAlg E = (ExpAlg E) & { sub : E -> E -> E };
subEvalAlg = trait inherits evalAlg => {
  sub (x : IEval) (y : IEval) = { eval = x.eval - y.eval }
}; -- : SubExpAlg[IEval];
type ExtExp = { accept: forall E. SubExpAlg E -> E };


type IPrint = { print : String };


printAlg = trait [self : Top] => {
  lit (x : Int) = { print = x.toString };
  add (x : IPrint) (y : IPrint) = { print = "(" ++ x.print ++ " + " ++ y.print ++ ")" };
  sub (x : IPrint) (y : IPrint) = { print = "(" ++ x.print ++ " - " ++ y.print ++ ")" }
}; -- : SubExpAlg[IPrint];



lit (n : Int) = {
  accept E (f: ExpAlg E) = f.lit n
};
add (e1 : Exp) (e2 : Exp) = {
  accept E (f: ExpAlg E) = f.add (e1.accept @E f) (e2.accept @E f)
};
sub (e1 : ExtExp) (e2 : ExtExp) = {
  accept E (f: SubExpAlg E) = f.sub (e1.accept @E f) (e2.accept @E f)
};



-- BEGIN_COMBINE_DEF
combine A (B * A) (f : Trait[Top, SubExpAlg A]) (g : Trait[Top, SubExpAlg B]) = f ,, g;
-- END_COMBINE_DEF

e1  = { accept E (f: ExpAlg E) = f.add (f.lit 2) (f.lit 3) };
e2  = { accept E (f: SubExpAlg E) = f.sub (f.lit 5) (e1.accept @E f) };
e3  = { accept E (f: SubExpAlg E) = f.add (e2.accept @E f) (f.lit 3) };

-- BEGIN_COMBINE1_TEST
alg = combine @IEval @IPrint subEvalAlg printAlg;
o = e3.accept @(IEval & IPrint) (new alg);
o.print ++ " = " ++ o.eval.toString
-- Output: "((5 - (2 + 3)) + 3) = 3"
-- END_COMBINE1_TEST
