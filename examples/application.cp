--> "-(2.0 + 3.0) = -5.0"

type ExpAlg E = { lit : Int -> E, add : E -> E -> E };
type IEval = { eval : Int };
evalAlg = trait => {
  lit (x : Int) = { eval = x };
  add (x : IEval) (y : IEval) = { eval = x.eval + y.eval }
};

type Exp = { accept : forall E . ExpAlg E -> E };

e1 = { accept E (f: ExpAlg E) = f.add (f.lit 2) (f.lit 3) };


-- BEGIN_PRINT_DEF
type IPrint = { print : String };
printAlg = trait => {
  lit (x : Int) = { print = x.toString };
  add (x : IPrint) (y : IPrint) = {
    print = "(" ++ x.print ++ " + " ++ y.print ++ ")"
  }
};
-- END_PRINT_DEF


-- BEGIN_SUB_DEF
type ExpExtAlg E = (ExpAlg E) & { neg : E -> E };
negEvalAlg = trait inherits evalAlg => {
  neg (x : IEval) = { eval = 0 - x.eval }
};
negPrintAlg = trait inherits printAlg => {
  neg (x : IPrint) = { print= "-" ++ x.print }
};
-- END_SUB_DEF


-- BEGIN_EXPEXT_TYPE
type ExtExp = { accept: forall E. ExpExtAlg E -> E };
-- END_EXPEXT_TYPE


-- BEGIN_VALUE_E2
e2 = { accept E (f: ExpExtAlg E) = f.neg (e1.accept @E f) };
-- END_VALUE_E2


-- BEGIN_COMBINE
combine A (B * A) (f : Trait[ExpExtAlg A]) (g : Trait[ExpExtAlg B]) = f ,, g;
-- END_COMBINE

-- BEGIN_NEW_ALG
combinedAlg = combine @IEval @IPrint negEvalAlg negPrintAlg;
-- END_NEW_ALG




-- BEGIN_CLOSE
expExtAlg = trait inherits negEvalAlg ,, printAlg => {
  neg (x : IPrint) = { print= "-" ++ x.print }
};
-- END_CLOSE

-- BEGIN_USE
o = e2.accept @(IEval & IPrint) (new combinedAlg);
o.print ++ " = " ++ o.eval.toString -- "-(2.0 + 3.0) = -5.0"
-- END_USE
