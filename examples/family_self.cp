--> "2 + 3 and 5 + 4 = 9"

type ExpAlg E = {
  lit : Int -> E,
  add : E -> E -> E
};

type Exp = { accept : forall E . ExpAlg E -> E };

type IEval = { eval : Int };
type IPrint = { print : String };


evalAlg = trait => {
  lit (x : Int)   = { eval = x };
  add (x : IEval) (y : IEval) = { eval = x.eval + y.eval }
};


e1 = { accept = /\E . \(f: ExpAlg E) -> f.add (f.lit 2) (f.lit 3) };


-- Family self reference
printAlg3 = trait [fself : ExpAlg (IEval & IPrint)] => {
  lit (x : Int)  = { print = x.toString };
  add (e1 : IPrint) (e2 : IPrint) = { print =
    let plus54 = fself.add (fself.lit 5) (fself.lit 4)
    in e1.print ++ " + " ++ e2.print ++ " and " ++ "5 + 4 = " ++ plus54.eval.toString
  }
};

evalAlg2 = trait => {
  lit (x : Int) = { eval = x + 1 };
  add (x : IEval) (y : IEval) = { eval = x.eval + y.eval }
};

o = new evalAlg ,, printAlg3;

(e1.accept @(IEval & IPrint) o).print
