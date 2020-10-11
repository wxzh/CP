--> "4.0 + 7.0 = 11.0 and 5 + 4 = 9.0"

type IEval = { eval : Double };

type IPrint = { print : String };

fix A (f : A -> A) = letrec s : A = f s in s;

type GExpAlg In Out = {
  lit : Double -> Out,
  add : In -> In -> Out
};

type ExpAlg E = GExpAlg E E;

type Exp = { accept : forall E . ExpAlg E -> E };

type OExpAlg S E = GExpAlg S (S -> E);

evalAlg = trait => {
  lit (x : Double) (oself : IEval) = { eval = x };
  add (x : IEval) (y : IEval) (oself : IEval) = { eval = x.eval + y.eval }
}; -- : OExpAlg[IEval, IEval];


-- This is boilerplate
closeAlg E (alg : OExpAlg E E) = trait => {
  lit (x : Double) = fix @E (alg.lit x);
  add (e1 : E) (e2 : E) = fix @E (alg.add e1 e2)
};

fcloseAlg E (a : OExpAlg E E) = new closeAlg @E a;


-- family and object self-reference

printAlg3 = trait [fself : ExpAlg (IEval & IPrint)] => {

  lit (x : Double) (osefl : IPrint) = { print = x.toString };

  add (e1 : IEval & IPrint) (e2 : IEval & IPrint) (oself : IEval & IPrint) = { print =
    let plus54 = fself.add (fself.lit 5) (fself.lit 4)
    in e1.print ++ " + " ++ e2.print ++ " = " ++ oself.eval.toString ++ " and "
                ++ "5 + 4 = " ++ plus54.eval.toString
  }

};

-- Can subtyping do this?
merge A (B * A) (a : Trait[ExpAlg (A & B), OExpAlg (A & B) A]) (b : Trait[ExpAlg (A & B), OExpAlg (A & B) B]) = trait [self : ExpAlg (A & B)] => {

  lit (x : Double) (oself : A & B) = (a ^ self).lit x oself  ,, (b ^ self).lit x oself;

  add (e1 : A & B) (e2 : A & B) (oself : A & B) = (a ^ self).add e1 e2 oself ,, (b ^ self).add e1 e2 oself

};

close S (a : Trait[ExpAlg S, OExpAlg S S]) = fix @(ExpAlg S) (\(d: ExpAlg S) -> fcloseAlg @S (a ^ d));

alg = close @(IEval & IPrint) (merge @IEval @IPrint evalAlg printAlg3);

exp = { accept E (f: ExpAlg E) = f.add (f.lit 4) (f.lit 7) };

(exp.accept @(IEval & IPrint) alg).print


-- -- trait printAlg2 : OExpAlg[IEval & IPrint, IPrint] { self =>

-- --   def lit x  = \oself -> { print = x.toString }

-- --   def add e1 e2 = \oself -> { print =
-- --     e1.print ++ " + " ++ e2.print ++ " = " ++ oself.eval.toString
-- --   }

-- -- }

-- -- This doesn't work, needs extra subtyping rule(s)?
-- -- def m = new evalAlg & printAlg2

-- -- trait mergeF (a : Trait[OExpAlg[IEval & IPrint, IEval]], b : Trait[OExpAlg[IEval & IPrint, IPrint]])
-- --   : OExpAlg[IEval & IPrint, IEval & IPrint] { self =>

-- --   def lit x = \oself -> (new[OExpAlg[IEval & IPrint, IEval]] a).lit x oself ,, (new[OExpAlg[IEval & IPrint, IPrint]] b).lit x oself

-- --   def add e1 e2 = \oself -> (new[OExpAlg[IEval & IPrint, IEval]] a).add e1 e2 oself ,, (new[OExpAlg[IEval & IPrint, IPrint]] b).add e1 e2 oself

-- -- }

-- -- def m = new[OExpAlg[IEval & IPrint, IEval & IPrint]] mergeF(evalAlg, printAlg2)

-- -- def newAlg : ExpAlg[IEval & IPrint] = fcloseAlg (IEval & IPrint) m
