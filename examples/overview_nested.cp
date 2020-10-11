--> "-2.0+3.0 = 1.0"

type IPrint = { print : String };

type Lang = { lit : Int -> IPrint, add : IPrint -> IPrint -> IPrint };

type Lang = {lit : Int -> IPrint} & {add : IPrint -> IPrint -> IPrint};

implLang = {
  lit (value : Int) = { print = value.toString },
  add (left : IPrint) (right : IPrint) = {
    print = left.print ++ "+" ++ right.print
  }
} : Lang;

type IEval = { eval : Int };

type LangEval = {
  lit : Int -> IPrint & IEval,
  add : IPrint & IEval -> IPrint & IEval -> IPrint & IEval
};

type EvalExt = { lit : Int -> IEval, add : IEval -> IEval -> IEval };

implEval = {
  lit (value : Int) = { eval = value },
  add (left : IEval) (right : IEval) = {
    eval = left.eval + right.eval
  }
};
implLangEval = (implLang ,, implEval) : LangEval ;

type NegPrint = { neg : IPrint -> IPrint };
type LangNeg = Lang & NegPrint;

implNegPrint = {
  neg (exp : IPrint) = { print = "-" ++ exp.print }
} : NegPrint;

implLangNeg = (implLang ,, implNegPrint) : LangNeg;


type NegEval = { neg : IEval -> IEval};
implNegEval = {
  neg (exp : IEval) = { eval = 0 - exp.eval }
} : NegEval;

type NegEvalExt = { neg : IPrint & IEval -> IPrint & IEval };
type LangNegEval = LangEval & NegEvalExt;
implLangNegEval = (implLangEval ,, implNegPrint ,, implNegEval): LangNegEval ;



type ExpAlg E = { lit : Int -> E, add : E -> E -> E };
type ExpAlgExt E = ExpAlg E & { sub : E -> E -> E };


e1 E (f : ExpAlg E) : E = f.add (f.lit 2) (f.lit 3);    -- 2 + 3
e2 E (f : ExpAlgExt E) : E = f.sub (f.lit 5) (e1 @E f);  -- 5 - (2 + 3)

fac = implLangNegEval;
e = fac.add (fac.neg (fac.lit 2)) (fac.lit 3);
e.print ++ " = " ++ e.eval.toString -- Output: "-2+3 = 1"
