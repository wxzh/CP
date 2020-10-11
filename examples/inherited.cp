--> "{1.0}+\n {3.0}+\n  {4.0}"

type Exp<E> = {
  Lit : Int -> E;
  Add : E -> E -> E;
};

exp E = trait [self : Exp<E>] => {
  exp = new Add (new Lit 1) (new Add (new Lit 2) (new Lit 3));
};

type Indent = { indent : String };
type PrintInd = { print : Indent -> String };
expPrintInd = trait implements Exp<PrintInd> => {
  (Lit     n).print (inh:Indent) = inh.indent ++ n.toString;
  (Add e1 e2).print (inh:Indent) = e1.print inh ++ "+\n" ++
                                   e2.print { indent = inh.indent ++ " " };
};

-- (new expPrintInd ,, exp @PrintInd).exp.print { indent = "" }

type Cnt = { cnt : Int };
expCnt = trait implements Exp<Cnt> => {
  (Lit     n).cnt = 1;
  (Add e1 e2).cnt = e1.cnt + e2.cnt;
};

type Pos = { pos : Int };
type PrintPos =  { print : Pos -> String };
expPrintPos = trait implements Exp<Cnt % PrintPos> => {
  (Lit     n).print (inh:Pos) = "{" ++ inh.pos.toString ++ "}";
  (Add e1 e2).print (inh:Pos) = e1.print { pos = inh.pos + 1 } ++ "+" ++
                                e2.print { pos = inh.pos + e1.cnt + 1 };
};

{-------------------------------------
"1 + (2 + 3)"
=>  Add (Lit 1) (Add (Lit 2) (Lit 3))
cnt 3    1       2    1       1
pos 0    1       2    3       4
-------------------------------------}

-- (new expCnt ,, expPrintPos ,, exp @(Cnt & PrintPos)).exp.print { pos = 0 }

type PrintIndPos = { print : Indent&Pos -> String };
expPrintIndPos = trait implements Exp<Cnt % PrintIndPos> => {
  (Lit     n).print (inh:Indent&Pos) =
    inh.indent ++ "{" ++ inh.pos.toString ++ "}";
  (Add e1 e2).print (inh:Indent&Pos) =
    e1.print { indent = inh.indent, pos = inh.pos + 1 } ++ "+\n" ++
    e2.print { indent = inh.indent ++ " ", pos = inh.pos + e1.cnt + 1 };
};

(new expCnt ,, expPrintIndPos ,, exp @(Cnt & PrintIndPos)).exp.print { indent = "", pos = 0 }
