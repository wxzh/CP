--> "let $x = (1.0+1.0) in $x^10.0 = 1024.0"

--------------
--  Common  --
--------------

type Env T = String -> T;
type EnvD = Env Double;

empty T = \(_ : String) -> undefined : T;
eD = empty @Double;

lookup T (s : String) (env : Env T) = env s;

insert T (s : String) (v : T) (env : Env T) =
  \(s': String) -> if s == s' then v else lookup @T s' env;

type Eval T = { eval : EnvD -> T };
type EvalD = Eval Double;
type EvalB = Eval Bool;

type Print = { print : String };

type Log = { log : EnvD -> String };

type Codegen = { codegen : String };


--------------
--  Number  --
--------------

type NExprSig<E> = {
  Lit : Double -> E,
  Neg : E -> E,
  Add : E -> E -> E,
  Sub : E -> E -> E,
  Mul : E -> E -> E,
  Div : E -> E -> E,
  Pow : E -> E -> E
};

pow (b:Double) (x:Double) : Double = if x == 0 then 1 else b * pow b (x-1);

exprNEval = trait implements NExprSig<EvalD> => {
  (Lit n).eval (_:EnvD) = n;
  (Neg e).eval (env:EnvD) = 0 - e.eval env;
  (Add e1 e2).eval (env:EnvD) = e1.eval env + e2.eval env;
  (Sub e1 e2).eval (env:EnvD) = e1.eval env - e2.eval env;
  (Mul e1 e2).eval (env:EnvD) = e1.eval env * e2.eval env;
  (Div e1 e2).eval (env:EnvD) = e1.eval env / e2.eval env;
  (Pow e1 e2).eval (env:EnvD) = pow (e1.eval env) (e2.eval env);
};

exprNPrint = trait implements NExprSig<Print> => {
  (Lit n).print = n.toString;
  (Neg e).print = "(-" ++ e.print ++ ")";
  (Add e1 e2).print = "(" ++ e1.print ++ "+" ++ e2.print ++ ")";
  (Sub e1 e2).print = "(" ++ e1.print ++ "-" ++ e2.print ++ ")";
  (Mul e1 e2).print = "(" ++ e1.print ++ "*" ++ e2.print ++ ")";
  (Div e1 e2).print = "(" ++ e1.print ++ "/" ++ e2.print ++ ")";
  (Pow e1 e2).print = e1.print ++ "^" ++ e2.print;
};

exprNPrint' = trait implements NExprSig<EvalD%Print> => {
  (Lit n).print = n.toString;
  (Neg e).print = if e.eval eD == 0 then "0" else "(-" ++ e.print ++ ")";
  (Add e1 e2).print = if e1.eval eD == 0 then e2.print
                      else if e2.eval eD == 0 then e1.print
                      else "(" ++ e1.print ++ "+" ++ e2.print ++ ")";
  (Sub e1 e2).print = if e1.eval eD == 0 then "(-" ++ e2.print ++ ")"
                      else if e2.eval eD == 0 then e1.print
                      else "(" ++ e1.print ++ "-" ++ e2.print ++ ")";
  (Mul e1 e2).print = if e1.eval eD == 0 || e2.eval eD == 0 then "0"
                      else "(" ++ e1.print ++ "*" ++ e2.print ++ ")";
  (Div e1 e2).print = if e1.eval eD == 0 then "0"
                      else if e2.eval eD == 0 then "NaN"
                      else "(" ++ e1.print ++ "/" ++ e2.print ++ ")";
  (Pow e1 e2).print = if e1.eval eD == 0 then "0"
                      else if e2.eval eD == 0 then "1"
                      else e1.print ++ "^" ++ e2.print;
};

printAux (val:Double) (e1:Print) (e2:Print) (sep:String) =
  if val == 0 then "0" else "(" ++ e1.print ++ sep ++ e2.print ++ ")";

exprNPrint'' = trait implements NExprSig<EvalD%Print> => {
  (Lit n).print = n.toString;
  (Neg e [self:EvalD]).print = if self.eval eD == 0 then "0"
                              else "(-" ++ e.print ++ ")";
  (Add e1 e2 [self:EvalD]).print = printAux (self.eval eD) e1 e2 "+";
  (Sub e1 e2 [self:EvalD]).print = printAux (self.eval eD) e1 e2 "-";
  (Mul e1 e2 [self:EvalD]).print = printAux (self.eval eD) e1 e2 "*";
  (Div e1 e2 [self:EvalD]).print = printAux (self.eval eD) e1 e2 "/";
  (Pow e1 e2 [self:EvalD]).print = printAux (self.eval eD) e1 e2 "^";
};

exprNLog = trait implements NExprSig<EvalD&Print%Log> => {
  (Lit n [self:Print]).log (_:EnvD) = self.print;
  (Neg e [self:Print]).log (_:EnvD) = self.print;
  (Add e1 e2 [self:EvalD&Print]).log (env:EnvD) = self.print ++ " = " ++ (self.eval env).toString;
  (Sub e1 e2 [self:EvalD&Print]).log (env:EnvD) = self.print ++ " = " ++ (self.eval env).toString;
  (Mul e1 e2 [self:EvalD&Print]).log (env:EnvD) = self.print ++ " = " ++ (self.eval env).toString;
  (Div e1 e2 [self:EvalD&Print]).log (env:EnvD) = self.print ++ " = " ++ (self.eval env).toString;
  (Pow e1 e2 [self:EvalD&Print]).log (env:EnvD) = self.print ++ " = " ++ (self.eval env).toString;
};

exprNCodegen = trait implements NExprSig<Codegen> => {
  (Lit n).codegen = "ldc_w " ++ n.toString ++ "\n";
  (Neg e).codegen = e.codegen ++ "dneg\n";
  (Add e1 e2).codegen = e1.codegen ++ e2.codegen ++ "dadd\n";
  (Sub e1 e2).codegen = e1.codegen ++ e2.codegen ++ "dsub\n";
  (Mul e1 e2).codegen = e1.codegen ++ e2.codegen ++ "dmul\n";
  (Div e1 e2).codegen = e1.codegen ++ e2.codegen ++ "ddiv\n";
  (Pow e1 e2).codegen = e1.codegen ++ e2.codegen ++
                        "invokestatic java/lang/Math/pow(DD)D\n";
};

exprN N = trait [self : NExprSig<N>] => {
  zero = new Add (new Sub (new Lit 0) (new Lit 0)) (new Lit 0);
  pow = new Pow (new Mul (new Lit 2) (new Lit 2))
                (new Add (new Lit 1) (new Lit 1));
};

num = new exprNEval ,, exprNPrint ,, exprNLog ,, exprNCodegen ,,
          exprN @(EvalD & Print & Log & Codegen);
-- num.pow.log eD


---- inherited attributes ----

type IndentedPrint = { print : String -> String };
exprIndentedPrint = trait implements NExprSig<IndentedPrint> => {
  (Lit n).print (indent:String) = n.toString;
  (Neg e).print (indent:String) = indent ++ "(-" ++ e.print "" ++ ")";
  (Add e1 e2).print (indent:String) = "(" ++ e1.print indent ++ " +\n" ++ indent ++ e2.print (indent ++ " ") ++ ")";
  (Sub e1 e2).print (indent:String) = "(" ++ e1.print indent ++ " -\n" ++ indent ++ e2.print (indent ++ " ") ++ ")";
  (Mul e1 e2).print (indent:String) = "(" ++ e1.print indent ++ " *\n" ++ indent ++ e2.print (indent ++ " ") ++ ")";
  (Div e1 e2).print (indent:String) = "(" ++ e1.print indent ++ " /\n" ++ indent ++ e2.print (indent ++ " ") ++ ")";
  (Pow e1 e2).print (indent:String) = "(" ++ e1.print indent ++ " ^\n" ++ indent ++ e2.print (indent ++ " ") ++ ")";
};

num = new exprIndentedPrint ,, exprN @IndentedPrint;
-- num.zero.print " "


---- mutual dependency ----

type PrintAux = { printAux : String };

exprPrintMutual = trait implements NExprSig<PrintAux%Print> => {
  (Lit n).print = n.toString;
  (Neg e).print = "-" ++ e.printAux;
  (Add e1 e2).print = e1.printAux ++ "+" ++ e2.printAux;
  (Sub e1 e2).print = e1.printAux ++ "-" ++ e2.printAux;
  (Mul e1 e2).print = e1.printAux ++ "*" ++ e2.printAux;
  (Div e1 e2).print = e1.printAux ++ "/" ++ e2.printAux;
  (Pow e1 e2).print = e1.printAux ++ "^" ++ e2.printAux;
};

exprPrintAux = trait implements NExprSig<Print%PrintAux> => {
  (Lit n [self:Print]).printAux = self.print;
  (Neg e [self:Print]).printAux = "(" ++ self.print ++ ")";
  (Add e1 e2 [self:Print]).printAux = "(" ++ self.print ++ ")";
  (Sub e1 e2 [self:Print]).printAux = "(" ++ self.print ++ ")";
  (Mul e1 e2 [self:Print]).printAux = "(" ++ self.print ++ ")";
  (Div e1 e2 [self:Print]).printAux = "(" ++ self.print ++ ")";
  (Pow e1 e2 [self:Print]).printAux = "(" ++ self.print ++ ")";
};

p = new exprPrintMutual ,, exprPrintAux ,, exprN @(Print & PrintAux);
-- p.zero.print


---------------
--  Boolean  --
---------------

type BExprSig<E> = {
  True  : E,
  False : E,
  Not : E -> E,
  And : E -> E -> E,
  Or  : E -> E -> E,
  Xor : E -> E -> E
};

exprBEval = trait implements BExprSig<EvalB> => {
  (True).eval (_:EnvD) = true;
  (False).eval (_:EnvD) = false;
  (Not e).eval (env:EnvD) = if e.eval env then false else true;
  (And e1 e2).eval (env:EnvD) = e1.eval env && e2.eval env;
  (Or e1 e2).eval (env:EnvD) = e1.eval env || e2.eval env;
  (Xor e1 e2).eval (env:EnvD) = e1.eval env != e2.eval env;
};

exprBPrint = trait implements BExprSig<Print> => {
  (True).print = "true";
  (False).print = "false";
  (Not e).print = "(not " ++ e.print ++ ")";
  (And e1 e2).print = "(" ++ e1.print ++ " and " ++ e2.print ++ ")";
  (Or e1 e2).print = "(" ++ e1.print ++ " or " ++ e2.print ++ ")";
  (Xor e1 e2).print = "(" ++ e1.print ++ " xor " ++ e2.print ++ ")";
};

exprBPrint' = trait implements BExprSig<Print> => {
  (True).print = "T";
  (False).print = "F";
  (Not e).print = "(!" ++ e.print ++ ")";
  (And e1 e2).print = "(" ++ e1.print ++ "&&" ++ e2.print ++ ")";
  (Or e1 e2).print = "(" ++ e1.print ++ "||" ++ e2.print ++ ")";
  (Xor e1 e2).print = "(" ++ e1.print ++ "!=" ++ e2.print ++ ")";
};

exprBLog = trait implements BExprSig<EvalB&Print%Log> => {
  (True [self:Print]).log (_:EnvD) = self.print;
  (False [self:Print]).log (_:EnvD) = self.print;
  (Not e [self:EvalB&Print]).log (env:EnvD) = self.print ++ " = " ++ (self.eval env).toString;
  (And e1 e2 [self:EvalB&Print]).log (env:EnvD) = self.print ++ " = " ++ (self.eval env).toString;
  (Or e1 e2 [self:EvalB&Print]).log (env:EnvD) = self.print ++ " = " ++ (self.eval env).toString;
  (Xor e1 e2 [self:EvalB&Print]).log (env:EnvD) = self.print ++ " = " ++ (self.eval env).toString;
};

exprBCodegen = trait implements BExprSig<Codegen> => {
  (True).codegen = "iconst_1\n";
  (False).codegen = "iconst_0\n";
  (Not e).codegen = e.codegen ++ "ineg\n";
  (And e1 e2).codegen = e1.codegen ++ e2.codegen ++ "iand\n";
  (Or e1 e2).codegen = e1.codegen ++ e2.codegen ++ "ior\n";
  (Xor e1 e2).codegen = e1.codegen ++ e2.codegen ++ "ixor\n";
};

exprB B = trait [self : BExprSig<B>] => {
  unary = new Not (new Not (new True));
  binary = new And (new Or (new True) (new False))
                   (new Xor (new True) (new False));
};

bool = new exprBEval ,, exprBPrint' ,, exprBLog ,, exprBCodegen ,,
           exprB @(EvalB & Print & Log & Codegen);
-- bool.binary.log eD


------------------
--  Comparison  --
------------------

type CExprSig<B> N = {
  Eq : N -> N -> B,
  Ne : N -> N -> B,
  Lt : N -> N -> B,
  Le : N -> N -> B,
  Gt : N -> N -> B,
  Ge : N -> N -> B
};

exprCEval = trait implements CExprSig<EvalB> EvalD => {
  (Eq e1 e2).eval (env:EnvD) = e1.eval env == e2.eval env;
  (Ne e1 e2).eval (env:EnvD) = e1.eval env != e2.eval env;
  (Lt e1 e2).eval (env:EnvD) = e1.eval env < e2.eval env;
  (Le e1 e2).eval (env:EnvD) = e1.eval env < e2.eval env || e1.eval env == e2.eval env;
  (Gt e1 e2).eval (env:EnvD) = e1.eval env > e2.eval env;
  (Ge e1 e2).eval (env:EnvD) = e1.eval env > e2.eval env || e1.eval env == e2.eval env;
};

exprCPrint = trait implements CExprSig<Print> Print => {
  (Eq e1 e2).print = "(" ++ e1.print ++ " == " ++ e2.print ++ ")";
  (Ne e1 e2).print = "(" ++ e1.print ++ " != " ++ e2.print ++ ")";
  (Lt e1 e2).print = "(" ++ e1.print ++ " < " ++ e2.print ++ ")";
  (Le e1 e2).print = "(" ++ e1.print ++ " <= " ++ e2.print ++ ")";
  (Gt e1 e2).print = "(" ++ e1.print ++ " > " ++ e2.print ++ ")";
  (Ge e1 e2).print = "(" ++ e1.print ++ " >= " ++ e2.print ++ ")";
};

exprCLog = trait implements CExprSig<EvalB&Print%Log> Top => {
  (Eq e1 e2 [self:EvalB&Print]).log (env:EnvD) = self.print ++ " = " ++ (self.eval env).toString;
  (Ne e1 e2 [self:EvalB&Print]).log (env:EnvD) = self.print ++ " = " ++ (self.eval env).toString;
  (Lt e1 e2 [self:EvalB&Print]).log (env:EnvD) = self.print ++ " = " ++ (self.eval env).toString;
  (Le e1 e2 [self:EvalB&Print]).log (env:EnvD) = self.print ++ " = " ++ (self.eval env).toString;
  (Gt e1 e2 [self:EvalB&Print]).log (env:EnvD) = self.print ++ " = " ++ (self.eval env).toString;
  (Ge e1 e2 [self:EvalB&Print]).log (env:EnvD) = self.print ++ " = " ++ (self.eval env).toString;
};

exprCCodegen = trait implements CExprSig<Codegen> Codegen => {
  (Eq e1 e2).codegen = e1.codegen ++ e2.codegen ++ "dcmpg\n" ++
    "ifeq L1\niconst_0\ngoto L2\nL1: iconst_1\nL2: nop\n";
  (Ne e1 e2).codegen = e1.codegen ++ e2.codegen ++ "dcmpg\n" ++
    "ifne L1\niconst_0\ngoto L2\nL1: iconst_1\nL2: nop\n";
  (Lt e1 e2).codegen = e1.codegen ++ e2.codegen ++ "dcmpg\n" ++
    "iflt L1\niconst_0\ngoto L2\nL1: iconst_1\nL2: nop\n";
  (Le e1 e2).codegen = e1.codegen ++ e2.codegen ++ "dcmpg\n" ++
    "ifle L1\niconst_0\ngoto L2\nL1: iconst_1\nL2: nop\n";
  (Gt e1 e2).codegen = e1.codegen ++ e2.codegen ++ "dcmpg\n" ++
    "ifgt L1\niconst_0\ngoto L2\nL1: iconst_1\nL2: nop\n";
  (Ge e1 e2).codegen = e1.codegen ++ e2.codegen ++ "dcmpg\n" ++
    "ifge L1\niconst_0\ngoto L2\nL1: iconst_1\nL2: nop\n";
};

exprC N B = trait [self : NExprSig<N> & BExprSig<B> & CExprSig<B> N] => {
  cmp = new And (new Ge (new Lit 3.14) (new Lit 3))
                (new Lt (new Lit 3.14) (new Lit 4));
};

cmp = new exprNEval ,, exprBEval ,, exprCEval ,,
          exprNPrint ,, exprBPrint ,, exprCPrint ,,
          exprNLog ,, exprBLog ,, exprCLog ,,
          exprNCodegen ,, exprBCodegen ,, exprCCodegen ,,
          exprC @(EvalD & Print & Log & Codegen)
                @(EvalB & Print & Log & Codegen);
-- cmp.cmp.log eD


--------------
--  Branch  --
--------------

type BrExprSig<N> B = {
  If : B -> N -> N -> N,
  Unless : B -> N -> N -> N
};

exprBrEval = trait implements BrExprSig<EvalD> EvalB => {
  (If b e1 e2).eval (env:EnvD) = if b.eval env then e1.eval env else e2.eval env;
  (Unless b e1 e2).eval (env:EnvD) = if b.eval env then e2.eval env else e1.eval env;
};

exprBrPrint = trait implements BrExprSig<Print> Print => {
  (If b e1 e2).print = "(if " ++ b.print ++ " then " ++ e1.print ++ " else " ++ e2.print ++ ")";
  (Unless b e1 e2).print = "(unless " ++ b.print ++ " then " ++ e1.print ++ " else " ++ e2.print ++ ")";
};

exprBrPrint' = trait implements BrExprSig<Print> Print => {
  (If b e1 e2).print = "(" ++ b.print ++ " ? " ++ e1.print ++ " : " ++ e2.print ++ ")";
  (Unless b e1 e2).print = "(" ++ b.print ++ " ? " ++ e2.print ++ " : " ++ e1.print ++ ")";
};

exprBrLog = trait implements BrExprSig<EvalD&Print%Log> Top => {
  (If b e1 e2 [self:EvalD&Print]).log (env:EnvD) = self.print ++ " = " ++ (self.eval env).toString;
  (Unless b e1 e2 [self:EvalD&Print]).log (env:EnvD) = self.print ++ " = " ++ (self.eval env).toString;
};

exprBrCodegen = trait implements BrExprSig<Codegen> Codegen => {
  (If b e1 e2).codegen = b.codegen ++ "ifeq L1\n" ++ e1.codegen ++
    "goto L2\nL1: " ++ e2.codegen ++ "L2: nop\n";
  (Unless b e1 e2).codegen = b.codegen ++ "ifne L1\n" ++ e1.codegen ++
    "goto L2\nL1: " ++ e2.codegen ++ "L2: nop\n";
};

exprBr N B = trait [self : NExprSig<N> & BExprSig<B> & CExprSig<B> N & BrExprSig<N> B] => {
  branch = new If (new And (new Eq (new Lit 1.1) (new Lit 1.1)) (new Not (new True)))
           (new Div (new Lit 0) (new Lit 0))
           (new If (new Lt (new Lit 4) (new Lit 8))
                   (new Pow (new Add (new Lit 1) (new Lit 1))
                            (new Mul (new Lit 2) (new Lit 5)))
                   (new Neg (new Lit 42)));
};

expr = new exprNEval ,, exprBEval ,, exprCEval ,, exprBrEval ,,
           exprNPrint ,, exprBPrint ,, exprCPrint ,, exprBrPrint ,,
           exprNLog ,, exprBLog ,, exprCLog ,, exprBrLog ,,
           exprNCodegen ,, exprBCodegen ,, exprCCodegen ,, exprBrCodegen ,,
           exprBr @(EvalD & Print & Log & Codegen)
                  @(EvalB & Print & Log & Codegen);
-- expr.branch.log eD


type CmpExprSig<N> = {
  -- three branches for <, =, > compared with zero
  Cmp : N -> N -> N -> N -> N
};

exprCmpEval = trait implements CmpExprSig<EvalD> => {
  (Cmp n lt eq gt).eval (env:EnvD) =
    if n.eval env < 0 then lt.eval env
    else if n.eval env == 0 then eq.eval env
    else gt.eval env;
};

exprCmpPrint = trait implements CmpExprSig<Print> => {
  (Cmp n lt eq gt).print = "case " ++ n.print ++ " of\n" ++
                           "(<0) -> " ++ lt.print ++ "\n" ++
                           "(=0) -> " ++ eq.print ++ "\n" ++
                           "(>0) -> " ++ gt.print ++ "\n";
};

exprCmpLog = trait implements CmpExprSig<EvalD&Print%Log> => {
  (Cmp n lt eq gt [self:EvalD&Print]).log (env:EnvD) = self.print ++ " = " ++ (self.eval env).toString;
};

exprCmpCodegen = trait implements CmpExprSig<Codegen> => {
  (Cmp n lt eq gt).codegen = n.codegen ++ "ifge L1\n" ++
    lt.codegen ++ "goto L3\nL1: ifgt L2\n" ++ eq.codegen ++
    "goto L3\nL2: " ++ gt.codegen ++ "L3: nop\n";
};

exprCmp N = trait [self : NExprSig<N> & CmpExprSig<N>] => {
  cmp = new Cmp (new Lit 0)
                (new Lit 1) (new Lit 2) (new Lit 3);
};

cmp = new exprNEval ,, exprCmpEval ,, exprNPrint ,, exprCmpPrint ,,
          exprNLog ,, exprCmpLog ,, exprNCodegen ,, exprCmpCodegen ,,
          exprCmp @(EvalD & Print & Log & Codegen);
-- cmp.cmp.log eD


----------------
--  Variable  --
----------------

type VarExprSig<E> = {
  Let : String -> E -> E -> E,
  Var : String -> E
};

exprVarEval = trait implements VarExprSig<EvalD> => {
  (Let name e1 e2).eval (env:EnvD) =
    e2.eval (insert @Double name (e1.eval env) env);
  (Var name).eval (env:EnvD) =
    lookup @Double name env;
};

exprVarPrint = trait implements VarExprSig<Print> => {
  (Let name e1 e2).print = "let $" ++ name ++ " = " ++ e1.print ++ " in " ++ e2.print;
  (Var name).print = "$" ++ name;
};

exprVarLog = trait implements VarExprSig<EvalD&Print%Log> => {
  (Let name e1 e2 [self:EvalD&Print]).log (env:EnvD) = self.print ++ " = " ++ (self.eval env).toString;
  (Var name [self:EvalD&Print]).log (env:EnvD) = self.print ++ " = " ++ (self.eval env).toString;
};

exprVarCodegen = trait implements VarExprSig<Codegen> => {
  (Let name e1 e2).codegen = e1.codegen ++ "dstore " ++ name ++ "\n" ++ e2.codegen;
  (Var name).codegen = "dload " ++ name ++ "\n";
};

exprVar N = trait [self : NExprSig<N> & VarExprSig<N>] => {
  decl = new Let "x" (new Add (new Lit 1) (new Lit 1))
                 (new Pow (new Var "x") (new Lit 10));
};

decl = new exprNEval ,, exprVarEval ,, exprNPrint ,, exprVarPrint ,,
           exprNLog ,, exprVarLog ,, exprNCodegen ,, exprVarCodegen ,,
           exprVar @(EvalD & Print & Log & Codegen);
decl.decl.log eD
