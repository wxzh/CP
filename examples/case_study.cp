--> "letf $f = <Lambda> in let $x = 9.0 in appf $f $x is 81.0"

--------------
--  Common  --
--------------

type Env T = String -> T;
type  EnvD = {  env : Env Double };
type DEnvD = { denv : Env Double };

empty T = \(_ : String) -> undefined : T;
eD = { env = empty @Double, denv = empty @Double };

lookup T (s : String) (env : Env T) = env s;

insert T (s : String) (v : T) (env : Env T) =
  \(s': String) -> if s == s' then v else lookup @T s' env;

type Eval C T = { eval : C -> T };
type EvalTopD C = Eval C Double;
type EvalTopB C = Eval C Bool;
type EvalEnvD C = Eval (EnvD&C) Double;
type EvalEnvDEnvD C = Eval (EnvD&DEnvD&C) Double;
type EvalD = Eval Top Double;
type EvalB = Eval Top Bool;

type Print = { print : String };

type LogTop C = { log : C -> String };
type LogEnv C = LogTop (EnvD&C);
type LogEnvDEnv C = LogTop (EnvD&DEnvD&C);
type LogS = LogTop Top;

type Codegen = { codegen : String };


--------------
--  Number  --
--------------

type NumericSig<E> = {
  Lit : Double -> E;
  Neg : E -> E;
  Add : E -> E -> E;
  Sub : E -> E -> E;
  Mul : E -> E -> E;
  Div : E -> E -> E;
  Pow : E -> E -> E;
};

pow (b:Double) (x:Double) : Double = if x == 0 then 1 else b * pow b (x-1);

numEval C = trait implements NumericSig<EvalTopD C> => {
  (Lit n).eval (_:C) = n;
  (Neg e).eval (ctx:C) = 0 - e.eval ctx;
  (Add e1 e2).eval (ctx:C) = e1.eval ctx + e2.eval ctx;
  (Sub e1 e2).eval (ctx:C) = e1.eval ctx - e2.eval ctx;
  (Mul e1 e2).eval (ctx:C) = e1.eval ctx * e2.eval ctx;
  (Div e1 e2).eval (ctx:C) = e1.eval ctx / e2.eval ctx;
  (Pow e1 e2).eval (ctx:C) = pow (e1.eval ctx) (e2.eval ctx);
};

numPrint = trait implements NumericSig<Print> => {
  (Lit n).print = n.toString;
  (Neg e).print = "(-" ++ e.print ++ ")";
  (Add e1 e2).print = "(" ++ e1.print ++ "+" ++ e2.print ++ ")";
  (Sub e1 e2).print = "(" ++ e1.print ++ "-" ++ e2.print ++ ")";
  (Mul e1 e2).print = "(" ++ e1.print ++ "*" ++ e2.print ++ ")";
  (Div e1 e2).print = "(" ++ e1.print ++ "/" ++ e2.print ++ ")";
  (Pow e1 e2).print = e1.print ++ "^" ++ e2.print;
};

numPrint' = trait implements NumericSig<EvalD % Print> => {
  (Lit n).print = n.toString;
  (Neg e).print = if e.eval () == 0 then "0" else "(-" ++ e.print ++ ")";
  (Add e1 e2).print = if e1.eval () == 0 then e2.print
                      else if e2.eval () == 0 then e1.print
                      else "(" ++ e1.print ++ "+" ++ e2.print ++ ")";
  (Sub e1 e2).print = if e1.eval () == 0 then "(-" ++ e2.print ++ ")"
                      else if e2.eval () == 0 then e1.print
                      else "(" ++ e1.print ++ "-" ++ e2.print ++ ")";
  (Mul e1 e2).print = if e1.eval () == 0 || e2.eval () == 0 then "0"
                      else "(" ++ e1.print ++ "*" ++ e2.print ++ ")";
  (Div e1 e2).print = if e1.eval () == 0 then "0"
                      else if e2.eval () == 0 then "NaN"
                      else "(" ++ e1.print ++ "/" ++ e2.print ++ ")";
  (Pow e1 e2).print = if e1.eval () == 0 then "0"
                      else if e2.eval () == 0 then "1"
                      else e1.print ++ "^" ++ e2.print;
};

printAux (val:Double) (e1:Print) (e2:Print) (sep:String) =
  if val == 0 then "0" else "(" ++ e1.print ++ sep ++ e2.print ++ ")";

numPrint'' = trait implements NumericSig<EvalD % Print> => {
  (Lit n).print = n.toString;
  (Neg e [self:EvalD]).print = if self.eval () == 0 then "0"
                              else "(-" ++ e.print ++ ")";
  (Add e1 e2 [self:EvalD]).print = printAux (self.eval ()) e1 e2 "+";
  (Sub e1 e2 [self:EvalD]).print = printAux (self.eval ()) e1 e2 "-";
  (Mul e1 e2 [self:EvalD]).print = printAux (self.eval ()) e1 e2 "*";
  (Div e1 e2 [self:EvalD]).print = printAux (self.eval ()) e1 e2 "/";
  (Pow e1 e2 [self:EvalD]).print = printAux (self.eval ()) e1 e2 "^";
};

numLog C = trait implements NumericSig<(EvalTopD C) & Print % LogTop C> => {
  (Lit n [self:Print]).log (_:C) = self.print;
  (Neg e [self:Print]).log (_:C) = self.print;
  (Add e1 e2 [self : (EvalTopD C) & Print]).log (ctx:C) = self.print ++ " = " ++ (self.eval ctx).toString;
  (Sub e1 e2 [self : (EvalTopD C) & Print]).log (ctx:C) = self.print ++ " = " ++ (self.eval ctx).toString;
  (Mul e1 e2 [self : (EvalTopD C) & Print]).log (ctx:C) = self.print ++ " = " ++ (self.eval ctx).toString;
  (Div e1 e2 [self : (EvalTopD C) & Print]).log (ctx:C) = self.print ++ " = " ++ (self.eval ctx).toString;
  (Pow e1 e2 [self : (EvalTopD C) & Print]).log (ctx:C) = self.print ++ " = " ++ (self.eval ctx).toString;
};

numCodegen = trait implements NumericSig<Codegen> => {
  (Lit n).codegen = "ldc_w " ++ n.toString ++ "\n";
  (Neg e).codegen = e.codegen ++ "dneg\n";
  (Add e1 e2).codegen = e1.codegen ++ e2.codegen ++ "dadd\n";
  (Sub e1 e2).codegen = e1.codegen ++ e2.codegen ++ "dsub\n";
  (Mul e1 e2).codegen = e1.codegen ++ e2.codegen ++ "dmul\n";
  (Div e1 e2).codegen = e1.codegen ++ e2.codegen ++ "ddiv\n";
  (Pow e1 e2).codegen = e1.codegen ++ e2.codegen ++ "invokestatic java/lang/Math/pow(DD)D\n";
};

numT N = trait [self : NumericSig<N>] => {
  zero = new Add (new Sub (new Lit 0) (new Lit 0)) (new Lit 0);
  pow = new Pow (new Mul (new Lit 2) (new Lit 2))
                (new Add (new Lit 1) (new Lit 1));
};

num = new numEval @Top ,, numPrint ,,
          numLog @Top ,, numCodegen ,,
          numT @(EvalD & Print & LogS & Codegen);
-- num.pow.log ()


---- mutual dependency ----

type PrintAux = { printAux : String };

numPrintMutual = trait implements NumericSig<PrintAux % Print> => {
  (Lit n).print = n.toString;
  (Neg e).print = "-" ++ e.printAux;
  (Add e1 e2).print = e1.printAux ++ "+" ++ e2.printAux;
  (Sub e1 e2).print = e1.printAux ++ "-" ++ e2.printAux;
  (Mul e1 e2).print = e1.printAux ++ "*" ++ e2.printAux;
  (Div e1 e2).print = e1.printAux ++ "/" ++ e2.printAux;
  (Pow e1 e2).print = e1.printAux ++ "^" ++ e2.printAux;
};

numPrintAux = trait implements NumericSig<Print % PrintAux> => {
  (Lit n [self:Print]).printAux = self.print;
  (Neg e [self:Print]).printAux = "(" ++ self.print ++ ")";
  (Add e1 e2 [self:Print]).printAux = "(" ++ self.print ++ ")";
  (Sub e1 e2 [self:Print]).printAux = "(" ++ self.print ++ ")";
  (Mul e1 e2 [self:Print]).printAux = "(" ++ self.print ++ ")";
  (Div e1 e2 [self:Print]).printAux = "(" ++ self.print ++ ")";
  (Pow e1 e2 [self:Print]).printAux = "(" ++ self.print ++ ")";
};

p = new numPrintMutual ,, numPrintAux ,, numT @(Print & PrintAux);
-- p.zero.print


---------------
--  Boolean  --
---------------

type BoolSig<E> = {
  True  : E;
  False : E;
  Not : E -> E;
  And : E -> E -> E;
  Or  : E -> E -> E,
  Xor : E -> E -> E;
};

boolEval C = trait implements BoolSig<EvalTopB C> => {
  (True).eval (_:C) = true;
  (False).eval (_:C) = false;
  (Not e).eval (ctx:C) = if e.eval ctx then false else true;
  (And e1 e2).eval (ctx:C) = e1.eval ctx && e2.eval ctx;
  (Or e1 e2).eval (ctx:C) = e1.eval ctx || e2.eval ctx;
  (Xor e1 e2).eval (ctx:C) = e1.eval ctx != e2.eval ctx;
};

boolPrint = trait implements BoolSig<Print> => {
  (True).print = "true";
  (False).print = "false";
  (Not e).print = "(not " ++ e.print ++ ")";
  (And e1 e2).print = "(" ++ e1.print ++ " and " ++ e2.print ++ ")";
  (Or e1 e2).print = "(" ++ e1.print ++ " or " ++ e2.print ++ ")";
  (Xor e1 e2).print = "(" ++ e1.print ++ " xor " ++ e2.print ++ ")";
};

boolPrint' = trait implements BoolSig<Print> => {
  (True).print = "T";
  (False).print = "F";
  (Not e).print = "(!" ++ e.print ++ ")";
  (And e1 e2).print = "(" ++ e1.print ++ "&&" ++ e2.print ++ ")";
  (Or e1 e2).print = "(" ++ e1.print ++ "||" ++ e2.print ++ ")";
  (Xor e1 e2).print = "(" ++ e1.print ++ "!=" ++ e2.print ++ ")";
};

boolLog C = trait implements BoolSig<(EvalTopB C) & Print % LogTop C> => {
  (True [self:Print]).log (_:C) = self.print;
  (False [self:Print]).log (_:C) = self.print;
  (Not e [self : (EvalTopB C) & Print]).log (ctx:C) = self.print ++ " = " ++ (self.eval ctx).toString;
  (And e1 e2 [self : (EvalTopB C) & Print]).log (ctx:C) = self.print ++ " = " ++ (self.eval ctx).toString;
  (Or e1 e2 [self : (EvalTopB C) & Print]).log (ctx:C) = self.print ++ " = " ++ (self.eval ctx).toString;
  (Xor e1 e2 [self : (EvalTopB C) & Print]).log (ctx:C) = self.print ++ " = " ++ (self.eval ctx).toString;
};

boolCodegen = trait implements BoolSig<Codegen> => {
  (True).codegen = "iconst_1\n";
  (False).codegen = "iconst_0\n";
  (Not e).codegen = e.codegen ++ "ineg\n";
  (And e1 e2).codegen = e1.codegen ++ e2.codegen ++ "iand\n";
  (Or e1 e2).codegen = e1.codegen ++ e2.codegen ++ "ior\n";
  (Xor e1 e2).codegen = e1.codegen ++ e2.codegen ++ "ixor\n";
};

exprB B = trait [self : BoolSig<B>] => {
  unary = new Not (new Not (new True));
  binary = new And (new Or (new True) (new False))
                   (new Xor (new True) (new False));
};

bool = new boolEval @Top ,, boolPrint' ,,
           boolLog @Top ,, boolCodegen ,,
           exprB @(EvalB & Print & LogS & Codegen);
-- bool.binary.log ()


------------------
--  Comparison  --
------------------

type CompSig<Boolean,Numeric> = {
  Eq : Numeric -> Numeric -> Boolean;
  Ne : Numeric -> Numeric -> Boolean;
  Lt : Numeric -> Numeric -> Boolean;
  Le : Numeric -> Numeric -> Boolean;
  Gt : Numeric -> Numeric -> Boolean;
  Ge : Numeric -> Numeric -> Boolean;
};

compEval C = trait implements CompSig<EvalTopB C,EvalTopD C> => {
  (Eq e1 e2).eval (ctx:C) = e1.eval ctx == e2.eval ctx;
  (Ne e1 e2).eval (ctx:C) = e1.eval ctx != e2.eval ctx;
  (Lt e1 e2).eval (ctx:C) = e1.eval ctx < e2.eval ctx;
  (Le e1 e2).eval (ctx:C) = e1.eval ctx < e2.eval ctx || e1.eval ctx == e2.eval ctx;
  (Gt e1 e2).eval (ctx:C) = e1.eval ctx > e2.eval ctx;
  (Ge e1 e2).eval (ctx:C) = e1.eval ctx > e2.eval ctx || e1.eval ctx == e2.eval ctx;
};

compPrint = trait implements CompSig<Print,Print> => {
  (Eq e1 e2).print = "(" ++ e1.print ++ " == " ++ e2.print ++ ")";
  (Ne e1 e2).print = "(" ++ e1.print ++ " != " ++ e2.print ++ ")";
  (Lt e1 e2).print = "(" ++ e1.print ++ " < " ++ e2.print ++ ")";
  (Le e1 e2).print = "(" ++ e1.print ++ " <= " ++ e2.print ++ ")";
  (Gt e1 e2).print = "(" ++ e1.print ++ " > " ++ e2.print ++ ")";
  (Ge e1 e2).print = "(" ++ e1.print ++ " >= " ++ e2.print ++ ")";
};

compLog C = trait implements CompSig<(EvalTopB C) & Print % LogTop C, Top> => {
  (Eq e1 e2 [self : (EvalTopB C) & Print]).log (ctx:C) = self.print ++ " = " ++ (self.eval ctx).toString;
  (Ne e1 e2 [self : (EvalTopB C) & Print]).log (ctx:C) = self.print ++ " = " ++ (self.eval ctx).toString;
  (Lt e1 e2 [self : (EvalTopB C) & Print]).log (ctx:C) = self.print ++ " = " ++ (self.eval ctx).toString;
  (Le e1 e2 [self : (EvalTopB C) & Print]).log (ctx:C) = self.print ++ " = " ++ (self.eval ctx).toString;
  (Gt e1 e2 [self : (EvalTopB C) & Print]).log (ctx:C) = self.print ++ " = " ++ (self.eval ctx).toString;
  (Ge e1 e2 [self : (EvalTopB C) & Print]).log (ctx:C) = self.print ++ " = " ++ (self.eval ctx).toString;
};

compCodegen = trait implements CompSig<Codegen, Codegen> => {
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

comp N B = trait [self : NumericSig<N> & BoolSig<B> & CompSig<B,N>] => {
  cmp = new Not (new Eq (new Lit 3) (new Lit 4))
};

cmp = new numEval @Top ,, boolEval @Top ,, compEval @Top ,,
          numPrint ,, boolPrint ,, compPrint ,,
          numLog @Top ,, boolLog @Top ,, compLog @Top ,,
          numCodegen ,, boolCodegen ,, compCodegen ,,
          comp @(EvalD & Print & LogS & Codegen)
               @(EvalB & Print & LogS & Codegen);
-- cmp.cmp.log ()


--------------
--  Branch  --
--------------

-- BEGIN_IF_UNLESS
type BranchSig<Boolean,Numeric> = {
  If     : Boolean -> Numeric -> Numeric -> Numeric;
  Unless : Boolean -> Numeric -> Numeric -> Numeric;
};
-- END_IF_UNLESS

branchEval C = trait implements BranchSig<EvalTopB C, EvalTopD C> => {
  (If     b e1 e2).eval (ctx:C) = if b.eval ctx then e1.eval ctx else e2.eval ctx;
  (Unless b e1 e2).eval (ctx:C) = if b.eval ctx then e2.eval ctx else e1.eval ctx;
};
-- END_IF_UNLESS

-- BEGIN_IF_UNLESS_MORE
branchPrint = trait implements BranchSig<Print, Print> => {
  (If     b e1 e2).print =
    "(if "     ++ b.print ++ " then " ++ e1.print ++ " else " ++ e2.print ++ ")";
  (Unless b e1 e2).print =
    "(unless " ++ b.print ++ " then " ++ e1.print ++ " else " ++ e2.print ++ ")";
};

branchPrint' = trait implements BranchSig<Print, Print> => {
  (If     b e1 e2).print = "("++b.print++" ? "++e1.print++" : "++e2.print++")";
  (Unless b e1 e2).print = "("++b.print++" ? "++e2.print++" : "++e1.print++")";
};

branchLog C = trait implements BranchSig<Top, (EvalTopD C) & Print % LogTop C> => {
  (If     b e1 e2 [self : (EvalTopD C) & Print]).log (ctx:C) =
    self.print ++ " is " ++ (self.eval ctx).toString;
  (Unless b e1 e2 [self : (EvalTopD C) & Print]).log (ctx:C) =
    self.print ++ " is " ++ (self.eval ctx).toString;
};
-- END_IF_UNLESS_MORE

branchCodegen = trait implements BranchSig<Codegen, Codegen> => {
  (If     b e1 e2).codegen = b.codegen ++ "ifeq L1\n" ++ e1.codegen ++
    "goto L2\nL1: " ++ e2.codegen ++ "L2: nop\n";
  (Unless b e1 e2).codegen = b.codegen ++ "ifne L1\n" ++ e1.codegen ++
    "goto L2\nL1: " ++ e2.codegen ++ "L2: nop\n";
};

branch N B = trait [self : NumericSig<N> & BoolSig<B> & CompSig<B,N> & BranchSig<B,N>] => {
  branch = new If (new And (new Eq (new Lit 1.1) (new Lit 1.1))
                           (new Not (new True)))
           (new Div (new Lit 0) (new Lit 0))
           (new If (new Lt (new Lit 4) (new Lit 8))
                   (new Pow (new Add (new Lit 1) (new Lit 1))
                            (new Mul (new Lit 2) (new Lit 5)))
                   (new Neg (new Lit 42)));
};

expr = new numEval @Top ,, boolEval @Top ,, compEval @Top ,, branchEval @Top ,,
           numPrint ,, boolPrint ,, compPrint ,, branchPrint ,,
           numLog @Top ,, boolLog @Top ,, compLog @Top ,, branchLog @Top ,,
           numCodegen ,, boolCodegen ,, compCodegen ,, branchCodegen ,,
           branch @(EvalD & Print & LogS & Codegen)
                  @(EvalB & Print & LogS & Codegen);
-- expr.branch.log ()


type CmpExprSig<N> = {
  -- three branches for <, =, > compared with zero
  Cmp : N -> N -> N -> N -> N;
};

cmpEval C = trait implements CmpExprSig<EvalTopD C> => {
  (Cmp n lt eq gt).eval (ctx:C) =
    if n.eval ctx < 0 then lt.eval ctx
    else if n.eval ctx == 0 then eq.eval ctx
    else gt.eval ctx;
};

cmpPrint = trait implements CmpExprSig<Print> => {
  (Cmp n lt eq gt).print = "case " ++ n.print ++ " of\n" ++
                           "(<0) -> " ++ lt.print ++ "\n" ++
                           "(=0) -> " ++ eq.print ++ "\n" ++
                           "(>0) -> " ++ gt.print ++ "\n";
};

cmpLog C = trait implements CmpExprSig<(EvalTopD C) & Print % LogTop C> => {
  (Cmp n lt eq gt [self : (EvalTopD C) & Print]).log (ctx:C) = self.print ++ " = " ++ (self.eval ctx).toString;
};

cmpCodegen = trait implements CmpExprSig<Codegen> => {
  (Cmp n lt eq gt).codegen = n.codegen ++ "ifge L1\n" ++
    lt.codegen ++ "goto L3\nL1: ifgt L2\n" ++ eq.codegen ++
    "goto L3\nL2: " ++ gt.codegen ++ "L3: nop\n";
};

cmpT N = trait [self : NumericSig<N> & CmpExprSig<N>] => {
  cmp = new Cmp (new Lit 0) (new Lit 1) (new Lit 2) (new Lit 3);
};

cmp = new numEval @Top ,, cmpEval @Top ,,
          numPrint ,, cmpPrint ,,
          numLog @Top ,, cmpLog @Top ,,
          numCodegen ,, cmpCodegen ,,
          cmpT @(EvalD & Print & LogS & Codegen);
-- cmp.cmp.log ()


----------------
--  Variable  --
----------------

type VarSig<E> = {
  Let : String -> E -> E -> E;
  Var : String -> E;
};

varEval (C * EnvD) = trait implements VarSig<EvalEnvD C> => {
  (Let name e1 e2).eval (ctx:EnvD&C) =
    e2.eval ({ env = insert @Double name (e1.eval ctx) ctx.env } ,, ctx : C);
  (Var name).eval (ctx:EnvD&C) = lookup @Double name ctx.env;
};

varPrint = trait implements VarSig<Print> => {
  (Let name e1 e2).print = "let $" ++ name ++ " = " ++ e1.print ++ " in " ++ e2.print;
  (Var name).print = "$" ++ name;
};

varLog C = trait implements VarSig<(EvalEnvD C) & Print % LogEnv C> => {
  (Let name e1 e2 [self : (EvalEnvD C) & Print]).log (ctx:EnvD&C) = self.print ++ " is " ++ (self.eval ctx).toString;
  (Var name [self : (EvalEnvD C) & Print]).log (ctx:EnvD&C) = self.print ++ " is " ++ (self.eval ctx).toString;
};

varCodegen = trait implements VarSig<Codegen> => {
  (Let name e1 e2).codegen = e1.codegen ++ "dstore " ++ name ++ "\n" ++ e2.codegen;
  (Var name).codegen = "dload " ++ name ++ "\n";
};

var N = trait [self : NumericSig<N> & VarSig<N>] => {
  decl = new Let "x" (new Add (new Lit 1) (new Lit 1))
                 (new Pow (new Var "x") (new Lit 10));
};

decl = new numEval @EnvD ,, varEval @Top ,,
           numPrint ,, varPrint ,,
           numLog @EnvD ,, varLog @Top ,,
           numCodegen ,, varCodegen ,,
           var @(EvalEnvD Top & Print & LogEnv Top & Codegen);
-- decl.decl.log eD


----------------------------
-- Dynamic Scoped Closure --
----------------------------

type Closure Expr = {
  param : String;
  body  : Expr;
  env   : Env Double;
};

type ClosExprSig<E> = {
  DynLet : String -> E -> E -> E;
  DynApp : Closure E -> E -> E;
};

closEval (C * EnvD&DEnvD) = trait implements ClosExprSig<EvalEnvDEnvD C> => {
  (DynLet name e1 e2).eval (ctx:EnvD&DEnvD&C) =
    e2.eval ({ env  = insert @Double name (e1.eval ctx) ctx.env,
               denv = insert @Double name (e1.eval ctx) ctx.denv } ,,
             ctx : C);
  (DynApp clos e).eval (ctx:EnvD&DEnvD&C) =
    let env' = \(s:String) ->
      if s == clos.param then e.eval ctx
      else ctx.denv s -- ?? clos.env s (* optional coalescing *)
    in clos.body.eval ({ env = env', denv = ctx.denv } ,, ctx : C);
};

closPrint = trait implements ClosExprSig<Print> => {
  (DynLet name e1 e2).print = "dynlet $" ++ name ++ " = " ++ e1.print ++ " in " ++ e2.print;
  (DynApp clos e).print = "dynapp (\\" ++ clos.param ++ " -> " ++ clos.body.print ++ ") " ++ e.print;
};

closLog C = trait implements ClosExprSig<(EvalEnvDEnvD C) & Print % LogEnvDEnv C> => {
  (DynLet name e1 e2 [self : (EvalEnvDEnvD C) & Print]).log (ctx:EnvD&DEnvD&C) = self.print ++ " is " ++ (self.eval ctx).toString;
  (DynApp clos e [self : (EvalEnvDEnvD C) & Print]).log (ctx:EnvD&DEnvD&C) = self.print ++ " is " ++ (self.eval ctx).toString;
};

clos N = trait [self : NumericSig<N> & VarSig<N> & ClosExprSig<N>] => {
  dynlet = let clos = { param = "x",
                        body = new Add (new Var "x") (new Var "a"),
                        env (s:String) = if s == "a" then 1 else undefined : Double }
    in new DynLet "a" (new Lit 2) (new DynApp clos (new Lit 10));
};

dyn = new numEval @(EnvD&DEnvD) ,, varEval @DEnvD ,, closEval @Top ,, numPrint ,, varPrint ,, closPrint ,, numLog @(EnvD&DEnvD) ,, varLog @DEnvD ,, closLog @Top ,, clos @(EvalEnvDEnvD Top & Print & LogEnvDEnv Top);
-- dyn.dynlet.log eD


----------------------
-- Builtin Function --
----------------------

type Func = Double -> Double;
type EnvF = { fn : Env Func };
type EvalEnvF C = Eval (EnvF&C) Double;
type LogEnvF C = LogTop (EnvF&C);

type FuncSig<E> = {
  LetF : String -> Func -> E -> E;
  AppF : String -> E -> E;
};

funcEval (C * EnvF) = trait implements FuncSig<EvalEnvF C> => {
  (LetF name f e).eval (ctx:EnvF&C) =
    e.eval ({ fn = insert @Func name f ctx.fn } ,, ctx : C);
  (AppF name e).eval (ctx:EnvF&C) =
    (lookup @Func name ctx.fn) (e.eval ctx);
};

funcPrint = trait implements FuncSig<Print> => {
  (LetF name f e).print = "letf $" ++ name ++ " = " ++ f.toString ++ " in " ++ e.print;
  (AppF name e).print = "appf $" ++ name ++ " " ++ e.print;
};

funcLog C = trait implements FuncSig<(EvalEnvF C) & Print%LogEnvF C> => {
  (LetF name f e [self : (EvalEnvF C) & Print]).log (ctx:EnvF&C) = self.print ++ " is " ++ (self.eval ctx).toString;
  (AppF name e [self : (EvalEnvF C) & Print]).log (ctx:EnvF&C) = self.print ++ " is " ++ (self.eval ctx).toString;
};

func N = trait [self : NumericSig<N> & VarSig<N> & FuncSig<N>] => {
  app = new LetF "f" (\(x:Int) -> x * x)
                 (new Let "x" (new Lit 9) (new AppF "f" (new Var "x")));
};

expr = new numEval @(EnvD&EnvF) ,, varEval @EnvF ,, funcEval @EnvD ,, numPrint ,, varPrint ,, funcPrint ,, numLog @(EnvD&EnvF) ,, varLog @EnvF ,, funcLog @EnvD ,, func @(EvalEnvD EnvF & Print & LogEnv EnvF);
expr.app.log { env = empty @Double, fn = empty @Func }
