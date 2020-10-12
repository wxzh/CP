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

type Type = { ty : String };

type LogTop C = { log : C -> String };
type LogEnv C = LogTop (EnvD&C);
type LogEnvDEnv C = LogTop (EnvD&DEnvD&C);
type LogS = LogTop Top;

type Codegen = { codegen : String };


--------------
--  Number  --
--------------

type NumSig<Numeric> = {
  Lit : Double -> Numeric;
  Neg : Numeric -> Numeric;
  Add : Numeric -> Numeric -> Numeric;
  Sub : Numeric -> Numeric -> Numeric;
  Mul : Numeric -> Numeric -> Numeric;
  Div : Numeric -> Numeric -> Numeric;
  Mod : Numeric -> Numeric -> Numeric;
  Pow : Numeric -> Numeric -> Numeric;
};

mod (m:Double) (n:Double) : Double =
  if m < 0 then mod (m+n) n
  else if m < n then m
  else mod (m-n) n;

pow (b:Double) (x:Double) : Double =
  if x == 0 then 1 else b * pow b (x-1);

numEval C = trait implements NumSig<EvalTopD C> => {
  (Lit n).eval (_:C) = n;
  (Neg e).eval (ctx:C) = 0 - e.eval ctx;
  (Add e1 e2).eval (ctx:C) = e1.eval ctx + e2.eval ctx;
  (Sub e1 e2).eval (ctx:C) = e1.eval ctx - e2.eval ctx;
  (Mul e1 e2).eval (ctx:C) = e1.eval ctx * e2.eval ctx;
  (Div e1 e2).eval (ctx:C) = e1.eval ctx / e2.eval ctx;
  (Mod e1 e2).eval (ctx:C) = mod (e1.eval ctx) (e2.eval ctx);
  (Pow e1 e2).eval (ctx:C) = pow (e1.eval ctx) (e2.eval ctx);
};

numPrint = trait implements NumSig<Print> => {
  (Lit n).print = n.toString;
  (Neg e).print = "(-" ++ e.print ++ ")";
  (Add e1 e2).print = "(" ++ e1.print ++ "+" ++ e2.print ++ ")";
  (Sub e1 e2).print = "(" ++ e1.print ++ "-" ++ e2.print ++ ")";
  (Mul e1 e2).print = "(" ++ e1.print ++ "*" ++ e2.print ++ ")";
  (Div e1 e2).print = "(" ++ e1.print ++ "/" ++ e2.print ++ ")";
  (Mod e1 e2).print = "(" ++ e1.print ++ "%" ++ e2.print ++ ")";
  (Pow e1 e2).print = e1.print ++ "^" ++ e2.print;
};

numPrint' = trait implements NumSig<EvalD % Print> => {
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
  (Mod e1 e2).print = if e1.eval () == 0 then "0"
                      else if e2.eval () == 0 then "NaN"
                      else "(" ++ e1.print ++ "%" ++ e2.print ++ ")";
  (Pow e1 e2).print = if e1.eval () == 0 then "0"
                      else if e2.eval () == 0 then "1"
                      else e1.print ++ "^" ++ e2.print;
};

printAux (val:Double) (e1:Print) (e2:Print) (sep:String) =
  if val == 0 then "0" else "(" ++ e1.print ++ sep ++ e2.print ++ ")";

numPrint'' = trait implements NumSig<EvalD % Print> => {
  (Lit n).print = n.toString;
  (Neg e [self:EvalD]).print = if self.eval () == 0 then "0"
                              else "(-" ++ e.print ++ ")";
  (Add e1 e2 [self:EvalD]).print = printAux (self.eval ()) e1 e2 "+";
  (Sub e1 e2 [self:EvalD]).print = printAux (self.eval ()) e1 e2 "-";
  (Mul e1 e2 [self:EvalD]).print = printAux (self.eval ()) e1 e2 "*";
  (Div e1 e2 [self:EvalD]).print = printAux (self.eval ()) e1 e2 "/";
  (Mod e1 e2 [self:EvalD]).print = printAux (self.eval ()) e1 e2 "%";
  (Pow e1 e2 [self:EvalD]).print = printAux (self.eval ()) e1 e2 "^";
};

numType = trait implements NumSig<Type> => {
  (Lit n).ty = "Double";
  (Neg e).ty = "Double";
  (Add e1 e2).ty = "Double";
  (Sub e1 e2).ty = "Double";
  (Mul e1 e2).ty = "Double";
  (Div e1 e2).ty = "Double";
  (Mod e1 e2).ty = "Double";
  (Pow e1 e2).ty = "Double";
};

numLog C = trait implements NumSig<(EvalTopD C) & Print & Type % LogTop C> => {
  (Lit n [self:Print & Type]).log (_:C) = self.print ++ " : " ++ self.ty;
  (Neg e [self:Print & Type]).log (_:C) = self.print ++ " : " ++ self.ty;
  (Add e1 e2 [self : (EvalTopD C) & Print & Type]).log (ctx:C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
  (Sub e1 e2 [self : (EvalTopD C) & Print & Type]).log (ctx:C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
  (Mul e1 e2 [self : (EvalTopD C) & Print & Type]).log (ctx:C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
  (Div e1 e2 [self : (EvalTopD C) & Print & Type]).log (ctx:C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
  (Mod e1 e2 [self : (EvalTopD C) & Print & Type]).log (ctx:C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
  (Pow e1 e2 [self : (EvalTopD C) & Print & Type]).log (ctx:C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
};

numCodegen = trait implements NumSig<Codegen> => {
  (Lit n).codegen = "ldc_w " ++ n.toString ++ "\n";
  (Neg e).codegen = e.codegen ++ "dneg\n";
  (Add e1 e2).codegen = e1.codegen ++ e2.codegen ++ "dadd\n";
  (Sub e1 e2).codegen = e1.codegen ++ e2.codegen ++ "dsub\n";
  (Mul e1 e2).codegen = e1.codegen ++ e2.codegen ++ "dmul\n";
  (Div e1 e2).codegen = e1.codegen ++ e2.codegen ++ "ddiv\n";
  (Mod e1 e2).codegen = e1.codegen ++ e2.codegen ++ "drem\n";
  (Pow e1 e2).codegen = e1.codegen ++ e2.codegen ++
    "invokestatic java/lang/Math/pow(DD)D\n";
};

numT N = trait [self : NumSig<N>] => {
  zero = new Add (new Sub (new Lit 0) (new Lit 0)) (new Lit 0);
  mod = new Mod (new Lit 10) (new Lit 3);
  pow = new Pow (new Mul (new Lit 2) (new Lit 2))
                (new Add (new Lit 1) (new Lit 1));
};

num = new numEval @Top ,, numPrint ,, numType ,,
          numLog @Top ,, numCodegen ,,
          numT @(EvalD & Print & Type & LogS & Codegen);
-- num.pow.log ()


---- mutual dependency ----

type PrintAux = { printAux : String };

numPrintMutual = trait implements NumSig<PrintAux % Print> => {
  (Lit n).print = n.toString;
  (Neg e).print = "-" ++ e.printAux;
  (Add e1 e2).print = e1.printAux ++ "+" ++ e2.printAux;
  (Sub e1 e2).print = e1.printAux ++ "-" ++ e2.printAux;
  (Mul e1 e2).print = e1.printAux ++ "*" ++ e2.printAux;
  (Div e1 e2).print = e1.printAux ++ "/" ++ e2.printAux;
  (Mod e1 e2).print = e1.printAux ++ "%" ++ e2.printAux;
  (Pow e1 e2).print = e1.printAux ++ "^" ++ e2.printAux;
};

numPrintAux = trait implements NumSig<Print % PrintAux> => {
  (Lit n [self:Print]).printAux = self.print;
  (Neg e [self:Print]).printAux = "(" ++ self.print ++ ")";
  (Add e1 e2 [self:Print]).printAux = "(" ++ self.print ++ ")";
  (Sub e1 e2 [self:Print]).printAux = "(" ++ self.print ++ ")";
  (Mul e1 e2 [self:Print]).printAux = "(" ++ self.print ++ ")";
  (Div e1 e2 [self:Print]).printAux = "(" ++ self.print ++ ")";
  (Mod e1 e2 [self:Print]).printAux = "(" ++ self.print ++ ")";
  (Pow e1 e2 [self:Print]).printAux = "(" ++ self.print ++ ")";
};

p = new numPrintMutual ,, numPrintAux ,, numT @(Print & PrintAux);
-- p.zero.print


---------------
--  Boolean  --
---------------

type BoolSig<Boolean> = {
  True  : Boolean;
  False : Boolean;
  Not : Boolean -> Boolean;
  And : Boolean -> Boolean -> Boolean;
  Or  : Boolean -> Boolean -> Boolean,
  Xor : Boolean -> Boolean -> Boolean;
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

boolType = trait implements BoolSig<Type> => {
  (True).ty = "Bool";
  (False).ty = "Bool";
  (Not e).ty = "Bool";
  (And e1 e2).ty = "Bool";
  (Or e1 e2).ty = "Bool";
  (Xor e1 e2).ty = "Bool";
};

boolLog C = trait implements BoolSig<(EvalTopB C) & Print & Type % LogTop C> => {
  (True [self:Print & Type]).log (_:C) = self.print ++ " : " ++ self.ty;
  (False [self:Print & Type]).log (_:C) = self.print ++ " : " ++ self.ty;
  (Not e [self : (EvalTopB C) & Print & Type]).log (ctx:C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
  (And e1 e2 [self : (EvalTopB C) & Print & Type]).log (ctx:C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
  (Or e1 e2 [self : (EvalTopB C) & Print & Type]).log (ctx:C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
  (Xor e1 e2 [self : (EvalTopB C) & Print & Type]).log (ctx:C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
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

bool = new boolEval @Top ,, boolPrint' ,, boolType ,,
           boolLog @Top ,, boolCodegen ,,
           exprB @(EvalB & Print & Type & LogS & Codegen);
-- bool.binary.log ()


------------------
--  Comparison  --
------------------

type CmpSig<Boolean, Numeric> = {
  Eq : Numeric -> Numeric -> Boolean;
  Ne : Numeric -> Numeric -> Boolean;
  Lt : Numeric -> Numeric -> Boolean;
  Le : Numeric -> Numeric -> Boolean;
  Gt : Numeric -> Numeric -> Boolean;
  Ge : Numeric -> Numeric -> Boolean;
  Cmp : Numeric -> Numeric -> Numeric;
};

cmpEval C = trait implements CmpSig<EvalTopB C, EvalTopD C> => {
  (Eq e1 e2).eval (ctx:C) = e1.eval ctx == e2.eval ctx;
  (Ne e1 e2).eval (ctx:C) = e1.eval ctx != e2.eval ctx;
  (Lt e1 e2).eval (ctx:C) = e1.eval ctx < e2.eval ctx;
  (Le e1 e2).eval (ctx:C) = e1.eval ctx < e2.eval ctx ||
                            e1.eval ctx == e2.eval ctx;
  (Gt e1 e2).eval (ctx:C) = e1.eval ctx > e2.eval ctx;
  (Ge e1 e2).eval (ctx:C) = e1.eval ctx > e2.eval ctx ||
                            e1.eval ctx == e2.eval ctx;
  (Cmp e1 e2).eval (ctx:C) = let e1' = e1.eval ctx in
                             let e2' = e2.eval ctx in
                             if e1' == e2' then 0
                             else if e1' > e2' then 1
                             else 0 - 1;
};

cmpPrint = trait implements CmpSig<Print, Print> => {
  (Eq e1 e2).print = "(" ++ e1.print ++ " == " ++ e2.print ++ ")";
  (Ne e1 e2).print = "(" ++ e1.print ++ " != " ++ e2.print ++ ")";
  (Lt e1 e2).print = "(" ++ e1.print ++ " < " ++ e2.print ++ ")";
  (Le e1 e2).print = "(" ++ e1.print ++ " <= " ++ e2.print ++ ")";
  (Gt e1 e2).print = "(" ++ e1.print ++ " > " ++ e2.print ++ ")";
  (Ge e1 e2).print = "(" ++ e1.print ++ " >= " ++ e2.print ++ ")";
  (Cmp e1 e2).print = "(" ++ e1.print ++ " <=> " ++ e2.print ++ ")";
};

cmpType = trait implements CmpSig<Type, Type> => {
  (Eq e1 e2).ty = "Bool";
  (Ne e1 e2).ty = "Bool";
  (Lt e1 e2).ty = "Bool";
  (Le e1 e2).ty = "Bool";
  (Gt e1 e2).ty = "Bool";
  (Ge e1 e2).ty = "Bool";
  (Cmp e1 e2).ty = "Double";
};

cmpLog C = trait implements CmpSig<(EvalTopB C) & Print & Type % LogTop C,
                                   (EvalTopD C) & Print & Type % LogTop C> => {
  (Eq e1 e2 [self : (EvalTopB C) & Print & Type]).log (ctx:C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
  (Ne e1 e2 [self : (EvalTopB C) & Print & Type]).log (ctx:C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
  (Lt e1 e2 [self : (EvalTopB C) & Print & Type]).log (ctx:C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
  (Le e1 e2 [self : (EvalTopB C) & Print & Type]).log (ctx:C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
  (Gt e1 e2 [self : (EvalTopB C) & Print & Type]).log (ctx:C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
  (Ge e1 e2 [self : (EvalTopB C) & Print & Type]).log (ctx:C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
  (Cmp e1 e2 [self : (EvalTopD C) & Print & Type]).log (ctx:C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
};

cmpCodegen = trait implements CmpSig<Codegen, Codegen> => {
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
  (Cmp e1 e2).codegen = e1.codegen ++ e2.codegen ++ "dcmpg\n" ++
    "ifeq L1\nifge L2\nldc_w -1\ngoto L3\nL2: dconst_1\n" ++
    "goto L3\nL1: dconst_0\nL3: nop\n";
};

cmp N B = trait [self : NumSig<N> & BoolSig<B> & CmpSig<B, N>] => {
  neq = new Not (new Eq (new Lit 1) (new Lit 2));
  ltgt = new Or (new Lt (new Lit 3) (new Lit 4))
                (new Gt (new Lit 3) (new Lit 4));
  lege = new And (new Le (new Lit 5) (new Lit 6))
        (new And (new Ge (new Lit 6) (new Lit 5))
        (new And (new Le (new Lit 5) (new Lit 5))
                 (new Ge (new Lit 6) (new Lit 6))));
};

comp = new numEval @Top ,, boolEval @Top ,, cmpEval @Top ,,
           numPrint ,, boolPrint ,, cmpPrint ,,
           numType ,, boolType ,, cmpType ,,
           numLog @Top ,, boolLog @Top ,, cmpLog @Top ,,
           numCodegen ,, boolCodegen ,, cmpCodegen ,,
           cmp @(EvalD & Print & Type & LogS & Codegen)
               @(EvalB & Print & Type & LogS & Codegen);
-- comp.neq.log ()


--------------
--  Parity  --
--------------

type ParitySig<Boolean, Numeric> = {
  Odd  : Numeric -> Boolean;
  Even : Numeric -> Boolean;
};

parityEval C = trait implements ParitySig<EvalTopB C, EvalTopD C> => {
  (Odd e).eval (ctx:C) = mod (e.eval ctx) 2 == 1;
  (Even e).eval (ctx:C) = mod (e.eval ctx) 2 == 0;
};

parityPrint = trait implements ParitySig<Print, Print> => {
  (Odd e).print = "(" ++ e.print ++ " % 2 == 1)";
  (Even e).print = "(" ++ e.print ++ " % 2 == 0)";
};

parityPrint' = trait implements ParitySig<Print, Print> => {
  (Odd e).print = "(odd " ++ e.print ++ ")";
  (Even e).print = "(even " ++ e.print ++ ")";
};

parityType = trait implements ParitySig<Type, Top> => {
  (Odd e).ty = "Bool";
  (Even e).ty = "Bool";
};

parityLog C = trait implements
    ParitySig<(EvalTopB C) & Print & Type % LogTop C, Top> => {
  (Odd e [self : (EvalTopB C) & Print & Type]).log (ctx:C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
  (Even e [self : (EvalTopB C) & Print & Type]).log (ctx:C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
};

parityCodegen = trait implements ParitySig<Codegen, Codegen> => {
  (Odd e).codegen = e.codegen ++ "ldc_w 2\ndrem\ndconst_1\n" ++
    "ifeq L1\niconst_0\ngoto L2\nL1: iconst_1\nL2: nop\n";
  (Even e).codegen = e.codegen ++ "ldc_w 2\ndrem\ndconst_0\n" ++
    "ifeq L1\niconst_0\ngoto L2\nL1: iconst_1\nL2: nop\n";
};

parity N B = trait [self : NumSig<N> & BoolSig<B> & ParitySig<B, N>] => {
  truth = new And (new Odd (new Lit 11)) (new Even (new Lit 20))
};

oddeven = new numEval @Top ,, boolEval @Top ,, parityEval @Top ,,
              numPrint ,, boolPrint ,, parityPrint ,,
              numType ,, boolType ,, parityType ,,
              numLog @Top ,, boolLog @Top ,, parityLog @Top ,,
              numCodegen ,, boolCodegen ,, parityCodegen ,,
              parity @(EvalD & Print & Type & LogS & Codegen)
                     @(EvalB & Print & Type & LogS & Codegen);
-- oddeven.truth.log ()


-----------
-- Comma --
-----------

type CommaSig<Numeric> = {
  -- comma operator in C/C++
  Comma : Numeric -> Numeric -> Numeric;
};

commaEval C = trait implements CommaSig<EvalTopD C> => {
  (Comma e1 e2).eval (ctx:C) = e2.eval ctx;
};

commaPrint = trait implements CommaSig<Print> => {
  (Comma e1 e2).print = e1.print ++ ", " ++ e2.print;
};

commaType = trait implements CommaSig<Type> => {
  (Comma e1 e2).ty = "Double";
};

commaLog C = trait implements CommaSig<(EvalTopD C) & Print & Type % LogTop C> => {
  (Comma e1 e2 [self : (EvalTopD C) & Print & Type]).log (ctx:C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
};

commaCodegen = trait implements CommaSig<Codegen> => {
  (Comma e1 e2).codegen = e1.codegen ++ "pop\n" ++ e2.codegen;
};

comma N = trait [self : NumSig<N> & CommaSig<N>] => {
  seq = new Comma (new Lit 4) (new Lit 8);
};

seq = new numEval @Top ,, commaEval @Top ,,
          numPrint ,, commaPrint ,,
          numType ,, commaType ,,
          numLog @Top ,, commaLog @Top ,,
          numCodegen ,, commaCodegen ,,
          comma @(EvalD & Print & Type & LogS & Codegen);
-- seq.seq.log ()


--------------
--  Branch  --
--------------

type BranchSig<Boolean, Numeric> = {
  If     : Boolean -> Numeric -> Numeric -> Numeric;
  Unless : Boolean -> Numeric -> Numeric -> Numeric;
};

branchEval C = trait implements BranchSig<EvalTopB C, EvalTopD C> => {
  (If b e1 e2).eval (ctx:C) =
    if b.eval ctx then e1.eval ctx else e2.eval ctx;
  (Unless b e1 e2).eval (ctx:C) =
    if b.eval ctx then e2.eval ctx else e1.eval ctx;
};

branchPrint = trait implements BranchSig<Print, Print> => {
  (If b e1 e2).print = "(if " ++ b.print ++ " then " ++ e1.print ++
                       " else " ++ e2.print ++ ")";
  (Unless b e1 e2).print = "(unless " ++ b.print ++ " then " ++ e1.print ++
                           " else " ++ e2.print ++ ")";
};

branchPrint' = trait implements BranchSig<Print, Print> => {
  (If b e1 e2).print =
    "(" ++ b.print ++ " ? " ++ e1.print ++ " : " ++ e2.print ++ ")";
  (Unless b e1 e2).print =
    "(" ++ b.print ++ " ? " ++ e2.print ++ " : " ++ e1.print ++ ")";
};

branchType = trait implements BranchSig<Type, Top> => {
  (If b e1 e2).ty = "Double";
  (Unless b e1 e2).ty = "Double";
};

branchLog C = trait implements
    BranchSig<Top, (EvalTopD C) & Print & Type % LogTop C> => {
  (If b e1 e2 [self : (EvalTopD C) & Print & Type]).log (ctx:C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
  (Unless b e1 e2 [self : (EvalTopD C) & Print & Type]).log (ctx:C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
};

branchCodegen = trait implements BranchSig<Codegen, Codegen> => {
  (If b e1 e2).codegen = b.codegen ++ "ifeq L1\n" ++ e1.codegen ++
    "goto L2\nL1: " ++ e2.codegen ++ "L2: nop\n";
  (Unless b e1 e2).codegen = b.codegen ++ "ifne L1\n" ++ e1.codegen ++
    "goto L2\nL1: " ++ e2.codegen ++ "L2: nop\n";
};

branch N B = trait
    [self : NumSig<N> & BoolSig<B> & CmpSig<B, N> & BranchSig<B, N>] => {
  branch = new If (new And (new Eq (new Lit 1.1) (new Lit 1.1))
                           (new Not (new True)))
           (new Div (new Lit 0) (new Lit 0))
           (new If (new Lt (new Lit 4) (new Lit 8))
                   (new Pow (new Add (new Lit 1) (new Lit 1))
                            (new Mul (new Lit 2) (new Lit 5)))
                   (new Neg (new Lit 42)));
};

expr = new numEval @Top ,, boolEval @Top ,, cmpEval @Top ,, branchEval @Top ,,
           numPrint ,, boolPrint ,, cmpPrint ,, branchPrint ,,
           numType ,, boolType ,, cmpType ,, branchType ,,
           numLog @Top ,, boolLog @Top ,, cmpLog @Top ,, branchLog @Top ,,
           numCodegen ,, boolCodegen ,, cmpCodegen ,, branchCodegen ,,
           branch @(EvalD & Print & Type & LogS & Codegen)
                  @(EvalB & Print & Type & LogS & Codegen);
-- expr.branch.log ()


------------
--  Sign  --
------------

type SignSig<Boolean, Numeric> = {
  IsZero : Numeric -> Boolean;
  Positive : Numeric -> Boolean;
  Negative : Numeric -> Boolean;
  NonPositive : Numeric -> Boolean;
  NonNegative : Numeric -> Boolean;
  Sgn : Numeric -> Numeric;
};

signEval C = trait implements SignSig<EvalTopB C, EvalTopD C> => {
  (IsZero e).eval (ctx:C) = e.eval ctx == 0;
  (Positive e).eval (ctx:C) = e.eval ctx > 0;
  (Negative e).eval (ctx:C) = e.eval ctx < 0;
  (NonPositive e).eval (ctx:C) = e.eval ctx < 0 || e.eval ctx == 0;
  (NonNegative e).eval (ctx:C) = e.eval ctx > 0 || e.eval ctx == 0;
  (Sgn e).eval (ctx:C) = let e' = e.eval ctx in
    if e' == 0 then 0 else if e' > 0 then 1 else 0 - 1;
};

signPrint = trait implements SignSig<Print, Print> => {
  (IsZero e).print = "(" ++ e.print ++ " == 0)";
  (Positive e).print = "(" ++ e.print ++ " > 0)";
  (Negative e).print = "(" ++ e.print ++ " < 0)";
  (NonPositive e).print = "(" ++ e.print ++ " <= 0)";
  (NonNegative e).print = "(" ++ e.print ++ " >= 0)";
  (Sgn e).print = "(" ++ e.print ++ " <=> 0)";
};

signPrint' = trait implements SignSig<Print, Print> => {
  (IsZero e).print = "(zero? " ++ e.print ++ ")";
  (Positive e).print = "(pos? " ++ e.print ++ ")";
  (Negative e).print = "(neg? " ++ e.print ++ ")";
  (NonPositive e).print = "(nonpos? " ++ e.print ++ ")";
  (NonNegative e).print = "(nonneg? " ++ e.print ++ ")";
  (Sgn e).print = "(sgn " ++ e.print ++ ")";
};

signType = trait implements SignSig<Type, Type> => {
  (IsZero e).ty = "Bool";
  (Positive e).ty = "Bool";
  (Negative e).ty = "Bool";
  (NonPositive e).ty = "Bool";
  (NonNegative e).ty = "Bool";
  (Sgn e).ty = "Double";
};

signLog C = trait implements SignSig<(EvalTopB C) & Print & Type % LogTop C,
                                     (EvalTopD C) & Print & Type % LogTop C> => {
  (IsZero e [self : (EvalTopB C) & Print & Type]).log (ctx:C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
  (Positive e [self : (EvalTopB C) & Print & Type]).log (ctx:C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
  (Negative e [self : (EvalTopB C) & Print & Type]).log (ctx:C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
  (NonPositive e [self : (EvalTopB C) & Print & Type]).log (ctx:C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
  (NonNegative e [self : (EvalTopB C) & Print & Type]).log (ctx:C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
  (Sgn e [self : (EvalTopD C) & Print & Type]).log (ctx:C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
};

signCodegen = trait implements SignSig<Codegen, Codegen> => {
  (IsZero e).codegen = e.codegen ++ "dconst_0\ndcmpg\n" ++
    "ifeq L1\niconst_0\ngoto L2\nL1: iconst_1\nL2: nop\n";
  (Positive e).codegen = e.codegen ++ "dconst_0\ndcmpg\n" ++
    "ifgt L1\niconst_0\ngoto L2\nL1: iconst_1\nL2: nop\n";
  (Negative e).codegen = e.codegen ++ "dconst_0\ndcmpg\n" ++
    "iflt L1\niconst_0\ngoto L2\nL1: iconst_1\nL2: nop\n";
  (NonPositive e).codegen = e.codegen ++ "dconst_0\ndcmpg\n" ++
    "ifle L1\niconst_0\ngoto L2\nL1: iconst_1\nL2: nop\n";
  (NonNegative e).codegen = e.codegen ++ "dconst_0\ndcmpg\n" ++
    "ifge L1\niconst_0\ngoto L2\nL1: iconst_1\nL2: nop\n";
  (Sgn e).codegen = e.codegen ++ "dconst_0\ndcmpg\n" ++
    "ifeq L1\nifge L2\nldc_w -1\ngoto L3\nL2: dconst_1\n" ++
    "goto L3\nL1: dconst_0\nL3: nop\n";
};

type SignBranchSig<Numeric> = {
  -- three branches for <, =, > compared with zero
  SignBranch : Numeric -> Numeric -> Numeric -> Numeric -> Numeric;
};

signBranchEval C = trait implements SignBranchSig<EvalTopD C> => {
  (SignBranch n lt eq gt).eval (ctx:C) =
    if n.eval ctx < 0 then lt.eval ctx
    else if n.eval ctx == 0 then eq.eval ctx
    else gt.eval ctx;
};

signBranchPrint = trait implements SignBranchSig<Print> => {
  (SignBranch n lt eq gt).print =
    "if " ++ n.print ++ " < 0 then " ++ lt.print ++ "\n" ++
    "else if " ++ n.print ++ " == 0 then " ++ eq.print ++ "\n" ++
    "else " ++ gt.print ++ "\n";
};

signBranchPrint' = trait implements SignBranchSig<Print> => {
  (SignBranch n lt eq gt).print = "case " ++ n.print ++ " of\n" ++
                                  "(<0) -> " ++ lt.print ++ "\n" ++
                                  "(=0) -> " ++ eq.print ++ "\n" ++
                                  "(>0) -> " ++ gt.print ++ "\n";
};

signBranchType = trait implements SignBranchSig<Type> => {
  (SignBranch n lt eq gt).ty = "Double";
};

signBranchLog C = trait implements
    SignBranchSig<(EvalTopD C) & Print & Type % LogTop C> => {
  (SignBranch n lt eq gt [self : (EvalTopD C) & Print & Type]).log (ctx:C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
};

signBranchCodegen = trait implements SignBranchSig<Codegen> => {
  (SignBranch n lt eq gt).codegen = n.codegen ++ "ifge L1\n" ++
    lt.codegen ++ "goto L3\nL1: ifgt L2\n" ++ eq.codegen ++
    "goto L3\nL2: " ++ gt.codegen ++ "L3: nop\n";
};

sign N B = trait
    [self : NumSig<N> & BoolSig<B> & SignSig<B, N> & SignBranchSig<N>] => {
  posneg = new And (new Positive (new Lit 1)) (new Negative (new Lit (0-1)));
  zero = new And (new IsZero (new Lit 0))
        (new And (new NonPositive (new Lit 0))
                 (new NonNegative (new Lit 0)));
  sgn = new Add (new Sgn (new Lit 16)) (new Sgn (new Lit (0-1)));
  branch = new SignBranch (new Lit 0) (new Lit 1) (new Lit 2) (new Lit 3);
};

sgn = new numEval @Top ,, boolEval @Top ,, signEval @Top ,, signBranchEval @Top ,,
          numPrint ,, boolPrint ,, signPrint ,, signBranchPrint ,,
          numType ,, boolType ,, signType ,, signBranchType ,,
          numLog @Top ,, boolLog @Top ,, signLog @Top ,, signBranchLog @Top ,,
          numCodegen ,, boolCodegen ,, signCodegen ,, signBranchCodegen ,,
          sign @(EvalD & Print & Type & LogS & Codegen)
               @(EvalB & Print & Type & LogS & Codegen);
-- sgn.branch.log ()


----------------
--  Variable  --
----------------

type VarSig<Numeric> = {
  Let : String -> Numeric -> Numeric -> Numeric;
  Var : String -> Numeric;
};

varEval (C * EnvD) = trait implements VarSig<EvalEnvD C> => {
  (Let name e1 e2).eval (ctx:EnvD&C) =
    e2.eval ({ env = insert @Double name (e1.eval ctx) ctx.env } ,, ctx : C);
  (Var name).eval (ctx:EnvD&C) = lookup @Double name ctx.env;
};

varPrint = trait implements VarSig<Print> => {
  (Let name e1 e2).print =
    "let $" ++ name ++ " = " ++ e1.print ++ " in " ++ e2.print;
  (Var name).print = "$" ++ name;
};

varType = trait implements VarSig<Type> => {
  (Let name e1 e2).ty = "Double";
  (Var name).ty = "Double";
};

varLog C = trait implements VarSig<(EvalEnvD C) & Print & Type % LogEnv C> => {
  (Let name e1 e2 [self : (EvalEnvD C) & Print & Type]).log (ctx:EnvD&C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
  (Var name [self : (EvalEnvD C) & Print & Type]).log (ctx:EnvD&C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
};

varCodegen = trait implements VarSig<Codegen> => {
  (Let name e1 e2).codegen =
    e1.codegen ++ "dstore " ++ name ++ "\n" ++ e2.codegen;
  (Var name).codegen = "dload " ++ name ++ "\n";
};

var N = trait [self : NumSig<N> & VarSig<N>] => {
  decl = new Let "x" (new Add (new Lit 1) (new Lit 1))
                 (new Pow (new Var "x") (new Lit 10));
};

decl = new numEval @EnvD ,, varEval @Top ,,
           numPrint ,, varPrint ,,
           numType ,, varType ,,
           numLog @EnvD ,, varLog @Top ,,
           numCodegen ,, varCodegen ,,
           var @(EvalEnvD Top & Print & Type & LogEnv Top & Codegen);
-- decl.decl.log eD


----------------------------
-- Dynamic Scoped Closure --
----------------------------

type Closure Expr = {
  param : String;
  body  : Expr;
  env   : Env Double;
};

type ClosExprSig<Numeric> = {
  DynLet : String -> Numeric -> Numeric -> Numeric;
  DynApp : Closure Numeric -> Numeric -> Numeric;
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
  (DynLet name e1 e2).print =
    "dynlet $" ++ name ++ " = " ++ e1.print ++ " in " ++ e2.print;
  (DynApp clos e).print =
    "dynapp (\\" ++ clos.param ++ " -> " ++ clos.body.print ++ ") " ++ e.print;
};

closType = trait implements ClosExprSig<Type> => {
  (DynLet name e1 e2).ty = "Double";
  (DynApp clos e).ty = "Double";
};

closLog C = trait implements
    ClosExprSig<(EvalEnvDEnvD C) & Print & Type % LogEnvDEnv C> => {
  (DynLet name e1 e2 [self : (EvalEnvDEnvD C) & Print & Type]).log (ctx:EnvD&DEnvD&C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
  (DynApp clos e [self : (EvalEnvDEnvD C) & Print & Type]).log (ctx:EnvD&DEnvD&C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
};

clos N = trait [self : NumSig<N> & VarSig<N> & ClosExprSig<N>] => {
  dynlet =
    let clos = { param = "x",
                 body = new Add (new Var "x") (new Var "a"),
                 env (s:String) = if s == "a" then 1 else undefined : Double }
    in new DynLet "a" (new Lit 2) (new DynApp clos (new Lit 10));
};

dyn = new numEval @(EnvD&DEnvD) ,, varEval @DEnvD ,, closEval @Top ,,
          numPrint ,, varPrint ,, closPrint ,,
          numType ,, varType ,, closType ,,
          numLog @(EnvD&DEnvD) ,, varLog @DEnvD ,, closLog @Top ,,
          clos @(EvalEnvDEnvD Top & Print & Type & LogEnvDEnv Top);
-- dyn.dynlet.log eD


----------------------
-- Builtin Function --
----------------------

type Func = Double -> Double;
type EnvF = { fn : Env Func };
type EvalEnvF C = Eval (EnvF&C) Double;
type LogEnvF C = LogTop (EnvF&C);

type FuncSig<Numeric> = {
  LetF : String -> Func -> Numeric -> Numeric;
  AppF : String -> Numeric -> Numeric;
};

funcEval (C * EnvF) = trait implements FuncSig<EvalEnvF C> => {
  (LetF name f e).eval (ctx:EnvF&C) =
    e.eval ({ fn = insert @Func name f ctx.fn } ,, ctx : C);
  (AppF name e).eval (ctx:EnvF&C) =
    (lookup @Func name ctx.fn) (e.eval ctx);
};

funcPrint = trait implements FuncSig<Print> => {
  (LetF name f e).print =
    "letf $" ++ name ++ " = " ++ f.toString ++ " in " ++ e.print;
  (AppF name e).print = "appf $" ++ name ++ " " ++ e.print;
};

funcType = trait implements FuncSig<Type> => {
  (LetF name f e).ty = "Double";
  (AppF name e).ty = "Double";
};

funcLog C = trait implements FuncSig<(EvalEnvF C) & Print & Type % LogEnvF C> => {
  (LetF name f e [self : (EvalEnvF C) & Print & Type]).log (ctx:EnvF&C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
  (AppF name e [self : (EvalEnvF C) & Print & Type]).log (ctx:EnvF&C) =
    self.print ++ " : " ++ self.ty ++ " = " ++ (self.eval ctx).toString;
};

func N = trait [self : NumSig<N> & VarSig<N> & FuncSig<N>] => {
  app = new LetF "f" (\(x:Int) -> x * x)
                 (new Let "x" (new Lit 9) (new AppF "f" (new Var "x")));
};

expr = new numEval @(EnvD&EnvF) ,, varEval @EnvF ,, funcEval @EnvD ,,
           numPrint ,, varPrint ,, funcPrint ,,
           numType ,, varType ,, funcType ,,
           numLog @(EnvD&EnvF) ,, varLog @EnvF ,, funcLog @EnvD ,,
           func @(EvalEnvD EnvF & Print & Type & LogEnv EnvF);
expr.app.log { env = empty @Double, fn = empty @Func }
