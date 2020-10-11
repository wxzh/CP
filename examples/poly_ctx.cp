--> 81.0

type Env T = String -> T;
type EnvD = Env Double;
type Func = Double -> Double;
type EnvF = Env Func;

empty T = \(_ : String) -> undefined : T;
lookup T (s : String) (env : Env T) = env s;
insert T (s : String) (v : T) (env : Env T) =
  \(s': String) -> if s == s' then v else lookup @T s' env;

type ExpSig<Exp> = {
  Lit : Double -> Exp;
  Add : Exp -> Exp -> Exp;
};

type VarSig<Exp> = {
  Let : String -> Exp -> Exp -> Exp;
  Var : String -> Exp;
};

type FuncSig<Exp> = {
  LetF : String -> Func -> Exp -> Exp;
  AppF : String -> Exp -> Exp;
};

-- BEGIN_CNT
type Cnt = { cnt : Int };
expCnt = trait implements ExpSig<Cnt> => {
  (Lit     n).cnt = 1;
  (Add e1 e2).cnt = e1.cnt + e2.cnt + 1;
};
-- END_CNT

-- BEGIN_POS
type Pos = { pos : Int };
type InhPos = { pos1 : Pos -> Int; pos2 : Pos -> Cnt -> Int };
type PrintPos Ctx = { print : Pos&Ctx -> String };
printPos (Ctx * Pos) = trait [self : InhPos] implements ExpSig<Cnt % PrintPos Ctx> => {
  (Lit     n).print (inh:Pos&Ctx) = "{" ++ inh.pos.toString ++ "}";
  (Add e1 e2).print (inh:Pos&Ctx) =
    "(" ++ e1.print ({ pos = pos1 inh } ,, inh:Ctx) ++ "+" ++
           e2.print ({ pos = pos2 inh e1 } ,, inh:Ctx) ++ ")";
  pos1 (e0:Pos) = e0.pos + 1;                    -- e1.pos = e0.pos + 1
  pos2 (e0:Pos) (e1:Cnt) = e0.pos + e1.cnt + 1;  -- e2.pos = e0.pos + e1.cnt + 1
};
-- END_POS

{-
-- BEGIN_LATTR
exp Exp = trait [self : ExpSig<Exp>] => {
  test = new Add (new Add (new Lit 1) (new Lit 2)) (new Add (new Lit 3) (new Lit 4));
};
e = new expCnt ,, printPos @Top ,, exp @(Cnt & PrintPos Top);
e.test.print { pos = 0 }  --> (({2}+{3})+({5}+{6}))
-- END_LATTR
-}

-- BEGIN_VARIABLE_BINDING
type Eval = { eval : EnvD -> Double };
evalNum = trait implements ExpSig<Eval> => {
  (Lit     n).eval (env:EnvD) = n;
  (Add e1 e2).eval (env:EnvD) = e1.eval env + e2.eval env;
};
evalVar = trait implements VarSig<Eval> => {
  (Let s e1 e2).eval (env:EnvD) = e2.eval (insert @Double s (e1.eval env) env);
  (Var       s).eval (env:EnvD) = lookup @Double s env;
};
-- END_VARIABLE_BINDING

-- BEGIN_INTRINSIC_FUNCTIONS
type Eval = { eval : EnvD -> EnvF -> Double };
evalNum = trait implements ExpSig<Eval> => {
  (Lit     n).eval (envD:EnvD) (envF:EnvF) = n;
  (Add e1 e2).eval (envD:EnvD) (envF:EnvF) = e1.eval envD envF + e2.eval envD envF;
};
evalVar = trait implements VarSig<Eval> => {
  (Let s e1 e2).eval (envD:EnvD) (envF:EnvF) =
    e2.eval (insert @Double s (e1.eval envD envF) envD) envF;
  (Var       s).eval (envD:EnvD) (envF:EnvF) = lookup @Double s envD;
};
evalFunc = trait implements FuncSig<Eval> => {
  (LetF s f e).eval (envD:EnvD) (envF:EnvF) = e.eval envD (insert @Func s f envF);
  (AppF  s  e).eval (envD:EnvD) (envF:EnvF) = (lookup @Func s envF) (e.eval envD envF);
};
-- END_INTRINSIC_FUNCTIONS

-- BEGIN_EVAL_CTX
type Eval Context = { eval : Context -> Double };
-- END_EVAL_CTX

-- BEGIN_POLY_EVAL
evalNum Context = trait implements ExpSig<Eval Context> => {
  (Lit     n).eval (ctx:Context) = n;
  (Add e1 e2).eval (ctx:Context) = e1.eval ctx + e2.eval ctx;
};
-- END_POLY_EVAL

expAdd Exp = trait [self : ExpSig<Exp>] => {
  add = new Add (new Lit 4) (new Lit 8);
};

{-
-- BEGIN_EVAL_ADD
(new evalNum @Top ,, expAdd @(Eval Top)).add.eval ()  --> 12.0
-- END_EVAL_ADD
-}

-- BEGIN_CTXD
type CtxD = { envD : EnvD };
-- END_CTXD

-- BEGIN_EVAL_VAR
evalVar (Context * CtxD) = trait implements VarSig<Eval (CtxD&Context)> => {
  (Let s e1 e2).eval (ctx:CtxD&Context) =
    e2.eval ({ envD = insert @Double s (e1.eval ctx) ctx.envD } ,, ctx:Context);
  (Var       s).eval (ctx:CtxD&Context) = lookup @Double s ctx.envD;
};
-- END_EVAL_VAR

-- BEGIN_EVAL_FUNC
type CtxF = { envF : EnvF };
evalFunc (Context * CtxF) = trait implements FuncSig<Eval (CtxF&Context)> => {
  (LetF s f e).eval (ctx:CtxF&Context) =
    e.eval ({ envF = insert @Func s f ctx.envF } ,, ctx:Context);
  (AppF  s  e).eval (ctx:CtxF&Context) = (lookup @Func s ctx.envF) (e.eval ctx);
};
-- END_EVAL_FUNC

-- BEGIN_POLY_MERGE
expPoly Exp = trait [self : ExpSig<Exp> & VarSig<Exp> & FuncSig<Exp>] => {
  test = new LetF "f" (\(x:Double) -> x * x)
                 (new Let "x" (new Lit 9) (new AppF "f" (new Var "x")));
};
e = new evalNum @(CtxD&CtxF) ,, evalVar @CtxF ,, evalFunc @CtxD ,,
        expPoly @(Eval (CtxD & CtxF));
e.test.eval { envD = empty @Double, envF = empty @Func }  --> 81.0
-- END_POLY_MERGE
