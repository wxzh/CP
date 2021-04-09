--> "((3){2}+(4){3}){1}"

type PreExprSig In Out = {
  Lit : Int -> Out,
  Add : In -> In -> Out
};

type ExprSig E = PreExprSig E E;
type CtxExprSig E Ctx Out = PreExprSig E (Ctx -> Out);

type PreInhSig In Out = {
  Add1 : Out,
  Add2 : In -> Out
};

type InhSig E = PreInhSig E E;
type CtxInhSig E Ctx Out = PreInhSig E (Ctx -> Out);

exprAssemble Ctx (Out * Ctx) (alg1 : CtxExprSig (Ctx & Out) Ctx Out)
                             (alg2 : CtxInhSig (Ctx & Out) Ctx Ctx) =
    trait implements ExprSig (Ctx -> Ctx & Out) => {
  Lit n = \(ctx : Ctx) -> ctx ,, alg1.Lit n ctx;
  Add (e1 : Ctx -> Ctx & Out) (e2 : Ctx -> Ctx & Out) =
    \(ctx : Ctx) -> let out1 = e1 (alg2.Add1 ctx) in
                    let out2 = e2 (alg2.Add2 out1 ctx) in
                    ctx ,, alg1.Add out1 out2 ctx;
};

type HasCount = { count : Int };

exprCount = trait implements CtxExprSig HasCount Top HasCount => {
  Lit n = \(ctx:Top) ->
    { count = 1 };
  Add e1 e2 = \(ctx:Top) ->
    { count = e1.count + e2.count + 1 };
};

type HasPos = { pos : Int };

exprPos = trait implements CtxInhSig HasCount HasPos HasPos => {
  Add1 = \(ctx:HasPos) ->
    -- e1.pos = e0.pos + 1
    { pos = ctx.pos + 1 };
  Add2 (e1:HasCount) = \(ctx:HasPos) ->
    -- e2.pos = e0.pos + e1.count + 1
    { pos = ctx.pos + e1.count + 1 };
};

type HasPP = { pp : String };

exprPP = trait implements CtxExprSig HasPP HasPos HasPP => {
  Lit n = \(ctx:HasPos) ->
    { pp = "(" ++ n.toString ++ "){" ++ ctx.pos.toString ++ "}" };
  Add e1 e2 = \(ctx:HasPos) ->
    { pp = "(" ++ e1.pp ++ "+" ++ e2.pp ++ "){" ++ ctx.pos.toString ++ "}" };
};


expr T = trait [self : ExprSig T] => {
  seven = Add (Lit 3) (Lit 4);
};

assembled = exprAssemble @HasPos @(HasCount & HasPP) (new exprCount ,, exprPP) (new exprPos);
((new assembled ,, expr @(HasPos -> HasPos & HasCount & HasPP)).seven { pos = 1 }).pp
