-----------
-- Maybe --
-----------

type Maybe<M> A = {
  Nothing : M;
  Just : A -> M;
};

type Fold A = { fold : forall B. B -> (A -> B) -> B };

foldMaybe A = trait implements Maybe<Fold A> A => {
  (Nothing).fold B (x:B) (f:A->B) = x;
  (Just  v).fold B (x:B) (f:A->B) = f v;
};

type Map = String -> Fold Int;
empty = \(_:String) -> new (new foldMaybe @Int).Nothing;
just (x:Int) = new (new foldMaybe @Int).Just x;

----------------
-- Attributes --
----------------

-- inh --
type HasFunctions = { functions : Map };
type HasVariables = { variables : Map };
type HasOffset = { offset : Int };

-- syn --
type HasCount = { count : Int };
type HasCode C = { code : C -> String };
type ChainedFunctions C = { functions : HasFunctions & C -> Map };
type ChainedVariables C = { variables : HasVariables & C -> Map };
type HasPP = { pp : String };

--------------
-- Bytecode --
--------------

prelude = ".method mul_\n.args 3\n.locals 2\nbipush 1\nistore 4\nbipush 0\n"
  ++ "iload 1\nisub\niflt mul0\nbipush 0\niload 1\nisub\nistore 1\nbipush 0\n"
  ++ "istore 4\nmul0:\nbipush 0\nistore 3\nmul1:\niload 1\nifeq mul2\niload 1\n"
  ++ "bipush 1\nisub\nistore 1\niload 3\niload 2\niadd\nistore 3\ngoto mul1\n"
  ++ "mul2:\nbipush 1\niload 4\nisub\nifeq mul3\nbipush 0\niload 3\nisub\n"
  ++ "istore 3\nmul3:\niload 3\nireturn\n\n.method div_\n.args 3\n.locals 2\n"
  ++ "bipush 1\nistore 4\nbipush 0\niload 1\nisub\niflt div0\nbipush 0\niload 1\n"
  ++ "isub\nistore 1\nbipush 0\nistore 4\ndiv0:\nbipush 0\niload 2\nisub\niflt div1\n"
  ++ "bipush 0\niload 2\nisub\nistore 2\niload 4\nbipush 1\niadd\nistore 4\ndiv1:\n"
  ++ "bipush 0\nistore 3\ndiv2:\niload 1\niload 2\nisub\niflt div3\niload 1\n"
  ++ "iload 2\nisub\nistore 1\niload 3\nbipush 1\niadd\nistore 3\ngoto div2\ndiv3:\n"
  ++ "bipush 0\niload 4\nisub\niflt div4\nbipush 0\niload 3\nisub\nistore 3\ndiv4:\n"
  ++ "iload 3\nireturn\n\n.method mod_\n.args 3\n.locals 1\nbipush 44\niload 1\n"
  ++ "iload 2\ninvokevirtual div_\nistore 3\niload 1\nbipush 44\niload 3\niload 2\n"
  ++ "invokevirtual mul_\nisub\nireturn\n\n.method not_\n.args 2\niload 1\nifeq not1\n"
  ++ "bipush 0\ngoto not0\nnot1:\nbipush 1\nnot0:\n\n.method eq_\n.args 3\niload 1\n"
  ++ "iload 2\nisub\nifeq eq1\nbipush 0\nireturn\neq1:\nbipush 1\nireturn\n\n"
  ++ ".method ne_\n.args 3\niload 1\niload 2\nisub\nifeq ne0\nbipush 1\nireturn\n"
  ++ "ne0:\nbipush 0\nireturn\n\n.method lt_\n.args 3\niload 1\niload 2\nisub\n"
  ++ "iflt lt1\nbipush 0\nireturn\nlt1:\nbipush 1\nireturn\n\n.method gt_\n.args 3\n"
  ++ "iload 1\niload 2\nisub\niflt gt0\nbipush 1\nireturn\ngt0:\nbipush 0\nireturn\n"
  ++ "\n.method leq_\n.args 3\niload 1\niload 2\nisub\ndup\nifeq leqpop1\niflt leq1\n"
  ++ "bipush 0\nireturn\nleq1:\nbipush 1\nireturn\nleqpop1:\npop\nbipush 1\nireturn\n"
  ++ "\n.method geq_\n.args 3\niload 1\niload 2\nisub\ndup\nifeq geqpop1\niflt geq0\n"
  ++ "bipush 1\nireturn\ngeq0:\nbipush 0\nireturn\ngeqpop1:\npop\nbipush 1\nireturn\n";

error = undefined : String;

----------
-- List --
----------

type LstSig<Lst, Elm> = {
  LstEmpty : Lst;
  LstCons : Elm -> Lst -> Lst;
};

lstCode (C * HasOffset) = trait implements LstSig<HasCode (HasOffset & C), HasCode (HasOffset & C)> => {
  (LstEmpty).code (_:HasOffset&C) = "";
  (LstCons head tail).code (inh:HasOffset&C) = head.code inh ++
    tail.code ({ offset = inh.offset + 1 } ,, inh : C);
};

lstCount = trait implements LstSig<HasCount, Top> => {
  (LstEmpty).count = 0;
  (LstCons head tail).count = tail.count + 1;
};

lstFunctions (C * HasFunctions) = trait implements LstSig<ChainedFunctions C, ChainedFunctions C> => {
  (LstEmpty).functions (inh:HasFunctions&C) = inh.functions;
  (LstCons head tail).functions (inh:HasFunctions&C) =
    let h = head.functions inh in
    tail.functions ({ functions = h } ,, inh : C);
};

lstVariables (C * HasVariables & HasOffset) = trait implements LstSig<ChainedVariables (HasOffset & C), ChainedVariables (HasOffset & C)> => {
  (LstEmpty).variables (inh:HasOffset&HasVariables&C) = inh.variables;
  (LstCons head tail).variables (inh:HasOffset&HasVariables&C) =
    let h = head.variables inh in
    tail.variables ({ offset = inh.offset + 1, variables = h } ,, inh : C);
};

lstPP = trait implements LstSig<HasPP, HasPP> => {
  (LstEmpty).pp = "";
  (LstCons head tail).pp = if tail.pp == "" then head.pp
                           else head.pp ++ " " ++ tail.pp;
};

-------------
-- Program --
-------------

type ProgSig<Program, Fun> = {
  Prog : Fun -> Fun -> Program;
};

programCode (C * HasFunctions) = trait implements ProgSig<HasCode (HasFunctions & C), ChainedFunctions Top & HasCode (HasFunctions & C)> => {
  (Prog fdecls fdefs).code (inh:HasFunctions&C) = prelude ++ fdecls.code inh ++
    fdefs.code ({ functions = fdecls.functions inh } ,, inh : C);
};

programCount = trait implements ProgSig<HasCount, Top> => {
  (Prog fdecls fdefs).count = undefined : Int;
};

programFunctions (C * HasFunctions) = trait implements ProgSig<ChainedFunctions C, Top> => {
  (Prog fdecls fdefs).functions (inh:HasFunctions&C) = inh.functions;
};

programVariables (C * HasVariables) = trait implements ProgSig<ChainedVariables C, Top> => {
  (Prog fdecls fdefs).variables (inh:HasVariables&C) = inh.variables;
};

programPP = trait implements ProgSig<HasPP, HasPP> => {
  (Prog fdecls fdefs).pp = fdecls.pp ++ fdefs.pp;
};

--------------
-- Function --
--------------

type FunSig<Fun, Lst> = {
  FunDecl : String -> Lst -> Fun;
  FunDef : String -> Lst -> Lst -> Lst -> Fun;
};

functionCode (C * HasOffset & HasVariables) = trait implements FunSig<ChainedVariables HasOffset % HasCode (HasOffset & HasVariables & C), HasCount & HasCode (HasOffset & HasVariables & C)> => {
  (FunDecl id params).code (_:HasOffset&HasVariables&C) = "";
  (FunDef id params decls stmts [self:ChainedVariables HasOffset]).code (inh:HasOffset&HasVariables&C) =
    let ctx = { offset = inh.offset + params.count,
                variables = self.variables inh } ,, inh : C in
    let declsCode = decls.code ctx in
    let stmtsCode = stmts.code ctx in
    let locals = if decls.count > 0
        then ".locals " ++ decls.count.toString ++ "\n" else "" in
    ".method " ++ id ++ "\n.args " ++ (params.count + 1).toString ++ "\n" ++
    locals ++ declsCode ++ stmtsCode ++ "bipush 0\nireturn\n";
};

functionCount = trait implements FunSig<HasCount, Top> => {
  (FunDecl id params).count = undefined : Int;
  (FunDef id params decls stmts).count = undefined : Int;
};

functionFunctions (C * HasFunctions) = trait implements FunSig<ChainedFunctions C, HasCount> => {
  (FunDecl id params).functions (inh:HasFunctions&C) = \(name:String) ->
    if name == id then just params.count else inh.functions name;
  (FunDef id params decls stmts).functions (inh:HasFunctions&C) = inh.functions;
};

functionVariables (C * HasVariables & HasOffset) = trait implements FunSig<ChainedVariables (HasOffset & C), HasCount & ChainedVariables (HasOffset & C)> => {
  (FunDecl id params).variables (inh:HasOffset&HasVariables&C) = inh.variables;
  (FunDef id params decls stmts).variables (inh:HasOffset&HasVariables&C) =
    let p = params.variables inh in
    let d = decls.variables ({ offset = inh.offset + params.count, variables = p } ,, inh : C) in
    stmts.variables ({ offset = inh.offset + params.count, variables = d } ,, inh : C);
};

functionPP = trait implements FunSig<HasPP, HasPP> => {
  (FunDecl id params).pp = "function " ++ id ++ "(" ++ params.pp ++ ");\n";
  (FunDef id params decls stmts).pp = "function " ++ id ++
    "(" ++ params.pp ++ ") {\n" ++ decls.pp ++ stmts.pp ++ "}\n";
};

---------------
-- Parameter --
---------------

type ParamSig<Parameter> = {
  Param : String -> Parameter;
};

parameterCode C = trait implements ParamSig<HasCode C> => {
  (Param id).code (_:C) = "";
};

parameterCount = trait implements ParamSig<HasCount> => {
  (Param id).count = 1;
};

parameterFunctions (C * HasFunctions) = trait implements ParamSig<ChainedFunctions C> => {
  (Param id).functions (inh:HasFunctions&C) = inh.functions;
};

parameterVariables (C * HasVariables & HasOffset) = trait implements ParamSig<ChainedVariables (HasOffset & C)> => {
  (Param id).variables (inh:HasOffset&HasVariables&C) = \(name:String) ->
    if name == id then just inh.offset else inh.variables name;
};

parameterPP = trait implements ParamSig<HasPP> => {
  (Param id).pp = id;
};

-----------------
-- Declaration --
-----------------

type DeclSig<Decl> = {
  IntDecl : String -> Int -> Decl;
};

declarationCode (C * HasOffset) = trait implements DeclSig<HasCode (HasOffset & C)> => {
  (IntDecl id init).code (inh:HasOffset&C) =
    "bipush " ++ init.toString ++ "\nistore " ++ inh.offset.toString ++ "\n";
};

declarationCount = trait implements DeclSig<HasCount> => {
  (IntDecl id init).count = 1;
};

declarationFunctions (C * HasFunctions) = trait implements DeclSig<ChainedFunctions C> => {
  (IntDecl id init).functions (inh:HasFunctions&C) = inh.functions;
};

declarationVariables (C * HasVariables & HasOffset) = trait implements DeclSig<ChainedVariables (HasOffset & C)> => {
  (IntDecl id init).variables (inh:HasOffset&HasVariables&C) = \(name:String) ->
    if name == id then just inh.offset else inh.variables name;
};

declarationPP = trait implements DeclSig<HasPP> => {
  (IntDecl id init).pp = "var " ++ id ++ " = " ++ init.toString ++ ";\n";
};

---------------
-- Statement --
---------------

type StmtSig<Stmt, Expr, Lst> = {
  AssignStmt : String -> Expr -> Stmt;
  WhileStmt : Expr -> Lst -> Stmt;
  IfStmt : Expr -> Lst -> Lst -> Stmt;
  PutCharStmt : Expr -> Stmt;
  ReturnStmt : Expr -> Stmt;
};

statementCode (C * HasVariables) = trait implements StmtSig<HasCode (HasVariables & C), HasCode (HasVariables & C), HasCode (HasVariables & C)> => {
  (AssignStmt id value).code (inh:HasVariables&C) = let addr = inh.variables id in
    addr.fold @String error (\(addr:Int) ->
      value.code inh ++ "istore " ++ addr.toString ++ "\n");
  (WhileStmt cond body).code (inh:HasVariables&C) =
    "LabelLoop:\n" ++ cond.code inh ++ "ifeq LabelDone\n" ++
    body.code inh ++ "goto LabelLoop\nLabelDone:\n";
  (IfStmt cond the els).code (inh:HasVariables&C) =
    cond.code inh ++ "ifeq LabelElse\n" ++ the.code inh ++
    "goto LabelDone\nLabelElse:\n" ++ els.code inh ++ "LabelDone:\n";
  (PutCharStmt char).code (inh:HasVariables&C) =
    "bipush 44\n" ++ char.code inh ++ "invokevirtual putchar\n";
  (ReturnStmt value).code (inh:HasVariables&C) = value.code inh ++ "ireturn\n";
};

statementCount = trait implements StmtSig<HasCount, Top, Top> => {
  (AssignStmt id value).count = 1;
  (WhileStmt cond body).count = 1;
  (IfStmt cond the els).count = 1;
  (PutCharStmt char).count = 1;
  (ReturnStmt value).count = 1;
};

statementFunctions (C * HasFunctions) = trait implements StmtSig<ChainedFunctions C, Top, Top> => {
  (AssignStmt id value).functions (inh:HasFunctions&C) = inh.functions;
  (WhileStmt cond body).functions (inh:HasFunctions&C) = inh.functions;
  (IfStmt cond the els).functions (inh:HasFunctions&C) = inh.functions;
  (PutCharStmt char).functions (inh:HasFunctions&C) = inh.functions;
  (ReturnStmt value).functions (inh:HasFunctions&C) = inh.functions;
};

statementVariables (C * HasVariables) = trait implements StmtSig<ChainedVariables C, Top, Top> => {
  (AssignStmt id value).variables (inh:HasVariables&C) = inh.variables;
  (WhileStmt cond body).variables (inh:HasVariables&C) = inh.variables;
  (IfStmt cond the els).variables (inh:HasVariables&C) = inh.variables;
  (PutCharStmt char).variables (inh:HasVariables&C) = inh.variables;
  (ReturnStmt value).variables (inh:HasVariables&C) = inh.variables;
};

statementPP = trait implements StmtSig<HasPP, HasPP, HasPP> => {
  (AssignStmt id value).pp = id ++ " = " ++ value.pp ++ ";\n";
  (WhileStmt cond body).pp = "while (" ++ cond.pp ++ ") {\n" ++ body.pp ++ "}\n";
  (IfStmt cond the els).pp =
    "if (" ++ cond.pp ++ ") {\n" ++ the.pp ++ "} else {\n" ++ els.pp ++ "}\n";
  (PutCharStmt char).pp = "putchar(" ++ char.pp ++ ");\n";
  (ReturnStmt value).pp = "return " ++ value.pp ++ ";\n";
};

----------------
-- Expression --
----------------

type ExprSig<Expr, Lst> = {
  ConstExpr : Int -> Expr;
  GetCharExpr : Expr;
  IdExpr : String -> Expr;
  CallExpr : String -> Lst -> Expr;
  PrefixExpr : String -> Expr -> Expr;
  BinaryOpExpr : Expr -> String -> Expr -> Expr;
};

expressionCode (C * HasFunctions & HasVariables) = trait implements ExprSig<HasCode (HasFunctions & HasVariables & C), HasCount & HasCode (HasFunctions & HasVariables & C)> => {
  (ConstExpr value).code (inh:HasFunctions&HasVariables&C) =
    "ldc_w " ++ value.toString ++ "\n";
  (GetCharExpr).code (inh:HasFunctions&HasVariables&C) =
    "bipush 44\ninvokevirtual getchar\n";
  (IdExpr id).code (inh:HasFunctions&HasVariables&C) =
    let addr = inh.variables id in
      addr.fold @String error (\(addr:Int) -> "iload " ++ addr.toString ++ "\n");
  (CallExpr fun args).code (inh:HasFunctions&HasVariables&C) =
    let arity = inh.functions fun in
      arity.fold @String error (\(arity : Int) ->
        if arity != args.count then error else
          "bipush 44\n" ++ args.code inh ++ "invokevirtual " ++ fun ++ "\n");
  (PrefixExpr op body).code (inh:HasFunctions&HasVariables&C) =
    if op == "!" then body.code inh ++ "invokevirtual not_\n"
    else if op == "-" then body.code inh ++ "ineg\n" else error;
  (BinaryOpExpr lhs op rhs).code (inh:HasFunctions&HasVariables&C) =
    lhs.code inh ++ rhs.code inh ++
      if op == "+" then "iadd\n"
      else if op == "-" then "isub\n"
      else if op == "*" then "invokevirtual mul_\n"
      else if op == "/" then "invokevirtual div_\n"
      else if op == "%" then "invokevirtual mod_\n"
      else if op == "&" then "iand\n"
      else if op == "|" then "ior\n"
      else if op == "==" then "invokevirtual eq_\n"
      else if op == "!=" then "invokevirtual ne_\n"
      else if op == "<" then "invokevirtual lt_\n"
      else if op == ">" then "invokevirtual gt_\n"
      else if op == "<=" then "invokevirtual leq_\n"
      else if op == ">=" then "invokevirtual geq_\n"
      else error;
};

expressionCount = trait implements ExprSig<HasCount, Top> => {
  (ConstExpr value).count = 1;
  (GetCharExpr).count = 1;
  (IdExpr id).count = 1;
  (CallExpr fun args).count = 1;
  (PrefixExpr op body).count = 1;
  (BinaryOpExpr lhs op rhs).count = 1;
};

expressionFunctions (C * HasFunctions) = trait implements ExprSig<ChainedFunctions C, Top> => {
  (ConstExpr value).functions (inh:HasFunctions&C) = inh.functions;
  (GetCharExpr).functions (inh:HasFunctions&C) = inh.functions;
  (IdExpr id).functions (inh:HasFunctions&C) = inh.functions;
  (CallExpr fun args).functions (inh:HasFunctions&C) = inh.functions;
  (PrefixExpr op body).functions (inh:HasFunctions&C) = inh.functions;
  (BinaryOpExpr lhs op rhs).functions (inh:HasFunctions&C) = inh.functions;
};

expressionVariables (C * HasVariables) = trait implements ExprSig<ChainedVariables C, Top> => {
  (ConstExpr value).variables (inh:HasVariables&C) = inh.variables;
  (GetCharExpr).variables (inh:HasVariables&C) = inh.variables;
  (IdExpr id).variables (inh:HasVariables&C) = inh.variables;
  (CallExpr fun args).variables (inh:HasVariables&C) = inh.variables;
  (PrefixExpr op body).variables (inh:HasVariables&C) = inh.variables;
  (BinaryOpExpr lhs op rhs).variables (inh:HasVariables&C) = inh.variables;
};

expressionPP = trait implements ExprSig<HasPP, HasPP> => {
  (ConstExpr value).pp = "const(" ++ value.toString ++ ")";
  (GetCharExpr).pp = "getchar()";
  (IdExpr id).pp = "id(" ++ id ++ ")";
  (CallExpr fun args).pp = fun ++ "(" ++ args.pp ++ ")";
  (PrefixExpr op body).pp = op ++ "(" ++ body.pp ++ ")";
  (BinaryOpExpr lhs op rhs).pp = lhs.pp ++ " " ++ op ++ " " ++ rhs.pp;
};

-------------
-- Example --
-------------

example T = trait [self : LstSig<T, T> & ProgSig<T, T> & FunSig<T, T> & ParamSig<T> & DeclSig<T> & StmtSig<T, T, T> & ExprSig<T, T>] => {
  ast = new Prog (new FunDecl "hello"
    (new LstCons (new Param "a") (new LstCons (new Param "b") (new LstEmpty))))
  (new FunDef "hello"
    (new LstCons (new Param "a") (new LstCons (new Param "b") (new LstEmpty)))
    (new IntDecl "c" 42)
    (new AssignStmt "c" (new BinaryOpExpr (new IdExpr "a") "+" (new CallExpr "hello"
      (new LstCons (new IdExpr "a") (new LstCons (new IdExpr "b") (new LstEmpty))))))
  );
  fun = new FunDef "hello" (new Param "x") (new IntDecl "y" 42)
    (new BinaryOpExpr (new IdExpr "x") "*" (new PrefixExpr "-" (new IdExpr "y")));
};

e = new lstCode @(HasFunctions & HasVariables) ,, lstCount ,, lstFunctions @Top ,, lstVariables @Top ,, lstPP ,,
        programCode @(HasVariables & HasOffset) ,, programCount ,, programFunctions @Top ,, programVariables @HasOffset ,, programPP ,,
        functionCode @HasFunctions ,, functionCount ,, functionFunctions @Top ,, functionVariables @Top ,, functionPP ,,
        parameterCode @(HasFunctions & HasVariables & HasOffset) ,, parameterCount ,, parameterFunctions @Top ,, parameterVariables @Top ,, parameterPP ,,
        declarationCode @(HasFunctions & HasVariables) ,, declarationCount ,, declarationFunctions @Top ,, declarationVariables @Top ,, declarationPP ,,
        statementCode @(HasFunctions & HasOffset) ,, statementCount ,, statementFunctions @Top ,, statementVariables @HasOffset ,, statementPP ,,
        expressionCode @HasOffset ,, expressionCount ,, expressionFunctions @Top ,, expressionVariables @HasOffset ,, expressionPP ,,
        example @(HasCode (HasFunctions & HasVariables & HasOffset) & HasCount & ChainedFunctions Top & ChainedVariables HasOffset & HasPP);
e.ast.code { offset = 1, functions = empty, variables = empty }
-- e.ast.pp
