--> "((4+8)*4) is 48"

-- BEGIN_SIG
type ExpSig<Exp> = {
  Lit : Int -> Exp;
  Add : Exp -> Exp -> Exp;
};
-- END_SIG

-- BEGIN_TRAIT_EVAL
type Eval = { eval : Int };
evalNum = trait implements ExpSig<Eval> => {
  (Lit     n).eval = n;
  (Add e1 e2).eval = e1.eval + e2.eval;
};
-- END_TRAIT_EVAL

-- BEGIN_DESUGARED
evalNum = trait implements ExpSig<Eval> => {
  Lit     n = trait => { eval = n; };
  Add e1 e2 = trait => { eval = e1.eval + e2.eval; };
};
-- END_DESUGARED

-- BEGIN_TRAIT_PRINT
type Print = { print : String };
printNum = trait implements ExpSig<Print> => {
  (Lit     n).print = n.toString;
  (Add e1 e2).print = "(" ++ e1.print ++ "+" ++ e2.print ++ ")";
};
-- END_TRAIT_PRINT

-- BEGIN_PRINT_CHILD
printChild = trait implements ExpSig<Eval%Print> => {
  (Lit     n).print = n.toString;
  (Add e1 e2).print = if e2.eval == 0 then e1.print
                      else "(" ++ e1.print ++ "+" ++ e2.print ++ ")";
};
-- END_PRINT_CHILD

-- BEGIN_PRINT_INH
printInh = trait implements ExpSig<Eval&Print> inherits evalNum => {
  (Lit     n).print = n.toString;
  (Add e1 e2).print = if e2.eval == 0 then e1.print
                      else "(" ++ e1.print ++ "+" ++ e2.print ++ ")";
};
-- END_PRINT_INH

-- BEGIN_PRINT_SELF
printSelf = trait implements ExpSig<Eval%Print> => {
  (Lit     n            ).print = n.toString;
  (Add e1 e2 [self:Eval]).print = if self.eval == 0 then "0"
                                  else "(" ++ e1.print ++ "+" ++ e2.print ++ ")";
};
-- END_PRINT_SELF

-- BEGIN_SELF
expAdd Exp = trait [self : ExpSig<Exp>] => {
  test = new Add (new Lit 4) (new Lit 8);
};
-- END_SELF

-- BEGIN_COMPOSE
e = new evalNum ,, printNum ,, expAdd @(Eval&Print);
-- END_COMPOSE

{-
-- BEGIN_USAGE
e.test.print ++ " is " ++ e.test.eval.toString  --> "(4+8) is 12"
-- END_USAGE
-}

-- BEGIN_MUTUAL
type PrintAux = { printAux : String };
printMutual = trait implements ExpSig<PrintAux%Print> => {
  (Lit     n).print = n.toString;
  (Add e1 e2).print = e1.printAux ++ "+" ++ e2.printAux;
};
printAux = trait implements ExpSig<Print%PrintAux> => {
  (Lit     n [self:Print]).printAux = self.print;
  (Add e1 e2 [self:Print]).printAux = "(" ++ self.print ++ ")";
};
-- END_MUTUAL

{-
-- BEGIN_MUTUAL_PRINTER
(new printMutual ,, printAux ,, expAdd @(Print&PrintAux)).test.print  --> "4+8"
-- END_MUTUAL_PRINTER
-}

-- BEGIN_MUL_SIG
type MulSig<Exp> extends ExpSig<Exp> = { Mul : Exp -> Exp -> Exp };
-- END_MUL_SIG

-- BEGIN_MUL_OPS
evalMul = trait implements MulSig<Eval> inherits evalNum => {
  (Mul e1 e2).eval = e1.eval * e2.eval;
};
printMul = trait implements MulSig<Print> inherits printNum => {
  (Mul e1 e2).print = "(" ++ e1.print ++ "*" ++ e2.print ++ ")";
};
-- END_MUL_OPS

-- BEGIN_EXP_MUL
expMul Exp = trait [self : MulSig<Exp>] inherits expAdd @Exp => {
  override test = new Mul super.test (new Lit 4);
};
e' = new evalMul ,, printMul ,, expMul @(Eval & Print);
e'.test.print ++ " is " ++ e'.test.eval.toString  --> "((4+8)*4) is 48"
-- END_EXP_MUL
