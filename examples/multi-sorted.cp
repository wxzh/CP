--> "lam x: Bool->Bool.x x"
type Print = { print : String };


type LamAlg<E> T = {
  var : String -> E;
  abs : String -> T -> E -> E;
  app : E -> E -> E;
};


printLam = trait implements LamAlg<Print> Print => {
  (var x).print = x;
  (abs x t e).print = "lam " ++ x ++ ": " ++ t.print ++ "." ++ e.print;
  (app e1 e2).print = e1.print ++ " " ++ e2.print
};

type TyAlg<T> = {
  tyBool : T;
  tyArr : T -> T -> T;
};

printTy = trait implements TyAlg<Print> => {
  (tyBool).print = "Bool";
  (tyArr t1 t2).print = t1.print ++ "->" ++ t2.print
};

term E T = trait [self: LamAlg<E> T & TyAlg<T>] => {
  e1 = app (abs "x" (tyArr tyBool tyBool) (var "x")) (var "x")
};

(new printTy ,, printLam ,, term @Print @Print).e1.print
