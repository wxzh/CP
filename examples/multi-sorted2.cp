--> "lam x: Bool->Bool.x true"
type Print = { print : String };


type MultiAlg<E,T>  = {
  var : String -> E;
  abs : String -> T -> E -> E;
  app : E -> E -> E;
  tyBool : T;
  tyArr : T -> T -> T;
};

type ExtAlg<E,T> = MultiAlg<E,T> & {
  t : E;
  f : E;
};


print = trait implements MultiAlg<Print,Print> => {
  (var x).print = x;
  (abs x t e).print = "lam " ++ x ++ ": " ++ t.print ++ "." ++ e.print;
  (app e1 e2).print = e1.print ++ " " ++ e2.print;
  (tyBool).print = "Bool";
  (tyArr t1 t2).print = t1.print ++ "->" ++ t2.print;
};

printExt = trait implements ExtAlg<Print,Print> inherits print => {
  (t).print = "true";
  (f).print = "false";
};


term E T = trait [self: ExtAlg<E,T>] => {
  e1 = app (abs "x" (tyArr tyBool tyBool) (var "x")) t
};

(new printExt ,, term @Print @Print).e1.print
