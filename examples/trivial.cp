--> "((4.0 + 3.0) - 3.0) = 4.0"

-- Examples in "The Expression Problem, Trivially!"


type IEval = {eval : Double};
lit (x : Double) = trait [self : IEval] => {
  eval = x
};

add (e1 : IEval) (e2 : IEval) = trait => {
  eval = e1.eval + e2.eval
};


sub (e1 : IEval) (e2 : IEval) = trait => {
  eval  = e1.eval - e2.eval
};

type IPrint = IEval & { print : String };

litP (x : Double) = trait [self : IPrint] inherits lit x => {
  print = x.toString
};

addP (e1 : IPrint) (e2 : IPrint) = trait [self : IPrint] inherits add e1 e2 => {
  print = "(" ++ e1.print ++ " + " ++ e2.print ++ ")"
};

subP (e1 : IPrint) (e2 : IPrint) = trait [self : IPrint] inherits sub e1 e2 => {
  print = "(" ++ e1.print ++ " - " ++ e2.print ++ ")"
};


l1 = new litP 4;
l2 = new litP 3;
l3 = new addP l1 l2;
e  = new subP l3 l2;
e.print ++ " = " ++ e.eval.toString
