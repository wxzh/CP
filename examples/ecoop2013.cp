--> "5 + 4 = 9 and 5 + 4 = 9"

type GExpAlg <E> = {
  Lit : Int -> E;
  Add : E -> E -> E;
};

type Eval = { eval : Int };

eval = trait implements GExpAlg<Eval> => {
  (Lit n ).eval = n;
  (Add e1 e2).eval = e1.eval + e2.eval;
};

type Print = { print : String };

print = trait implements GExpAlg<Print> => {
  (Lit n).print = n.toString;
  (Add e1 e2).print = e1.print ++ "+" ++ e2.print;
};

print2 = trait implements GExpAlg<Eval%Print> => {
  (Lit n).print = n.toString;
  (Add e1 e2 [self:Eval]).print = e1.print ++ "+" ++ e2.print ++ self.eval.toString;
};


-- print2
type EP = Eval & Print;
print3 = trait [fself: GExpAlg<EP>] implements GExpAlg<Eval%Print> => {
  (Lit n).print = n.toString;
  (Add e1 e2 [self:EP]).print =
    let plus54 = new fself.Add (new (fself.Lit 5)) (new fself.Lit 4)
    in e1.print ++ " + " ++ e2.print ++ " = " ++ self.eval.toString ++ " and " ++ "5 + 4 = " ++ plus54.eval.toString;
};

term A = trait [self: GExpAlg <A>] => {
  plus54 = new Add (new Lit 5) (new Lit 4)
};

(new print3 ,, eval ,, (term @EP)).plus54.print
