--> "((0-0)+0) and 0 and 0 and (3-(1+1)) = 1"

type ExprSig<E> = {
  Lit : Int -> E,
  Add : E -> E -> E
};

type HasValue = { value : Int };

exprValue = trait implements ExprSig<HasValue> => {
  (Lit n).value = n;
  (Add e1 e2).value = e1.value + e2.value;
};

type HasPP = { pp : String };

exprPP0 = trait implements ExprSig<HasPP> => {
  (Lit n).pp = n.toString;
  (Add e1 e2).pp = "(" ++ e1.pp ++ "+" ++ e2.pp ++ ")";
};

exprPP1 = trait implements ExprSig<HasValue%HasPP> => {
  (Lit n).pp = n.toString;
  (Add e1 e2).pp =
    if e2.value == 0
    then e1.pp
    else "(" ++ e1.pp ++ "+" ++ e2.pp ++ ")";
};

exprPP2 = trait implements ExprSig<HasValue%HasPP> => {
  (Lit n).pp = n.toString;
  (Add e1 e2 [self : HasValue]).pp =
    if self.value == 0
    then "0"
    else "(" ++ e1.pp ++ "+" ++ e2.pp ++ ")";
};

type ExprSubSig<E> = {
  Sub : E -> E -> E
};

exprSubValue = trait implements ExprSubSig<HasValue> => {
  (Sub e1 e2).value = e1.value - e2.value;
};

exprSubPP0 = trait implements ExprSubSig<HasPP> => {
  (Sub e1 e2).pp = "(" ++ e1.pp ++ "-" ++ e2.pp ++ ")";
};

exprSubPP1 = trait implements ExprSubSig<HasValue%HasPP> => {
  (Sub e1 e2).pp =
    if e2.value == 0
    then e1.pp
    else "(" ++ e1.pp ++ "-" ++ e2.pp ++ ")";
};

exprSubPP2 = trait implements ExprSubSig<HasValue%HasPP> => {
  (Sub e1 e2 [self : HasValue]).pp =
    if self.value == 0
    then "0"
    else "(" ++ e1.pp ++ "-" ++ e2.pp ++ ")";
};


expr T = trait [self : ExprSig<T> & ExprSubSig<T>] => {
  zero = new Add (new Sub (new Lit 0) (new Lit 0)) (new Lit 0);
  one = new Sub (new Lit 3) (new Add (new Lit 1) (new Lit 1));
};

base = expr @(HasValue & HasPP) ,, exprValue ,, exprSubValue;
t0 = new base ,, exprPP0 ,, exprSubPP0;
t1 = new base ,, exprPP1 ,, exprSubPP1;
t2 = new base ,, exprPP2 ,, exprSubPP2;

t0.zero.pp ++ " and " ++ t1.zero.pp ++ " and " ++ t2.zero.pp ++ " and " ++
t0.one.pp ++ " = " ++ t0.one.value.toString
