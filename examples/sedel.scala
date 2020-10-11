type ExpAlg[E] = {
  lit : Int -> E,
  add : E -> E -> E
};

type Value = { value : Int };
trait value => {
  lit (n: Int) = { value = n };
  add (e1: Value) (e2: Value) = { value = e1.value + e2.value }
};

type Pp = { pp : String };
trait pp => {
  lit (n: Int) = { pp = n.toString };
  add (e1: Pp) (e2: Pp) = { pp = e1.pp ++ "+" ++ e2.pp }
};

trait pp2 => {
  lit (n: Int) = { pp = n.toString };
  add (e1: Pp) (e2: Pp & Value) = 
    if (e2.value == 0) then e1 else { pp = e1.pp ++ "+" ++ e2.pp }
};

exp E (f: ExpAlg[E]) = f.add (f.lit 1) (f.lit 0);

alg = new value ,, pp2;

> (exp (Pp & Value) alg).pp

-- > (exp (Pp & Value) (new value ,, pp2)).pp
-- > (exp Pp new pp with pp2).pp
-- > open ((new value ,, pp2) : Expr[Value & Pp]) in (add (lit 1) (lit 0)).pp
-- > open (new pp2 : Expr[Value & Pp]) in (add (lit 1) (lit 0)).pp
-- > open ((new pp2) : Expr[Value & Pp]) in lit 1

