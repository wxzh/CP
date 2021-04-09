--> 120

{---------------------------

AG = {G, A, R}
G = {N, T, S, P}
A = ⋃_{X∈N}(Syn(X) ∪ Inh(X))
R = ⋃_{p∈P}(R(p))

N = {R, F}
T = {ε}
S = R
P = {
  p_R  : R -> F,
  p_F1 : F -> F,
  p_F2 : F -> ε
}

Inh(Exp) = {in}
Syn(Exp) = {out}

R(p_R) = {
  F.in = R.in,
  R.out = F.out
}
R(p_F1) = {
  F_2 = if F_2.in == 0 then p_F2 else p_F1,
  F_2.in = F_1.in - 1,
  F_1.out = F_1.in * F_2.out
}
R(p_F2) = { F.out = 1 }

---------------------------}

type Fact<T> = {
  E : T,
  F : T,
  R : T -> T
};

type Out = { out : Int -> Int };
fact = trait [self : Fact<Out>] implements Fact<Out> => {
  ( E ).out (_:Int) = 1;
  ( F ).out (i:Int) = if i == 0 then (new E).out undefined
                      else i * (new F).out (i - 1);
  (R f).out (i:Int) = f.out i;
};

init T = trait [self : Fact<T>] => {
  init = new R (new F);
};

(new fact ,, init @Out).init.out 5
