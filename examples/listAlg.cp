type ListSig <Lst> A = {
  Nil : Lst;
  Cons : A -> Lst -> Lst;
};

type Size = { size : Int };

size A = trait implements ListSig <Size> A => {
  (Nil).size = 0;
  (Cons x xs).size = xs.size + 1;
};

test Lst = trait [self: ListAlg <Lst> Int] => {
  test = Cons 2 (Cons 1 Nil);
};

1