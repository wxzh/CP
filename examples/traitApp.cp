--> 4.0

type A = {m : Double, n : Double};

genA = trait [self : A] => {
  m = 1;
  n = self.m + 1
};

genB = trait [self : A] => {
  m = 2;
  n = self.m + 2
};


gen1 = trait [self : A] inherits genA \ {m : Double} ,, genB \ {n : Double} => {
  override m = super.m + 1
};


gen2 = trait [self : A] inherits genA \ {m : Double} ,, genB \ {n : Double} => {
  override m = (genA ^ self).m + 1
};


o1 = new gen1;

o2 = new gen2;

o1.n -- 4
