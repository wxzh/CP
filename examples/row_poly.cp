--> 15

{-

Emulate row polymorphism

-}

type Growable = { grow : Int -> Int };

type Fish = {
  size : Int,
  grow : Int -> Int
};

type Dog = {
  size : Int,
  grow : Int -> Int,
  howl : Top -> String
};

type Size = { size : Int };

dory (init_size : Int) = trait [self : Size] => {
  size = init_size;
  grow (amt : Int) = amt + self.size
};


snoopy (init_size : Int) = trait [self : Size] => {
  size = init_size;
  grow (amt : Int) = amt + self.size;
  howl (_ : Top) = "ARH-WOOOOOOOOOOOOOOOOOOOO"
};


-- Make something picky...
picky_mixin (A * Growable) (base : Trait[Size, Growable & A]) = trait [self : Size] inherits base => {
  override grow (amt : Int) = super.grow (0.75 * amt)
};

picky_dory (init_size : Int) = picky_mixin @Size (dory init_size);

picky_snoopy (init_size : Int) = picky_mixin @(Size & {howl : Top -> String}) (snoopy init_size);


-- Making objects

dory1 = new dory 3;

snoopy1 = new snoopy 12;

picky_dory1 = new picky_dory 3;

picky_snoopy1 = new picky_snoopy 12;

picky_snoopy1.grow 4
