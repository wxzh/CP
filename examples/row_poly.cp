--> 15.0

{-

Emulate row polymorphism

-}

type Growable = { grow : Double -> Double };

type Fish = {
  size : Double,
  grow : Double -> Double
};

type Dog = {
  size : Double,
  grow : Double -> Double,
  howl : Top -> String
};

type Size = { size : Double };

dory (init_size : Double) = trait [self : Size] => {
  size = init_size;
  grow (amt : Double) = amt + self.size
};


snoopy (init_size : Double) = trait [self : Size] => {
  size = init_size;
  grow (amt : Double) = amt + self.size;
  howl (_ : Top) = "ARH-WOOOOOOOOOOOOOOOOOOOO"
};


-- Make something picky...
picky_mixin (A * Growable) (base : Trait[Size, Growable & A]) = trait [self : Size] inherits base => {
  override grow (amt : Double) = super.grow (0.75 * amt)
};

picky_dory (init_size : Double) = picky_mixin @Size (dory init_size);

picky_snoopy (init_size : Double) = picky_mixin @(Size & {howl : Top -> String}) (snoopy init_size);


-- Making objects

dory1 = new dory 3;

snoopy1 = new snoopy 12;

picky_dory1 = new picky_dory 3;

picky_snoopy1 = new picky_snoopy 12;

picky_snoopy1.grow 4
