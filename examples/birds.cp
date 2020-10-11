--> "I am a duck, I can fly, I can swim"


swimming = trait => {
  swim = "I can swim"
};

flying = trait => {
  fly = "I can fly"
};

duck = trait inherits swimming ,, flying => {
  name = "I am a duck"
};

superDuck = new duck;
superDuck.name ++ ", " ++ superDuck.fly ++ ", " ++ superDuck.swim
