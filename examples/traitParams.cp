--> 1.0

type IdType T = {
  f : T -> T
};

type AType = {
  a : Int
};

idTrait (T * AType) = trait implements IdType T => {
  f = \(x:T) -> x
};

id = new idTrait @Double;

id.f 1.0
