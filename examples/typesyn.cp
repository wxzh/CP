--> 3

type AType = forall A . A -> A;

aid = /\ A . (\x -> x) : A -> A;

aid @Int 3

