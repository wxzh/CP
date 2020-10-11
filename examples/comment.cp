--> "Have fun!4.0"

type Comment = { content : String };
comment (c : String) = trait [self : Comment] => {
  content = c
};


type Up = { upvotes : Double };
up (u : Double) = trait [self : Up] => {
  upvotes = u
};

test = new comment("Have fun!") ,, up(4);

test.content ++ (test.upvotes).toString

