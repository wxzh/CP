--> "Have fun!4"

type Comment = { content : String };
comment (c : String) = trait [self : Comment] => {
  content = c
};


type Up = { upvotes : Int };
up (u : Int) = trait [self : Up] => {
  upvotes = u
};

test = new comment("Have fun!") ,, up(4);

test.content ++ (test.upvotes).toString

