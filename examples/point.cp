--> "(3, 4)"

type Point = { x_point : Int, get : Top -> String };

point (x : Int) = trait [self : Point] => {
  x_point = x;
  get (_ : Top) = self.x_point.toString
};

type Point2D = Point & { y_point : Int };

point2D (x: Int) (y : Int) = trait [self : Point2D] inherits (point x) \ {get : Top -> String} => {
    y_point = y;
    get (_ : Top) = "(" ++ self.x_point.toString ++ ", " ++ self.y_point.toString ++ ")"
  };

a_point = new point2D 3 4;

a_point.get ()
