--> "(3.0, 4.0)"

type Point = { x_point : Double, get : Top -> String };

point (x : Double) = trait [self : Point] => {
  x_point = x;
  get (_ : Top) = self.x_point.toString
};

type Point2D = Point & { y_point : Double };

point2D (x: Double) (y : Double) = trait [self : Point2D] inherits (point x) \ {get : Top -> String} => {
    y_point = y;
    get (_ : Top) = "(" ++ self.x_point.toString ++ ", " ++ self.y_point.toString ++ ")"
  };

a_point = new point2D 3 4;

a_point.get ()
