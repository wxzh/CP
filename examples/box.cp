--> "Round button has area: 28.26"

type Point = { x : Double, y : Double };
point (x : Double) (y : Double) = trait => {
  x = x;
  y = y } ;

pointTest  = new point 3 4;

abs (x : Double) = if x < 0 then (0 - x) else x;

square (x : Double) = x * x;


type Circle = Point & {radius : Double};
circle (center : Point) (radius : Double) =
  trait inherits point center.x center.y =>{ radius = radius };

circleTest = new circle pointTest 3;

type CircleFns = { area : Double, grow : Double, shrink : Double };
circleFns = trait [self : Circle] => {
  area   = self.radius * self.radius * 3.14;
  grow   = self.radius + 1;
  shrink = self.radius - 1 };

circleWithFns = new (circle pointTest 3 ,, circleFns);

type Button = { label : String };
button (label : String) = trait => { label = label };

type ButtonFns = { hover : Bool -> String, press : Bool -> String };
buttonFns = trait [self : Button] => {
  hover (b : Bool) = if b then "hovering..." else "no hovering";
  press (b : Bool) = if b then "pressing..." else "no pressing" };

type RoundButton = Circle & Button;
roundButton (radius : Double) (center: Point ) (label : String) = 
  circle center radius ,, button label;


asOval (shortRadius : Double) (longRadius : Double) = trait => {
  radius = shortRadius;
  longRadius = longRadius };


oval (shortRadius : Double) (longRadius : Double) (center: Point) =
  (circle center shortRadius) \ { radius : Double } ,, asOval shortRadius longRadius;

type Norm = { norm : Double -> Double -> Double };
euclideanNorm = trait [self : Point] => {
  norm (x : Double) (y : Double) = (square(self.x - x) + square(self.y - y)).sqrt };
manhattanNorm = trait [self : Point] => {
  norm (x : Double) (y : Double) = abs((self.x - x)) + abs((self.y - y)) };

type CircleFns2 = CircleFns & { inCircle : Double -> Double -> Bool };
circleFns2 = trait [self : Circle & Norm ] inherits circleFns => {
  inCircle (x : Double) (y : Double) = self.norm x y < self.radius };

roundButtonFac (radius : Double) (center : Point) (norm : Trait[Point, Norm]) =
  new roundButton radius center "Round button" ,, circleFns2 ,, buttonFns ,, norm;

roundButtonTest2 = roundButtonFac 3 pointTest euclideanNorm;

test = roundButtonTest2.inCircle 3 4;

roundButtonTest = new
  roundButton 3 pointTest "Round button" ,, circleFns ,, buttonFns;
roundButtonTest.label ++ " has area: " ++ (roundButtonTest.area).toString
-- Output: "Round button has area: 28.26"
