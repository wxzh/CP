def lzw[A](xs: List[A], ys: List[A])(f: (A, A) => A): List[A] = (xs, ys) match {
  case (Nil,_)        =>  ys
  case (_,Nil)        =>  xs
  case (x::xs,y::ys)  =>  f(x,y) :: lzw (xs,ys) (f)
}

trait Circuit1 {
  def width: Int
}
trait Identity1 extends Circuit1 {
  val n: Int
  def width = n
}
trait Fan1 extends Circuit1 {
  val n: Int
  def width = n
}
trait Above1 extends Circuit1 {
  val c1, c2: Circuit1
  def width = c1.width
}
trait Beside1 extends Circuit1 {
  val c1, c2: Circuit1
  def width = c1.width + c2.width
}
trait Stretch1 extends Circuit1 {
  val ns: List[Int]
  val c: Circuit1
  def width = ns.sum
}

trait Circuit2 extends Circuit1 {
  def depth: Int
}
trait Identity2 extends Identity1 with Circuit2 {
  def depth = 0
}
trait Fan2 extends Fan1 with Circuit2 {
  def depth = 1
}
trait Above2 extends Above1 with Circuit2 {
  val c1, c2: Circuit2
  def depth = c1.depth + c2.depth
}
trait Beside2 extends Beside1 with Circuit2 {
  val c1, c2: Circuit2
  def depth = Math.max(c1.depth, c2.depth)
}
trait Stretch2 extends Stretch1 with Circuit2 {
  val c: Circuit2
  def depth = c.depth
}

trait Circuit3 extends Circuit2 {
  def wellSized: Boolean
}
trait Identity3 extends Identity2 with Circuit3 {
  def wellSized = true
}
trait Fan3 extends Fan2 with Circuit3 {
  def wellSized = true
}
trait Above3 extends Above2 with Circuit3 {
  val c1, c2: Circuit3
  def wellSized = c1.wellSized && c2.wellSized && c1.width==c2.width
}
trait Beside3 extends Beside2 with Circuit3 {
  val c1, c2: Circuit3
  def wellSized = c1.wellSized && c2.wellSized
}
trait Stretch3 extends Stretch2 with Circuit3 {
  val c: Circuit3
  def wellSized = c.wellSized && ns.length==c.width
}

trait Circuit4 extends Circuit3 {
  def layout(f: Int => Int): List[List[(Int, Int)]]
}
trait Identity4 extends Identity3 with Circuit4 {
  def layout(f: Int => Int) = List()
}
trait Fan4 extends Fan3 with Circuit4 {
  def layout(f: Int => Int) =
    List(for (i <- List.range(1, n)) yield (f(0), f(i)))
}
trait Above4 extends Above3 with Circuit4 {
  val c1, c2: Circuit4
  def layout(f: Int => Int) = c1.layout(f) ++ c2.layout(f)
}
trait Beside4 extends Beside3 with Circuit4 {
  val c1, c2: Circuit4
  def layout(f: Int => Int) =
    lzw (c1 layout f,c2.layout(f compose (c1.width + _))) (_ ++ _)
}
trait Stretch4 extends Stretch3 with Circuit4 {
  val c: Circuit4
  def layout(f: Int => Int) = {
    val vs = ns.scanLeft(0)(_ + _).tail
    c.layout(f.compose(vs(_) - 1))
  }
}

trait Circuit[C] {
  def Identity(x: Int): C
  def Fan(x: Int): C
  def Above(x: C, y: C): C
  def Beside(x: C, y: C): C
  def Stretch(x: C, xs: Int*): C
}

trait Factory extends Circuit[Circuit4] {
  def Identity(x: Int)                 = new Identity4 { val n = x }
  def Fan(x: Int)                      = new Fan4      { val n = x }
  def Above(x: Circuit4, y: Circuit4)  = new Above4    { val c1 = x; val c2 = y }
  def Beside(x: Circuit4, y: Circuit4) = new Beside4   { val c1 = x; val c2 = y }
  def Stretch(x: Circuit4, xs: Int*)   = new Stretch4  { val ns = xs.toList; val c = x }
}

def brentKung[C](f: Circuit[C]) =
  f.Above(f.Beside(f.Fan(2), f.Fan(2)),
    f.Above(f.Stretch(f.Fan(2), 2, 2),
      f.Beside(f.Beside(f.Identity(1), f.Fan(2)), f.Identity(1))))

trait RStretch extends Stretch4 {
  override def layout(f: Int => Int) = {
    val vs = ns.scanLeft(ns.last - 1)(_ + _).init
    c.layout(f.compose(vs(_)))
  }
}

trait NCircuit[C] extends Circuit[C] {
  def RStretch(x: C, xs: Int*): C
}

trait NFactory extends NCircuit[Circuit4] with Factory {
  def RStretch(x: Circuit4, xs: Int*) = new RStretch { val ns = xs.toList; val c = x }
}

def circuit[C](f: NCircuit[C]) = f.RStretch(brentKung(f), 2, 2, 2, 2)
println(circuit(new NFactory {}).layout { x => x })
