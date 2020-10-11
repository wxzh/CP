trait Circuit[I, O] {
  def Identity(n: Int): O
  def Fan(n: Int): O
  def Above(c1: I, c2: I): O
  def Beside(c1: I, c2: I): O
  def Stretch(ns: List[Int], c: I): O
}

trait IWidth { def width: Int }
trait Width extends Circuit[IWidth, IWidth] {
  def Identity(n: Int) = new IWidth {
    def width = n
  }
  def Fan(n: Int) = new IWidth {
    def width = n
  }
  def Above(c1: IWidth, c2: IWidth) = new IWidth {
    def width = c1.width
  }
  def Beside(c1: IWidth, c2: IWidth) = new IWidth {
    def width = c1.width + c2.width
  }
  def Stretch(ns: List[Int], c: IWidth) = new IWidth {
    def width = ns.sum
  }
}

trait IDepth { def depth: Int }
trait Depth extends Circuit[IDepth, IDepth] {
  def Identity(n: Int) = new IDepth {
    def depth = 0
  }
  def Fan(n: Int) = new IDepth {
    def depth = 1
  }
  def Above(c1: IDepth, c2: IDepth) = new IDepth {
    def depth = c1.depth + c2.depth
  }
  def Beside(c1: IDepth, c2: IDepth) = new IDepth {
    def depth = Math.max(c1.depth, c2.depth)
  }
  def Stretch(ns: List[Int], c: IDepth) = new IDepth {
    def depth = c.depth
  }
}

// BEGIN_SCALA_WS
trait IWellSized { def wS: Boolean }
trait WellSized extends Circuit[IWidth with IWellSized, IWellSized] {
  def Identity(n: Int) = new IWellSized {
    def wS = true
  }
  def Fan(n: Int) = new IWellSized {
    def wS = true
  }
  def Above(c1: IWidth with IWellSized, c2: IWidth with IWellSized) = new IWellSized {
    def wS = c1.wS && c2.wS && c1.width == c2.width
  }
  def Beside(c1: IWidth with IWellSized, c2: IWidth with IWellSized) = new IWellSized {
    def wS = c1.wS && c2.wS
  }
  def Stretch(ns: List[Int], c: IWidth with IWellSized) = new IWellSized {
    def wS = c.wS && ns.length == c.width
  }
}
// END_SCALA_WS

trait ILayout { def layout(f: Int => Int): List[List[(Int, Int)]] }
trait Layout extends Circuit[IWidth with ILayout, ILayout] {
  def Identity(n: Int) = new ILayout {
    def layout(f: Int => Int) = List()
  }
  def Fan(n: Int) = new ILayout {
    def layout(f: Int => Int) =
      List(for (i <- List.range(1, n)) yield (f(0), f(i)))
  }
  def Above(c1: IWidth with ILayout, c2: IWidth with ILayout) = new ILayout {
    def layout(f: Int => Int) = c1.layout(f) ++ c2.layout(f)
  }
  def Beside(c1: IWidth with ILayout, c2: IWidth with ILayout) = new ILayout {
    def layout(f: Int => Int) =
      lzw (c1 layout f,c2.layout(f compose (c1.width + _))) (_ ++ _)
  }
  def Stretch(ns: List[Int], c: IWidth with ILayout) = new ILayout {
    def layout(f: Int => Int) = {
      val vs = ns.scanLeft(0)(_ + _).tail
      c.layout(f.compose(vs(_) - 1))
    }
  }
}

def lzw[A](xs: List[A], ys: List[A])(f: (A, A) => A): List[A] = (xs, ys) match {
  case (Nil,_)        =>  ys
  case (_,Nil)        =>  xs
  case (x::xs,y::ys)  =>  f(x,y) :: lzw (xs,ys) (f)
}

def brentKung[C](f: Circuit[C, C]) =
  f.Above(f.Beside(f.Fan(2), f.Fan(2)),
    f.Above(f.Stretch(List(2, 2), f.Fan(2)),
      f.Beside(f.Beside(f.Identity(1), f.Fan(2)), f.Identity(1))))
println(brentKung(new Width {}).width)
