object OOP {
//BEGIN_EP_OOP
abstract class Exp {
  def eval:  Int
  def print: String
}
class Lit(n: Int) extends Exp {
  def eval  = n
  def print = n.toString
}
class Add(l: Exp, r: Exp) extends Exp {
  def eval  = l.eval + r.eval
  def print = l.print + "+" + r.print
}
//END_EP_OOP
}

object FP {
//BEGIN_EP_FP
abstract class Exp
case class Lit(n: Int) extends Exp
case class Add(l: Exp, r: Exp) extends Exp
def eval(e: Exp): Int = e match {
  case Lit(n)    => n
  case Add(l, r) => eval(l) + eval(r)
}
def print(e: Exp): String = e match {
  case Lit(n)    => n.toString
  case Add(l, r) => print(l) + "+" + print(r)
}
//END_EP_FP
}object ObjectAlgebras extends App {

//BEGIN_OA_EXP
trait ExpAlg[Exp] {
  def Lit: Int       => Exp
  def Add: (Exp,Exp) => Exp
}
//END_OA_EXP

//BEGIN_OA_EVAL
trait IEval {
  def eval: Int
}
trait Eval extends ExpAlg[IEval] {
  def Lit = n => new IEval {
    def eval = n
  }
  def Add = (e1,e2) => new IEval {
    def eval = e1.eval + e2.eval
  }
}
object eval extends Eval
//END_OA_EVAL

//BEGIN_OA_PRINT
trait IPrint {
  def print: String
}
trait Print extends ExpAlg[IPrint] {
  def Lit = n => new IPrint {
    def print = n.toString
  }
  def Add = (e1,e2) => new IPrint {
    def print = "(" ++ e1.print ++ "+" ++ e2.print ++ ")"
  }
}
object print extends Print
//END_OA_PRINT

//BEGIN_OA_DPRINT
trait DPrint extends ExpAlg[IEval with IPrint] {
  def Lit = n => new IEval with IPrint {
    def eval = n
    def print = n.toString
  }
  def Add = (e1,e2) => new IEval with IPrint {
    def eval  = e1.eval + e2.eval
    def print = if (e1.eval == 0) e2.print
                else "(" ++ e1.print ++ "+" ++ ")"
  }
}
//END_OA_DPRINT

//BEGIN_OA_MUL
trait MulAlg[Exp] extends ExpAlg[Exp] {
  def Mul: (Exp,Exp) => Exp
}
//END_OA_MUL

//BEGIN_OA_EVALMUL
trait EvalMul extends MulAlg[IEval] with Eval {
  def Mul = (e1,e2) => new IEval {
    def eval = e1.eval * e2.eval
  }
}
//END_OA_EVALMUL

//BEGIN_OA_TERM
def exp[Exp](f: ExpAlg[Exp]) = f.Add(f.Lit(0),f.Lit(1))
//END_OA_TERM

//trait Lifter[A,B] {
//}
//BEGIN_OA_EXPMERGE
trait ExpMerge[A,B] extends ExpAlg[A with B] {
  val alg1: ExpAlg[A]
  val alg2: ExpAlg[B]
  def lift(x: A, y: B) : A with B

  def Lit = n =>
    lift(alg1.Lit(n),alg2.Lit(n))
  def Add = (e1,e2) =>
    lift(alg1.Add(e1, e2),alg2.Add(e1, e2))
}
//END_OA_EXPMERGE
//BEGIN_OA_EVALPRINT
object evalPrint extends ExpMerge[IEval,IPrint] {
  val alg1 = eval
  val alg2 = print

  def lift(x: IEval, y: IPrint) = new IEval with IPrint {
    def eval  = x.eval
    def print = y.print
  }
}
//END_OA_EVALPRINT

//BEGIN_OA_CLIENT
println(exp(eval).eval)   // 1
println(exp(print).print) // "(0+1)"
//END_OA_CLIENT

//BEGIN_OA_COMP_CLIENT
val e = exp(evalPrint)
println(e.print + "=" + e.eval)
//END_OA_COMP_CLIENT

object GOA extends App {
//BEGIN_GOA_GEXP
trait GExpAlg[Exp,OExp] {
  def Lit: Int       => OExp
  def Add: (Exp,Exp) => OExp
}
//END_GOA_GEXP

//BEGIN_GOA_EXP
type ExpAlg[Exp] = GExpAlg[Exp,Exp]
//END_GOA_EXP

trait IEval {
  def eval: Int
}

trait Eval extends ExpAlg[IEval] {
  def Lit = n =>
    new IEval { def eval = n }
  def Add = (e1,e2) =>
    new IEval { def eval = e1.eval + e2.eval }
}

trait IPrint {
  def print: String
}
//BEGIN_GOA_PRINTEVAL
trait DPrint extends GExpAlg[IEval with IPrint,IPrint] {
  def Lit = n => new IPrint {
    def print = n.toString
  }
  def Add = (e1,e2) => new IPrint {
    def print = if (e1.eval == 0) e2.print
                else "(" ++ e1.print ++ "+" ++ ")"
  }
}
//END_GOA_PRINTEVAL

trait ExpMerge[A,B] extends ExpAlg[A with B] {
  val alg1: ExpAlg[A]
  val alg2: ExpAlg[B]
  def lift(x: A, y: B ) : A with B

  def Lit(x: Int) : A with B =
    lift(alg1.Lit(x),alg2.Lit(x))
  def Add(e1: A with B, e2: A with B) : A with B =
    lift(alg1.Add(e1, e2),alg2.Add(e1, e2))
}
}

  
