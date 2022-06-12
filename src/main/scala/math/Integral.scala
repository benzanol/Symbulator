package sympany.math

import sympany._

object Integral {

  case class SymIntegral(expr: Sym) extends Sym {
    def exprs = Seq(expr)
    def instance(args: Sym*) = SymIntegral(args.head)
  }

  class IntegralActor(init: SymIntegral) {
    var integrals = Set[SymIntegral](init)
    var expressions = Set[Sym]()
    var references = Set[IntegralActor]()

    var solution: Option[Sym] = None

    // List of integrals that are equivalent
    def addInts(is: SymIntegral*) = integrals   ++= is

    // List of expressions that are equivalent to the integrals
    def addExprs(es: Sym*) = expressions ++= es

    // List of actors with expressions that contain this integral
    def addRefs(rs: IntegralActor*) = references  ++= rs

    // If an integral actor that references
    def replace(ints: Set[SymIntegral], sol: Sym) {
      for (int <- ints)
        expressions = expressions.map(_.replaceExpr(int, sol))

      // If one of the expressions now doesn't have an integral, it is the solution
      expressions.find(Integral.getIntegrals(_).isEmpty) match {
        case Some(expr) => this.solve(expr)
        case None => ()
      }
    }

    // If this integral gets solved
    def solve(sol: Sym) {
      this.solution = Some(sol.simple)

      references.foreach(_.replace(integrals, this.solution.get))
    }
  }

  // Return a list of integrals contained in an expression
  def getIntegrals(e: Sym): Seq[SymIntegral] = e match {
    case i @ SymIntegral(sub) => i +: getIntegrals(sub)
    case _ => e.exprs.flatMap(getIntegrals)
  }

  def containsOtherVar(e: Sym): Boolean = e match {
    case SymVar('x) => false
    case SymVar(_) => true
    case _ => e.exprs.map(containsOtherVar).contains(true)
  }

  type ActorMap = scala.collection.mutable.Map[SymIntegral, IntegralActor]

  def integrate(start: SymIntegral): Option[Sym] = {
    if (containsOtherVar(start)) return None

    val startActor = new IntegralActor(start)

    val actors: ActorMap = scala.collection.mutable.Map(start -> startActor)

    // The list of integrals to try to solve
    var queue = List[SymIntegral](start)
    var history = scala.collection.mutable.ListBuffer[SymIntegral](start)

    while (queue.nonEmpty) {
      // Get the first element of the queue, and remove it
      val q = queue.head
      println(s"Queue: $q")
      queue = queue.tail
      
      // Add the new integrals to the end of the queue
      val newIntegrals = tryIntegral(q, actors).filter{ s => !(history contains s) }
      queue ++= newIntegrals
      history ++= newIntegrals
      
      // If the final solution has been found return it
      if (startActor.solution.isDefined)
        return startActor.solution
    }

    // If the queue runs out before any solutions are found, return None
    return None
  }

  // Given an integral, calculate other integrals and expressions that are equal,
  // then see if any of those help to narrow down the search for the solution
  def tryIntegral(base: SymIntegral, actors: ActorMap): Seq[SymIntegral] = {
    import IntegralRules._

    val actor = actors(base)

    // If this integral has already been solved, no need to calculate it
    if (actor.solution.isDefined) return Nil


    // First check if it is a basic integral
    IntegralRules.basicIntegration(base) match {
      case Some(solution) => actor.solve(solution) ; return Nil
      case _ => ()
    }


    // Use rules to calculate equivalent integrals and expressions
    val rawInts: Seq[SymIntegral] = List[SymIntegral]()

    val parts: Seq[Sym] = base.expr match {
      case p: SymProd => integrationByParts(p)
      case _ => Nil
    }
    val splitSum: Seq[Sym] = base.expr.simple match {
      case s: SymSum => Seq(Sym.+++(s.exprs.map(SymIntegral)))
      case _ => Nil
    }
    val rawExprs = parts ++ splitSum


    // Simplify all of the new integrals
    val ints = rawInts.map{ i => SymIntegral(i.expr.simple) }


    // Replace any already solved integrals within the expressions
    val exprs = rawExprs.map(_.simple).map{ e =>
      getIntegrals(e).filter(actors contains _)
        .foldLeft(e){ (acc, i) =>
          actors(i).solution match {
            case Some(iSol) => acc.replaceExpr(i, iSol)
            case None => acc
          }
        }
    }

    // If any of the expressions or integrals have no integrals, then it is a solution
    (exprs ++ ints.map(_.simple)).find(getIntegrals(_).isEmpty) match {
      case Some(solution) => actor.solve(solution) ; return Nil
      case None => ()
    }

    // The new integrals equal the base integral, so they go in the same actor
    actor.addInts(ints:_*)
    for (i <- ints) actors(i) = actor


    actor.addExprs(exprs:_*)

    // Figure out what to do with all of the integrals in the newly created expressions
    var exprIntegrals = Seq[SymIntegral]()

    for (e <- exprs ; i <- getIntegrals(e)) {
      if (!actors.contains(i)) {
        actors(i) = new IntegralActor(i)
        exprIntegrals +:= i
      }

      actors(i).addRefs(actor)
    }

    return ints ++ exprIntegrals
  }
}

object IntegralRules {
  import sympany.Sym._
  import sympany.Pattern._
  import Integral._

  def basicIntegration(integral: SymIntegral): Option[Sym] =
    integral.expr match {
      case c: SymConstant => Some(**(c, SymVar('x)).simple)
      case SymPow(SymVar('x), p: SymConstant) =>
        Some( **(^(++(p, 1), -1), ^('x, ++(p, 1))).simple )
      case SymPow(b, SymVar('x)) if Pattern.noX(b) =>
        Some(**(^(SymLog(b), -1), ^(b, 'x)).simple)
      case e => basicIntegrals.get(e)
    }

  def integrationByParts(integrate: SymProd): Seq[Sym] =
    integrate.simple.exprs.toSet
      .subsets
      .filter(_.nonEmpty)
      .map{us =>
        val u = ***(us.toList).simple
        val du = u.derivative
        val dv = ***({integrate.simple.exprs.toSet diff us}.toList)
        val v = SymIntegral(dv)
        ++(**(u, v), **(S(-1), SymIntegral(**(v, du)))).simple
      }.toSeq

  val basicIntegrals = Map[Sym, Sym](
    'x.s -> **(1~2, ^('x, 2)),
    SymSin('x) -> **(S(-1), SymCos('x)),
    SymCos('x) -> SymSin('x),
  )
}
