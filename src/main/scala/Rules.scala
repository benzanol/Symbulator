package sympany.rules

import sympany.symbolics._
import sympany.symbolics.Sym._
import sympany.patterns._
import sympany.patterns.Pattern._

class Rule(name: String, p: Pattern, f: Any => Sym) {
  def first(e: Sym): Option[Sym] =
    try {
      LazyList(p.matches(e):_*)
        .map(callWithBind[Sym](_)(f))
        .find(_.id != e.id)
    } catch {
      case err: Throwable =>
        println(f"Rule `$name` threw error `$err`") ; None
    }

  def all(e: Sym): Seq[Sym] =
    p.matches(e)
      .map(callWithBind[Sym](_)(f))
      .filter(_.id != e.id)
}

class Rules() {
  val rules = scala.collection.mutable.Map[Sym, Seq[Rule]]()
  def +(t: Sym)(n: String)(p: Pattern)(f: Any => Sym) =
    rules(t) = rules.getOrElse(t, Nil) :+ new Rule(n, p, f)

  def apply(sym: Sym): Seq[Rule] = {
    rules.toList
      .filter{ r => (r._1 == SymInt(0)) || (r._1.getClass.isInstance(sym)) }
      .flatMap(_._2)
  }

  def first(e: Sym): Option[Sym] =
    LazyList(apply(e):_*).flatMap(_.first(e)).headOption

  def all(e: Sym): Seq[Sym] =
    apply(e).foldLeft(Seq[Sym]()){ (acc, r) => acc ++ r.all(e) }
}
