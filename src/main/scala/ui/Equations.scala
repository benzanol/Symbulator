package sympany.ui

import scala.util.chaining._
import scala.collection.mutable

import org.scalajs.dom
import org.scalajs.dom.document
import org.scalajs.dom.window
import scala.scalajs.js
import scala.scalajs.js.annotation.JSExportTopLevel

import sympany._
import sympany.math._
import sympany.ui._
import sympany.Main.jslog

object Equations {
  var handlers = Seq[EquationHandler]()

  // Update the layout of equations on the page based on the list of handlers
  def updateEquations(): Unit = {
    val parent = document.getElementById("equations")

    // Remove the existing equations
    parent.replaceChildren()

    // Add the equation from each handler
    handlers.foreach{ h => parent.appendChild(h.rootElem) }
  }

  // Whenever any equation changes, the graph screen needs to be updated
  def updateGraphs: Unit =
    Graph.setGraphs(handlers.flatMap(_.eqn))

  // Create a new html element with various properties and return it
  def makeElement(tag: String, props: (String, String)*): dom.Element = {
    val e: dom.Element = document.createElement(tag)
    props.foreach{
      case ("innerHTML", html) => e.innerHTML = html
      case ("innerText", text) => e.innerText = text
      case (k, v) => e.setAttribute(k, v)
    }
    return e
  }

  // API (from JS) functions

  // Create a new equation
  @JSExportTopLevel("addEquation")
  def addEquation(): Unit = {
    val h = new EquationHandler()
    handlers :+= h
    updateEquations()

    // Shift focus to the equation
    js.eval(s"MQ(document.getElementById('eqn-${h.id}')).focus()")
  }

  // Update the handler that has the specified id to have a new equation
  @JSExportTopLevel("updateLatex")
  def updateLatex(id: String, latex: String): Unit = {
    handlers.find(_.id == id) match {
      case Some(h) => {
        h.updateLatex(latex)
        updateGraphs
      }
      case None => throw new Exception(s"Handler $id not found")
    }
  }
}

import Equations.makeElement

class EquationHandler() {
  val id = scala.util.Random.nextInt().abs.toString

  val rootElem = makeElement("div", "class" -> "eqn-div",   "id" -> s"div-$id",  "hid" -> id)
  val eqnElem  = makeElement("p", "class" -> "mq-dynamic",  "id" -> s"eqn-$id",  "hid" -> id)
  val propElem = makeElement("div", "class" -> "eqn-props", "id" -> s"prop-$id", "hid" -> id)
  rootElem.appendChild(eqnElem)
  rootElem.appendChild(propElem)

  js.Dynamic.global.formatEquation(eqnElem)

  var latex: String = ""
  var eqn: Option[SuperSym] = None

  def updateLatex(newLatex: String): Unit = {
    if (newLatex == this.latex) return

    this.latex = newLatex
    this.eqn = Parse.parseLatex(newLatex).map(SuperSym(_))

    propElem.replaceChildren()

    if (eqn.isDefined)
      for (p <- eqn.get.props) {
        // Create a div for the property and add it to the property list
        val div = Equations.makeElement("div", "class" -> "eqn-prop")
        propElem.appendChild(div)

        // Add the description and equations of the property to the div
        div.appendChild(makeElement("p", "class" -> "prop-name", "innerText" -> p._1))
        for (i <- 0 until p._2.length) {
          val text = p._2(i).toLatex + (if (i == p._2.length - 1) "" else ",")
          val el = makeElement("p", "class" -> "mq-static", "innerText" -> text)
          div.appendChild(el)
        }
      }

    println(eqn.map(_.derivative))

    // Format the static equations as latex with mathquill
    js.Dynamic.global.formatStaticEquations()
  }
}

case class SuperSym(orig: Sym) {
  lazy val sym = Simplify.simplify(orig)
  
  lazy val explicit: Option[Sym] =
    if (!Sym.containsExpr(sym, SymVar('y))) Some(sym)
    else Solve.solve(sym, 'y).headOption
  
  lazy val solutions: Seq[Sym] = explicit.map(Solve.solve(_, 'x)).getOrElse(Nil)

  lazy val derivative: Sym =
    Derivative.derive(explicit.getOrElse(sym), 'x)

  lazy val extremas: Seq[Sym] =
    if (explicit.isEmpty) Nil
    else Solve.solve(derivative, 'x)

  lazy val importantPoints: Seq[Sym] =
    all.flatMap{s => Solve.importantPoints(s.sym, 'x)}.flatMap(_.expand)

  lazy val undefinedPoints: Seq[Sym] =
    all.flatMap{s => Solve.undefinedPoints(s.sym, 'x)}.flatMap(_.expand)

  lazy val function: Option[Double => Double] = explicit match {
    case None => None
    case Some(ex) => Some{ (x: Double) => ex.approx(Map('x -> x)) }
  }

  lazy val all: Seq[SuperSym] =
    if (explicit.isEmpty) Nil
    else explicit.get.expand.map(SuperSym(_))

  lazy val props: Seq[(String, Seq[Sym])] = Seq(
    {if (explicit.isDefined && explicit.get != sym)
      Some("Explicit" -> Seq(explicit.get)) else None},
    Option.when(solutions.nonEmpty)("Zeros" -> solutions),
    Option.when(extremas.nonEmpty)("Extremas" -> extremas),
    Some("Derivative" -> Seq(derivative)),
  ).flatten
}
