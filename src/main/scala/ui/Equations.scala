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
    Graph.setGraphs(handlers.flatMap(_.eqn).flatMap(_.explicit),
      handlers.flatMap(_.eqn).flatMap{ e =>
        expressionProperties(e).flatMap(_._2).collect{
          case SymPoint(x, y) => (e, x, y)
        }
      })

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
  def addEquation() {
    val h = new EquationHandler()
    handlers :+= h
    updateEquations()

    // Shift focus to the equation
    js.eval(s"MQ(document.getElementById('eqn-${h.id}')).focus()")
  }

  @JSExportTopLevel("insertEquation")
  def insertEquation(s: String) {
    val h = new EquationHandler()
    h.eqnElem.innerText = s
    h.eqnElem.setAttribute("class", "mq-static mq-dynamic")
    h.updateLatex(s)
    handlers :+= h
    updateEquations()
    updateGraphs
    js.eval("formatStaticEquations()")
  }

  @JSExportTopLevel("deleteEquation")
  def deleteEquation(id: String) {
    handlers = handlers.filter(_.id != id)
    updateEquations()
    updateGraphs
  }

  // Update the handler that has the specified id to have a new equation
  @JSExportTopLevel("updateLatex")
  def updateLatex(id: String, latex: String) {
    handlers.find(_.id == id) match {
      case Some(h) => {
        h.updateLatex(latex)
        updateGraphs
      }
      case None => throw new Exception(s"Handler $id not found")
    }
  }

  @JSExportTopLevel("updateProps")
  def updateProps() {
    for (h <- this.handlers)
      h.update()

    updateGraphs
  }

  def pointString(f: Sym, x: Sym): Seq[SymPoint] =
    x.simple.expand.map{ x1 =>
      SymPoint(x1.simple, f.replaceExpr('x, x1.simple).simple)
    }

  case class SymPoint(x: Sym, y: Sym) extends Sym {
    def instance(args: Sym*) = SymPoint(args(0), args(1))
    def exprs = Seq(x, y)
  }

  // Get the list of properties that should be displayed below an equation
  def expressionProperties(sym: Sym): Seq[(String, Seq[Sym])] = Seq(
    Some("Simplified", Seq(sym.simple)),
    {if (sym.explicit.isDefined && sym.explicit.get != sym.simple)
      Some("Explicit", Seq(sym.explicit.get)) else None},
    Some("Zeros", sym.zeros.map{ (a: Sym) => SymPoint(a, SymInt(0)) }),
    Some("Mins and Maxes", sym.extremas.flatMap(pointString(sym, _))),
    Some("Inflection Points", sym.derivative.extremas.flatMap(pointString(sym, _))),
    Some("Holes", sym.undefined.map(SymVertical)),
    Some("Derivative", Seq(sym.derivative)),
    //sym.integral.map("Integral", Seq(_)),
  ).flatten
    .filter{ case (n, seq) => (n == "Explicit").||(
      try {
        document.getElementById(n.toLowerCase.replace(' ', '-') + "-chk")
          .asInstanceOf[dom.HTMLInputElement].checked
      } catch {
        case e: Throwable => false
      }
    )}.map{t => (t._1, t._2.map(_.simple))}
    .map{t => (t._1, t._2.filter(_.isFinite))}
    .filter(_._2.nonEmpty)
}

import Equations.makeElement

class EquationHandler() {
  val id = scala.util.Random.nextInt().abs.toString

  val rootElem = makeElement("div", "class" -> "eqn-div",   "id" -> s"div-$id",  "hid" -> id)

  val delButton = makeElement("button", "innerText" -> "×",
    "class" -> "delete-equation-button", "id" -> s"btn-$id",
    "onclick" -> s"deleteEquation('$id')")
  rootElem.appendChild(delButton)

  val eqnElem  = makeElement("p", "class" -> "mq-dynamic",  "id" -> s"eqn-$id",  "hid" -> id)
  val propElem = makeElement("div", "class" -> "eqn-props", "id" -> s"prop-$id", "hid" -> id)
  rootElem.appendChild(eqnElem)
  rootElem.appendChild(propElem)

  js.Dynamic.global.formatEquation(eqnElem)

  var latex: String = ""
  var eqn: Option[Sym] = None

  def updateLatex(newLatex: String): Unit = {
    this.latex = newLatex
    this.eqn = Parse.parseLatex(newLatex)
    this.update()
  }

  def update() {
    propElem.replaceChildren()

    if (eqn.isDefined)
      for (p <- Equations.expressionProperties(eqn.get)) {
        // Create a div for the property and add it to the property list
        val div = Equations.makeElement("div", "class" -> "eqn-prop")
        propElem.appendChild(div)

        // Add the description and equations of the property to the div
        div.appendChild(makeElement("p", "class" -> "prop-name", "innerText" -> p._1))
        for (i <- 0 until p._2.length) {
          val text = p._2(i).toLatex + (if (i == p._2.length - 1) "" else ",")

          val divv = makeElement("div",
            "white-space" -> "nowrap",
            "overflow" -> "hidden",
            "text-overflow" -> "clip",
          )

          if (p._2.length == 1) {
            val txt = (p._2.head match {
              case Equations.SymPoint(x, y) => y.simple.toLatex
              case e => e.simple.toLatex
            }).replace("\\", "\\\\")

            val btn = makeElement("button", "innerText" -> "+", "class" -> "plus-btn",
              "onclick" -> s"insertEquation('$txt')")
            divv.appendChild(btn)
            divv.appendChild(makeElement("span", "innerText" -> " "))
          }

          val el = makeElement("p", "class" -> "mq-static", "innerText" -> text)
          divv.appendChild(el)

          div.appendChild(divv)

          val c = makeElement("p")
        }
      }

    // Format the static equations as latex with mathquill
    js.eval("formatStaticEquations()")
    //js.eval("setTimeout(formatStaticEquations, 0)")
  }
}
