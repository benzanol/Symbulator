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
    Graph.setGraphs(handlers.flatMap(_.eqn).flatMap(_.explicit))

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
  def updateLatex(id: String, latex: String): Unit = {
    handlers.find(_.id == id) match {
      case Some(h) => {
        h.updateLatex(latex)
        updateGraphs
      }
      case None => throw new Exception(s"Handler $id not found")
    }
  }

  // Get the list of properties that should be displayed below an equation
  def expressionProperties(sym: Sym): Seq[(String, Seq[Sym])] = Seq(
    Some("Simplified" -> Seq(sym.simple)),
    {if (sym.explicit.isDefined && sym.explicit.get != sym.simple)
      Some("Explicit" -> Seq(sym.explicit.get)) else None},
    Some("Zeros" -> sym.zeros),
    Some("Extremas" -> sym.extremas),
    //Some("Undefined" -> sym.undefined),
    //Some("Important" -> sym.important),
    Some("Derivative" -> Seq(sym.derivative)),
    //sym.integral.map("Integral" -> Seq(_)),
  ).flatten.filter(_._2.nonEmpty)
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
    if (newLatex == this.latex) return

    this.latex = newLatex
    this.eqn = Parse.parseLatex(newLatex)

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
            val txt = text.replace("\\", "\\\\")
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
