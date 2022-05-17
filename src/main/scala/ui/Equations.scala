package sympany.ui.equations

import scala.util.chaining._

import org.scalajs.dom
import org.scalajs.dom.document
import org.scalajs.dom.window
import scala.scalajs.js
import scala.scalajs.js.annotation.JSExportTopLevel

import sympany.symbolics._
import sympany.main.Main.jslog
import sympany.ui.graph.Graph
import sympany.parse.Parse.parseLatex
import sympany.symbolics.Sym
import sympany.math.Simplify.simplify
import sympany.math.Derivative.derivative
import sympany.math.Solve.zero

object Equations {
  // Detect when keys are pressed
  document.addEventListener("keyup", (event: dom.KeyboardEvent) => {
    event.keyCode match {
      // If enter key pressed, add a new equation below the current one
      case 13 => {
        try {
          val current = window.getSelection().anchorNode.parentNode
          if (current.attributes("class").value.contains("mathquill"))
            addEquation(current.attributes("id").value)
        } catch {
          case e: Throwable => addEquation()
        }
      }
        
      //  Ctrl+shift+delete removes the current equation
      case 8 if (event.ctrlKey && event.shiftKey) => {
        val current = window.getSelection().anchorNode.parentNode
        deleteEquation(current.attributes("id").value)
      }
        
      // If control up or down is pressed, move in that direction
      case 38 | 40 if (event.ctrlKey) => {
        val current = window.getSelection().anchorNode.parentNode
        val div = current.parentNode
        val sibling = if (40 == event.keyCode) div.nextSibling else div.previousSibling
        if (current.attributes("class").value.contains("mathquill") &&
          sibling != null && sibling.hasChildNodes())
          js.eval(s"focusEquation('${sibling.childNodes(1).attributes("id").value}')")
      }
        
      case _ => ()
    }
  })
  
  @JSExportTopLevel("addEquation")
  def addEquation(targetId: String = ""): Unit = {
    // Create the mathquill equation element
    val eqn = document.createElement("p")
    val eqnId = s"eqn-${(new scala.util.Random).nextInt.abs}"
    eqn.setAttribute("class", "mathquill")
    eqn.setAttribute("id", eqnId)
    
    // Create the button that will remove the equation
    val btn = document.createElement("button")
    btn.setAttribute("class", "delete-equation-button")
    btn.setAttribute("onclick", s"deleteEquation('$eqnId')")
    btn.innerHTML = "×"
    
    // Create the div that will store the equation properties
    val infoDiv = document.createElement("div")
    infoDiv.setAttribute("class", "eqn-info")
    
    // Create the div that will store all elements of a single equation
    val div = document.createElement("div")
    div.setAttribute("class", "equation-div")
    div.appendChild(btn)
    div.appendChild(eqn)
    div.appendChild(infoDiv)
    div.appendChild(document.createElement("br"))
    
    // Add the equation div to the list of equations
    if (targetId == "" || document.getElementById(targetId) == null)
      document.getElementById("equations").appendChild(div)
    else
      // Has to use js.eval since scalajs is missing `parentElement`
      js.eval(s"document.getElementById('$targetId').parentElement")
        .asInstanceOf[dom.Element].after(div)
    
    // Call mathquill to make the new element an equation (defined in index.html)
    js.eval("formatEquations()")
    
    js.eval(s"focusEquation('$eqnId')")
  }
  
  @JSExportTopLevel("deleteEquation")
  def deleteEquation(id: String): Unit = {
    val eqns = document.getElementById("equations")
    val eqnDiv = document.getElementById(id).parentNode
    
    try {
      // Select the next equation if possible, or the previous equation if possible
      val sibling =
        if (eqnDiv.nextSibling == null) eqnDiv.previousSibling
        else eqnDiv.nextSibling
      
      if (sibling != null && sibling.hasChildNodes())
        js.eval(s"focusEquation('${sibling.childNodes(1).attributes("id").value}')")
    } catch { case e: Error => () }
    
    
    // Remove the previously selected node from the list
    eqns.removeChild(eqnDiv)
    
    // Recalculate the equations and redraw the graph
    
    updateEquations
    Graph.drawGraph
  }
  
  @JSExportTopLevel("updateEquations")
  def updateEquations() {
    //val eqnDiv = document.getElementById(id).parentNode
    //jslog(id)
    val divs: Seq[dom.Element] = document.getElementsByClassName("equation-div").toSeq
    val infos = divs.map{ e: dom.Element => e.querySelector(".eqn-info") }
    
    val eqns: Seq[String] = divs.map{ e: dom.Element =>
      val id = e.querySelector(".mathquill").getAttribute("id")
      js.eval(s"getLatexEquation('$id')").toString
    }
    val syms: Seq[Option[Sym]] = eqns.map(parseLatex)
    
    val graphs: Seq[Sym] = (0 until syms.length).flatMap{i => syms(i) match {
      case None => infos(i).innerText = "\n" ; None
      case Some(e: Sym) => renderEquation(e, infos(i))
    }}
    
    Graph.setExpressions(graphs)
    
    js.eval("formatStaticEquations();")
  }
  
  def renderEquation(expr: Sym, div: dom.Element): Option[Sym] = {
    div.replaceChildren()

    var e = expr

    if (Sym.containsExpr(expr, SymVar('y))) {
      val explicit = zero(e, 'y).headOption
      
      if (explicit.isDefined) {
        appendEquation(div, "p", "Explicit: \\quad y = " + explicit.get.toLatex.pipe(Sym.noParens))
        e = explicit.get
        
      } else return None
    }

    val deriv = derivative(e, 'x)
    appendEquation(div, "p", "Derivative: \\quad " + deriv.toLatex.pipe(Sym.noParens))
    
    val fZeros = zero(e, 'x)
      .map(Sym.replaceExpr(_, SymVar('y), SymInt(0)))
      .map(simplify).map(_.toLatex).map(Sym.noParens)
    
    if (fZeros.nonEmpty)
      appendEquation(div, "p", "Zeros: \\quad " + fZeros.reduceLeft(_ + ", \\quad " + _))
    
    val extremas = zero(deriv, 'x).map(_.toLatex).map(Sym.noParens)
    if (extremas.nonEmpty)
      appendEquation(div, "p", "Extremas: \\quad " + extremas.reduceLeft(_ + ", \\quad " + _))
    
    return Some(e)
  }
  
  def appendEquation(existing: dom.Element, elem: String, text: String): Unit = {
    val e = document.createElement(elem)
    e.innerText = text
    e.setAttribute("class", "mq-static")
    
    existing.appendChild(e)
    existing.appendChild(document.createElement("br"))
  }
}
