package sympany

// This file contains bindings to allow use of scala functions from javascript

import org.scalajs.dom
import org.scalajs.dom.document

import scala.scalajs.js.annotation.JSExportTopLevel
import scala.scalajs.js

object JsBindings {
  @JSExportTopLevel("parseEquation")
  def jsParseEquation(str: String): Any =
    Parse.parseLatex(str) match {
      case None => null
      case Some(eqn) => eqn
    }
}

object JsUtils {
  def createElement(tag: String, props: (String, Any)*): dom.Element = {
    val e: dom.Element = document.createElement(tag)
    props.foreach{
      case ("innerHTML", html: String) => e.innerHTML = html
      case ("innerText", text: String) => e.innerText = text
      case ("children", cs: Seq[dom.Node]) => e.replaceChildren(cs:_*)
      case (k, v: String) => e.setAttribute(k, v)
      case _ => ()
    }
    return e
  }

  def createLatexElement(latex: String, props: (String, Any)*): dom.Element = {
    val element = createElement("div", props:_*)
    js.Dynamic.global.katexFormatElement(element, latex)
    return element
  }

  def stringToNode(str: String, props: (String, Any)*): dom.Element = {
    if (str.contains('\n')) {
      val el = createElement("div",
        { ("children" -> str.split('\n').toList.map{s => stringToNode(s)}) +: props}:_*
      )

      return el
    }

    val el = createElement("div", "class" -> "mixed-string")
    var latex = false
    var prev = 0

    for (i <- 0 to str.length - 2)

    // Start a latex block
    if (!latex && str.substring(i, i + 2) == "\\(") {
      if (i > 0) el.appendChild(createElement("div",
        "class" -> "mixed-string-text",
        "innerHTML" -> str.substring(prev, i)
      ))
      prev = i + 2
      latex = true

      // Finish a latex block
    } else if (latex && str.substring(i, i + 2) == "\\)") {
      el.appendChild(createLatexElement(str.substring(prev, i),
        "class" -> "mixed-string-latex"
      ))
      prev = i + 2
      latex = false
    }

    // Add the last element
    if (prev < str.length) el.appendChild{
      if (latex) createLatexElement(str.substring(prev),
        "class" -> "mixed-string-latex"
      )
      else createElement("div",
        "class" -> "mixed-string-text",
        "innerHTML" -> str.substring(prev)
      )
    }

    return createElement("div", {("children" -> Seq(el)) +: props}:_*)
  }

}
