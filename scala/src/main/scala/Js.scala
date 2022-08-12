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
  def makeElement(tag: String, props: (String, Any)*): dom.Element = {
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

  def stringToNode(str: String, cls: String = "") =
    makeElement("div",
      "class" -> cls,
      "innerHTML" ->
        (str.replace("\\(", "<p class=\"mq-static\">")
          .replace("\\)", "</p>"))
    )
}
