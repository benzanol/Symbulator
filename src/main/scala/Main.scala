package sympany.main

import org.scalajs.dom
import org.scalajs.dom.document
import scala.scalajs.js.annotation.JSExportTopLevel

object Main {
  def main(args: Array[String]): Unit = {
    sympany.ui.graph.Graph.setup
    sympany.ui.equations.Equations.addEquation()
  }

  def jslog(arg: Any): Unit =
    scalajs.js.Dynamic.global.console.log(arg.asInstanceOf[scalajs.js.Any])
}
