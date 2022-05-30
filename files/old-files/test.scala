import $ivy.`org.scala-lang.modules::scala-parallel-collections:1.0.0`
import scala.collection.parallel.immutable._

ParVector(2, 3, 4).map(_ + 1)
