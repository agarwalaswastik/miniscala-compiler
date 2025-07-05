package object miniscala {
  private def fixedPoint[T](start: T, maxIters: Option[Int])(f: T=>T): T = {
    val approx = Stream.iterate(start, maxIters getOrElse Integer.MAX_VALUE)(f)
    // val (improv, stable) = ((approx zip approx.tail) span (p => p._1 != p._2))
    val pairs = approx zip approx.tail
    val improv = pairs.takeWhile { case (a, b) => a != b }
    val stable = pairs.dropWhile { case (a, b) => a != b }
    if (improv.isEmpty) stable.head._1 else improv.last._2
  }

  private[miniscala] def fixedPoint[T](start: T)(f: T=>T): T =
    fixedPoint(start, None)(f)

  private[miniscala] def fixedPoint[T](start: T, maxIters: Int)(f: T=>T): T =
    fixedPoint(start, Some(maxIters))(f)
}
