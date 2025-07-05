package project3
import org.scalatest._
import org.scalatest.concurrent.{TimeLimitedTests, Signaler, ThreadSignaler}
import org.scalatest.time.{Span, Millis}

class TimedSuite extends FunSuite with TimeLimitedTests {

  val timeLimit = Span(1000, Millis)
  override val defaultTestSignaler: Signaler = ThreadSignaler
}
