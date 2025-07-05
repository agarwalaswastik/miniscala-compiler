package project3

import java.io._
import org.scalatest._

class ParserTest extends TimedSuite {
  import Language._

  def scanner(src: String) = new Scanner(new BaseReader(src, '\u0000'))

  def testBaseParser(op: String, res: Exp) = {
    val gen = new BaseParser(scanner(op))
    val ast = gen.parseCode
    assert(ast == LetRec(Nil, res), "Invalid result")
  }

  def testSyntacticSugar(op: String, res: Exp) = {
    val gen = new SyntacticSugarParser(scanner(op))
    val ast = gen.parseCode
    assert(ast == LetRec(Nil, res), "Invalid result")
  }

  def testFunctionParser(op: String, funcs: List[Exp], res: Exp) = {
    val gen = new FunctionParser(scanner(op))
    val ast = gen.parseCode
    assert(ast == LetRec(funcs, res), "Invalid result")
  }

  test("SingleDigit") {
    testBaseParser("1", Lit(1))
  }

  test("GenericPrecedence") {
    testBaseParser("2-4*3", Prim("-", List(Lit(2), Prim("*", List(Lit(4), Lit(3))))))
  }

  test("ParseType") {
    testBaseParser("val x: Int = 1; 2", Let("x", IntType, Lit(1), Lit(2)))
  }

  test("ParseOptionalType") {
    testBaseParser("val x = 1; 2", Let("x", UnknownType, Lit(1), Lit(2)))
  }

  test("ParseBooleanLiteralWithType") {
    testBaseParser("val x: Boolean = false; x", Let("x", BooleanType, Lit(false), Ref("x")))
  }

  test("ParseBooleanLiteralWithoutType") {
    testBaseParser("var x = true; x", VarDec("x", UnknownType, Lit(true), Ref("x")))
  }

  test("UnitType") {
    testBaseParser("var x = (); x", VarDec("x", UnknownType, Lit(()), Ref("x")))
  }

  test("SyntacticSugarDummy") {
    testSyntacticSugar("var x: Int = 1; val y = 2; x = x + y; x",
       VarDec("x", IntType, Lit(1),
        Let("y", UnknownType, Lit(2), 
          Let("x$1", UnknownType, VarAssign("x", Prim("+", List(Ref("x"), Ref("y")))),
            Ref("x")))))
  }

  test("SyntacticSugarNoElse") {
    testSyntacticSugar("var x = 5; if (2 > 0) x = x - 1; val y = x * 5; x",
      VarDec("x",UnknownType,Lit(5),Let("x$1",UnknownType,If(Prim(">",List(Lit(2), Lit(0))),VarAssign("x",Prim("-",List(Ref("x"), Lit(1)))),Lit(())),Let("y",UnknownType,Prim("*",List(Ref("x"), Lit(5))),Ref("x")))))
  }

  test("FunctionParserWithRtp") {
    testFunctionParser("def sqr(n: Int): Int = { x * x }; sqr(5)",
      List(),
      Lit(()))
  }

  test("FunctionParserDoubleApply") {
    testFunctionParser("def sqr(n: Int): Int = { x * x }; sqr(sqr(5))",
      List(),
      Lit(()))
  }

  test("FunctionDoubleParserDoubleApply") {
    testFunctionParser("def sqr(n: Int): Int = { x * x }; def sqr1(n: Int): Int = { x * x }; sqr(sqr(5))",
      List(),
      Lit(()))
  }

  test("ParseCallback") {
    testFunctionParser("def apply(f: (Int) => Int) = { f(5) }; def sqr(n: Int): Int = { x * x }; apply(sqr)",
      List(),
      Lit(()))
  }
}
