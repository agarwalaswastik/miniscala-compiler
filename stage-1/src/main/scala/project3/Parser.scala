package project3

// Class used to carry position information within the source code
case class Position(gapLine: Int, gapCol: Int, startLine: Int, startCol: Int, endLine: Int, endCol: Int) {
  override def toString = "pos"
}

class Positioned {
  var pos: Position = _
  def withPos(p: Position) = {
    pos = p
    this
  }
}

object Tokens {
  abstract class Token {
    var pos: Position = _
  }
  
  case object EOF extends Token

  // CHANGED: As we added new types, instead of having a Token called Number,
  // we have a Token called Literal for all constant values.
  case class Literal(x: Any) extends Token
  case class Ident(x: String) extends Token
  case class Keyword(x: String) extends Token
  case class Delim(x: Char) extends Token
}


// Scanner
class Scanner(in: Reader[Char]) extends Reader[Tokens.Token] with Reporter {
  import Tokens._

  // Position handling
  def pos = in.pos
  def input = in.input

  // Current line in the file
  var line = 0

  // lineStarts(i) contains the offset of the i th line within the file
  val lineStarts = scala.collection.mutable.ArrayBuffer(0)

  // Current column in the file
  def column = pos - lineStarts(line)

  // Extract the i th line of code.
  def getLine(i: Int) = {
    val start = lineStarts(i)
    val end = input.indexOf('\n', start)

    if (end < 0)
      input.substring(start)
    else
      input.substring(start, end)
  }

  // Information for the current Position
  var gapLine = 0;
  var gapCol = 0;
  var startLine = 0;
  var startCol = 0;
  var endLine = 0;
  var endCol = 0;

  override def abort(msg: String) = {
    abort(msg, showSource(getCurrentPos()))
  }

  /*
   * Show the line of code and highlight the token at position p
   */
  def showSource(p: Position) = {
    val width = if (p.endLine == p.startLine) (p.endCol - p.startCol) else 0

    val header = s"${p.startLine + 1}:${p.startCol + 1}: "
    val line1 = getLine(p.startLine)
    val line2 = " "*(p.startCol+header.length) + "^"*(width max 1)
    header + line1 + '\n' + line2
  }

  def isAlpha(c: Char) =
    ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')

  def isDigit(c: Char) = '0' <= c && c <= '9'

  def isAlphaNum(c: Char) = isAlpha(c) || isDigit(c)

  def isCommentStart(c1: Char, c2: Char) = c1 == '/' && c2 == '/'

  val isWhiteSpace = Set(' ','\t','\n','\r')

  // Boolean operators start with one of the following characters
  val isBOperator  = Set('<', '>', '!', '=')

  //  Operators start with one of the following characters
  val isOperator   = Set('+','-','*','/') ++ isBOperator

  // List of delimiters
  // TODO: Update this as delimiters are added to our language
  val isDelim      = Set('(',')','=',';','{','}',':','[',']')

  // List of keywords
  // TODO: Update this as keywords are added to our language
  val isKeyword    = Set("if", "else", "val", "var", "while", "def", "=>", "new")

  val isBoolean    = Set("true", "false")

  /*
   * Extract a name from the stream
   *
   * TODO: Handle Boolean literals
   */
  def getName() = {
    val buf = new StringBuilder
    while (in.hasNext(isAlphaNum)) {
      buf += in.next()
    }
    val s = buf.toString
    if (isKeyword(s)) Keyword(s)
    else if (isBoolean(s)) Literal(s.toBoolean)
    else Ident(s)
  }

  /*
   * Extract an operator from the stream
   */
  def getOperator() = {
    val buf = new StringBuilder
    do {
      buf += in.next()
    } while (in.hasNext(isOperator))
    val s = buf.toString
    // "=" is a delimiter, "=>" is a keyword, "==","=+", etc are operators
    if (s == "=") Delim('=')
    else if (isKeyword(s)) Keyword(s)
    else Ident(s)
  }

  /*
   * Extract a number from the stream and return it.
   * Raise an error if there is overflow.
   *
   * NOTE: An integer can be between 0 and (2 to the power 31) minus 1
   */
  val MAX_NUM = s"${(1 << 31) - 1}"
  def getNum() = {
    val num = new StringBuilder
    while (in.hasNext(isDigit)) {
      num += in.next()
    }

    val sNum = num.toString
    if (sNum.length < MAX_NUM.length || (sNum.length == MAX_NUM.length && sNum <= MAX_NUM))
      Literal(sNum.toInt)
    else
      abort(s"integer overflow")
  }

  /*
   * Extract a raw token from the stream.
   * i.e. without position information.
   */
  def getRawToken(): Token = {
    if (in.hasNext(isAlpha)) {
      getName()
    } else if (in.hasNext(isOperator)) {
      getOperator()
    } else if (in.hasNext(isDigit)) {
      getNum()
    } else if (in.hasNext(isDelim)) {
      Delim(in.next())
    } else if (!in.hasNext) {
      EOF
    } else {
      abort(s"unexpected character")
    }
  }

  /*
   * Skip whitespace and comments. Stop at the next token.
   */
  def skipWhiteSpace() = {
    while (in.hasNext(isWhiteSpace) || in.hasNext2(isCommentStart)) {

      // If it is a comment, consume the full line
      if (in.peek == '/') {
        in.next()
        while (in.peek != '\n') in.next()

      }

      // Update file statistics if new line
      if (in.peek == '\n') {
        lineStarts += pos + 1
        line += 1
      }
      in.next()
    }
  }

  def getCurrentPos() = {
    endLine = line; endCol = column
    Position(gapLine,gapCol,startLine,startCol,endLine,endCol)
  }

  /*
   * Extract a token and set position information
   */
  def getToken(): Token = {
    gapLine = line; gapCol = column
    skipWhiteSpace()
    startLine = line; startCol = column
    val tok = getRawToken()
    tok.pos = getCurrentPos()

    tok
  }

  var peek  = getToken()
  var peek1 = getToken()
  def hasNext: Boolean = peek != EOF
  def hasNext(f: Token => Boolean) = f(peek)
  def hasNext2(f: (Token, Token) => Boolean) = f(peek, peek1)
  def next() = {
    val res = peek
    peek = peek1
    peek1 = getToken()
    res
  }
}

class Parser(in: Scanner) extends Reporter {
  import Tokens._

  /*
   * Overloaded methods that show the source code
   * and highlight the current token when reporting
   * an error.
   */
  override def expected(msg: String) = {
    expected(msg, in.showSource(in.peek.pos))
  }

  override def abort(msg: String) = {
    abort(msg, in.showSource(in.peek.pos))
  }

  def error(msg: String, pos: Position): Unit =
    error(msg, in.showSource(pos))

  def warn(msg: String, pos: Position): Unit =
    warn(msg, in.showSource(pos))

  def accept(c: Char) = {
    if (in.hasNext(_ == Delim(c))) in.next()
    else expected(s"'$c'")
  }

  def accept(s: String) = {
    if (in.hasNext(_ == Keyword(s))) in.next()
    else expected(s"'$s'")
  }

  /*
   * Auxilaries functions
   * Test and extract data
   */
  def isName(x: Token) = x match {
    case Ident(x) => true
    case _ => false
  }

  def getName(): (String, Position) = {
    if (!in.hasNext(isName)) expected("Name")
    val pos = in.peek.pos
    val Ident(x) = in.next()
    (x, pos)
  }

  // CHANGED: It was only Number previsously
  def isLiteral(x: Token) = x match {
    case Literal(x) => true
    case _ => false
  }

  def getLiteral(): (Any, Position) = {
    if (!in.hasNext(isLiteral)) expected("Literal")
    val pos = in.peek.pos
    val Literal(x) = in.next()
    (x, pos)
  }

  def getOperator(): (String, Position) = {
    if (!in.hasNext(isOperator)) expected("Operator")
    val pos = in.peek.pos
    val Ident(x) = in.next()
    (x, pos)
  }

  /*
   * Test if the following token is an infix
   * operator with highest precedence
   */
  def isInfixOp(min: Int)(x: Token) = isOperator(x) && (x match {
    case Ident(x) => prec(x) >= min
    case _ => false
  })

  /*
   * Test if the following token is an operator.
   */
  def isOperator(x: Token) = x match {
    case Ident(x) => in.isOperator(x.charAt(0))
    case _ => false
  }

  /*
   * Define precedence of operator.
   * Negative precedence means that the operator can
   * not be used as an infix operator within a simple expression.
   *
   * CHANGED: boolean operators have precedence of 0
   */
  def prec(a: String) = a match { // higher bind tighter
    case "+" | "-" => 1
    case "*" | "/" => 2
    case _ if in.isBOperator(a.charAt(0)) => 0
    case _ => 0
  }

  def assoc(a: String) = a match {
    case "+" | "-" | "*" | "/"  => 1
    case _    => 1
  }
}


/**
 * Definition of our target language.
 *
 * The different nodes of the AST also keep Position information
 * for error handling during the semantic analysis.
 *
 * TODO: Every time you add an AST node, you must also track the position
 */
object Language {
  abstract class Exp {
    var pos: Position = _
    var tp: Type = UnknownType

    def withPos(p: Position) = {
      pos = p
      this
    }

    def withType(pt: Type) = {
      tp = pt
      this
    }
  }

  abstract class Type
  case object UnknownType extends Type
  case class BaseType(v: String) extends Type {
    override def toString = v
  }
  case class FunType(args: List[(String, Type)], rtp: Type) extends Type {
    override def toString = s"(${args mkString ","}) => $rtp"
  }
  case class ArrayType(tp: Type) extends Type

  val IntType = BaseType("Int")
  val UnitType = BaseType("Unit")
  val BooleanType = BaseType("Boolean")

  // Arithmetic
  case class Lit(x: Any) extends Exp
  // CHANGED: instead of creating a node for different operator arity,
  // we use a single node with a list of arguments.
  case class Prim(op: String, args: List[Exp]) extends Exp

  // Immutable variables
  case class Let(x: String, xtp: Type, a: Exp, b: Exp) extends Exp
  case class Ref(x: String) extends Exp

  // Branches
  case class If(cond: Exp, tBranch: Exp, eBranch: Exp) extends Exp

  // Mutable variables
  case class VarDec(x: String, xtp: Type, rhs: Exp, body: Exp) extends Exp
  case class VarAssign(x: String, rhs: Exp) extends Exp

  // While loops
  case class While(cond: Exp, lbody: Exp, body: Exp) extends Exp

  // Functions
  case class LetRec(funs: List[Exp], body: Exp) extends Exp
  case class Arg(name: String, tp: Type, pos: Position)
  case class FunDef(name: String, args: List[Arg], rtp: Type, fbody: Exp) extends Exp
  case class App(f: Exp, args: List[Exp]) extends Exp

  // Arrays
  case class ArrayDec(size: Exp, etp: Type) extends Exp
}

/*
 * The BaseParser class implements all of the functionality implemented in project 2,
 * with the addition of type information.
 *
 * To avoid repeating your effort from project 2, we have implemented all of the
 * parsing for you, excluding the parsing of types. As such...
 *
 * TODO: Implement the two functions that parse types.
 *
 * <type>  ::= <ident>
 * <op>    ::= ['*' | '/' | '+' | '-' | '<' | '>' | '=' | '!']+
 * <bool>  ::= 'true' | 'false'
 * <atom>  ::= <number> | <bool> | '()'
 *           | '('<simp>')'
 *           | <ident>
 *           | '{'<exp>'}'
 * <uatom> ::= [<op>]<atom>
 * <simp>  ::= <uatom>[<op><uatom>]*
 *           | 'if' '('<simp>')' <simp> 'else' <simp>
 *           |  <ident> '=' <simp>
 * <exp>   ::= <simp>
 *           | 'val' <ident>[:<type>] '=' <simp>';' <exp>
 *           | 'var' <ident>[:<type>] '=' <simp>';' <exp>
 *           | 'while' '('<simp>')'<simp>';' <exp>
 */
class BaseParser(in: Scanner) extends Parser(in) {
  import Language._
  import Tokens._

  /******************* Types **********************/

  /*
   * This function extracts the type information from
   * the source code. Raise an error if there is no
   * type information.
   *
   *  This function will only be used to read in a type
   * (i.e. you should not read in a delimiter)
   *
   * TODO: Implement this function
   */
  def parseType: Type = in.peek match {
    case Ident(x) =>
      in.next()
      BaseType(x)
    case _ => expected("type")
  }


  /*
   * This function is parsing a type which can be omitted.
   * If the type information is not in the source code,
   * it returns UnknownType
   *
   * TODO: Implement this function
   */
  def parseOptionalType: Type = in.peek match {
    case Delim(':') =>
      in.next()
      parseType
    case _ => UnknownType
  }

  /******************* Code  **********************/

  /*
   * Parse the full code,
   * verify that there are no unused tokens,
   * and raise an error if there are.
   */
  def parseCode = {
    val res = parseExpression
    if (in.hasNext)
      expected(s"EOF")
    LetRec(Nil, res)
  }

  def parseAtom: Exp = (in.peek, in.peek1) match {
    case (Literal(x), _) =>
      val (_, pos) = getLiteral
      Lit(x).withPos(pos)
    case (Delim('('), Delim(')')) =>
      val pos = in.next().pos
      in.next()
      Lit(()).withPos(pos)
    case (Delim('('), _) =>
      in.next()
      val res = parseSimpleExpression
      accept(')')
      res
    case (Ident(x), _) =>
      val (_, pos) = getName
      Ref(x).withPos(pos)
    case (Delim('{'), _) =>
      accept('{')
      val res = parseExpression
      accept('}')
      res
    case _ =>
      // println(s"Illegal start of simple expression: ${in.peek}, ${in.peek1}")
      abort(s"Illegal start of simple expression")
      
  }

  def parseUAtom: Exp = if (in.hasNext(isOperator)) {
    val (op, pos) = getOperator
    Prim(op, List(parseAtom)).withPos(pos)
  } else {
    parseAtom
  }

  def parseSimpleExpression(min: Int): Exp = {
    var res = parseUAtom
    while (in.hasNext(isInfixOp(min))) {
      val (op, pos) = getOperator
      val nMin = prec(op) + assoc(op)
      val rhs = parseSimpleExpression(nMin)
      res = Prim(op, List(res, rhs)).withPos(pos)
    }
    res
  }

  def parseSimpleExpression: Exp = (in.peek, in.peek1) match {
    case (Ident(x), Delim('=')) =>
      val (_, pos) = getName
      accept('=')
      val rhs = parseSimpleExpression
      VarAssign(x, rhs).withPos(pos)
    case (Keyword("if"), _) =>
      val pos = accept("if").pos
      accept('(')
      val cond = parseSimpleExpression
      accept(')')
      val tBranch = parseSimpleExpression
      accept("else")
      val eBranch = parseSimpleExpression
      If(cond, tBranch, eBranch).withPos(pos)
    case _ => parseSimpleExpression(0)
  }

  def parseExpression: Exp = in.peek match {
    case Keyword("val") =>
      accept("val")
      val (name, pos) = getName
      val tp = parseOptionalType
      accept('=')
      val rhs = parseSimpleExpression
      accept(';')
      val body = parseExpression
      Let(name, tp, rhs, body).withPos(pos)
    case Keyword("var") =>
      accept("var")
      val (name, pos) = getName
      val tp = parseOptionalType
      accept('=')
      val rhs = parseSimpleExpression
      accept(';')
      val body = parseExpression
      VarDec(name, tp, rhs, body).withPos(pos)
    case Keyword("while") =>
      val pos = accept("while").pos
      accept('(')
      val cond = parseSimpleExpression
      accept(')')
      val lBody = parseSimpleExpression
      accept(';')
      val body = parseExpression
      While(cond, lBody, body).withPos(pos)
    case _ => parseSimpleExpression
  }
}

/*
 * We want to make our syntax easier for the programmer to use.
 *
 * For example, instead of writing:
 *
 * var x = 0;
 * var y = 3;
 * let dummy = x = x + 1;
 * y = y + 1
 *
 * We will write
 *
 * var x = 0;
 * var y = 3;
 * x = x + 1;
 * y = y + 1
 *
 * However the AST generated will be the same. The parser will have to create a dummy
 * variable and insert a let binding.
 *
 * We also have some syntactic sugar for the if statement. If the else branch doesn't exist,
 * then the unit literal will be used for that branch.
 *
 * TODO complete the two functions to handle syntactic sugar.
 *
 * <type>  ::= <ident>
 * <op>    ::= ['*' | '/' | '+' | '-' | '<' | '>' | '=' | '!']+
 * <bool>  ::= 'true' | 'false'
 * <atom>  ::= <number> | <bool> | '()'
 *           | '('<simp>')'
 *           | <ident>
 *           | '{'<exp>'}'
 * <uatom> ::= [<op>]<atom>
 * <simp>  ::= <uatom>[<op><uatom>]*
 *           | 'if' '('<simp>')' <simp> ['else' <simp>]
 *           |  <ident> '=' <simp>
 * <exp>   ::= <simp>[;<exp>]
 *           | 'val' <ident>[:<type>] '=' <simp>';' <exp>
 *           | 'var' <ident>[:<type>] '=' <simp>';' <exp>
 *           | 'while' '('<simp>')'<simp>';' <exp>
 */
class SyntacticSugarParser(in: Scanner) extends BaseParser(in) {
  import Language._
  import Tokens._

  // Can be overriden for ; inference
  def isNewLine(x: Token) = x match {
    case Delim(';') => true
    case _ => false
  }

  var next = 0
  def freshName(suf: String = "x") = {
    next += 1
    suf + "$" + next
  }

  override def parseSimpleExpression = in.peek match {
    case Keyword("if") =>
      val pos = accept("if").pos
      accept('(')
      val cond = parseSimpleExpression
      accept(')')
      val tBranch = parseSimpleExpression

      val eBranch = in.peek match {
        case Keyword("else") =>
          accept("else")
          parseSimpleExpression
        case _ =>
          Lit(()).withPos(pos)
      }

      If(cond, tBranch, eBranch).withPos(pos)
    case _ => super.parseSimpleExpression
  }

  override def parseExpression = {
    // NOTE: parse expression terminates when it parse a simples expression.
    // syntax sugar allows to have an other expression after it.
    val res = super.parseExpression
    if (isNewLine(in.peek)) {
      val pos = in.next().pos
      Let(freshName(), UnknownType, res, super.parseExpression).withPos(pos)
    } else {
      res
    }
  }
}

/*
 * The next parser is going to add the necessary mechanic to parse functions.
 *
 * With function come function declaration, function definition and function type.
 *
 * Here are some example of valid syntax:
 *
 * def f(x: Int, k: Int => Int): Int = h(x);
 *
 * h(1)(2, 4);
 *
 * val g: (Int => Int) => Int = 3; g
 *
 * You need to write the function to parse these expression. The job has been splitted
 * in multiple small auxilary functions. Also don't forget that we already have some
 * function doing part of the job in the super class.
 *
 * We also defined the concept of program. All function must be defined first and then
 * the following expression is considered the main.
 *
 * Here is the formalized grammar. Most of it is already handle by the based parser. you
 * only need to handle the new constructs.
 *
 * <type>   ::= <ident>
 *            | <type> '=>' <type>
 *            | '('[<type>[','<type>]*]')' '=>' <type>
 * <op>     ::= ['*' | '/' | '+' | '-' | '<' | '>' | '=' | '!']+
 * <bool>   ::= 'true' | 'false'
 * <atom>   ::= <number> | <bool> | '()'
 *            | '('<simp>')'
 *            | <ident>
 * <tight>  ::= <atom>['('[<simp>[','<simp>]*]')']*
 *            | '{'<exp>'}'
 * <utight> ::= [<op>]<tight>
 * <simp>   ::= <utight>[<op><utight>]*
 *            | 'if' '('<simp>')' <simp> ['else' <simp>]
 *            |  <ident> '=' <simp>
 * <exp>    ::= <simp>[;<exp>]
 *            | 'val' <ident> [':'<type>] '=' <simp>';' <exp>
 *            | 'var' <ident> [':'<type>] '=' <simp>';' <exp>
 *            | 'while' '('<simp>')'<simp>';' <exp>
 * <arg>    ::= <ident>':'<type>
 * <prog>   ::= ['def'<ident>'('[<arg>[','<arg>]*]')'[':' <type>] '=' <simp>';']*<exp>
 */
class FunctionParser(in: Scanner) extends SyntacticSugarParser(in) {
  import Language._
  import Tokens._

  /*
   * This function is an auxilary function that is parsing a list of elements of type T which are
   * separated by 'sep'.
   *
   * 'sep' must be a valid delimiter.
   *
   * 12, 14, 11, 23, 10, 234
   *
   * parseList[Exp](parseAtom, ',', tok => tok match {
   *    case Literal(x: Int) => x < 20;
   *    case _ => false
   *  })
   *
   *  will return the list List(Lit(12), Lit(14), lit(11)) and the next token will be Delim(',')
   *
   *  You don't have to use this function but it may be useful.
   */
  def parseList[T](parseElem: => T, sep: Char, cond: Token => Boolean, first: Boolean = true): List[T] = {
    if (first && cond(in.peek)) {
      if (!first) {
        accept(sep)
      }
      parseElem :: parseList(parseElem, sep, cond, false)
    } else if (!first && in.peek == Delim(sep)) {
      accept(sep)
      if (cond(in.peek)) {
        parseElem :: parseList(parseElem, sep, cond, false)
      } else {
        Nil
      }
    } else {
      Nil
    }
  }


  /*
   * This function parse types.
   *
   * TODO
   */
  override def parseType = (in.peek, in.peek1) match {
    case (Ident(_), Keyword("=>")) =>
      val arg = parseType
      accept("=>")
      val rtp = parseType
      FunType(List(("", arg)), rtp)
    case (Delim('('), _) =>
      in.next()

      val args = parseList[Type](parseType, ',', tok => tok match {
        case Delim(')') => false
        case _ => true
      })

      accept(')')
      accept("=>")
      val rtp = parseType
      FunType(args.map(arg => ("", arg)), rtp)
    case _ => super.parseType
  }

  /*
   * Parse the program and verify that there nothing left
   * to be parsed.
   */
  override def parseCode = {
    val prog = parseProgram
    if (in.hasNext)
      expected(s"EOF")
    prog
  }

  /*
   * Parse one argument (<arg>)
   *
   * TODO: complete the function
   */
  def parseArg: Arg = {
    val (name, pos) = getName
    accept(':')
    val tp = parseType
    Arg(name, tp, pos)
  }

  /*
   * Parse one function.
   * We assume that the first token is Keyword("def")
   *
   * TODO: complete the function
   */
  def parseFunction: Exp = {
    accept("def")
    val (name, pos) = getName
    accept('(')
    val args = parseList[Arg](parseArg, ',', tok => tok match {
      case Delim(')') => false
      case _ => true
    })
    accept(')')
    val rtp = parseOptionalType
    accept('=')
    val fbody = parseSimpleExpression
    FunDef(name, args, rtp, fbody).withPos(pos)
  }

  /*
   * Parse a program. I.e a list of function following
   * by an expression.
   *
   * If there is no functions defined, this function
   * still return a LetRec with an empty function list.
   *
   * TODO: complete the function
   */
  def parseProgram = in.peek match {
    case Keyword("def") =>
      val funcs = parseList[Exp](parseFunction, ';', tok => tok match {
        case Keyword("def") => true
        case _ => false
      })

      LetRec(funcs, parseExpression)
    case _ => LetRec(Nil, parseExpression)
  }

  /*
   * this function is called uatom to avoid reimplementing
   * the previous functions. However it is parsing the <utight>
   * grammar.
   */
  override def parseUAtom = if (in.hasNext(isOperator)) {
    val (op, pos) = getOperator
    Prim(op, List(parseTight)).withPos(pos)
  } else {
    parseTight
  }

  /*
   * Parse <tight> grammar. i.e. function applications.
   *
   * Remember function application is left associative
   * and they all have the same precedence.
   *
   * a(i)(k, j) is parsed to
   *
   * App(App(Ref("a"), List(Ref("i"))), List(Ref("k"), Ref("j")))
   */
  def parseTight = in.peek match {
    case Delim('{') =>
      val pos = in.next().pos
      val res = parseExpression
      accept('}')
      res
    case  _ =>
      var res = parseAtom

      // TODO: complete
      while (in.peek == Delim('(')) {
        val pos = in.next().pos
        val args = parseList[Exp](parseSimpleExpression, ',', tok => tok match {
          case Delim(')') => false
          case _ => true
        })
        accept(')')
        res = App(res, args).withPos(pos)
      }

      res
  }
}

/*
 * We are now going to add heap storage. This kind of storage is persistant
 * between function calls.
 *
 * We are going to use the scala syntax of: new Array[Int](4). However
 * we are not going to implement object. The array behavior will be closer
 * to a C array.
 *
 * In order to access an element the element in the array we use the syntax:
 *
 * val arr = new Array[Int](4);
 * val x = arr(0);
 *
 * And for the update:
 *
 * arr(0) = 3;
 *
 * The acces is going to be parse as a function application but this is fine.
 * For the value update, the parser need to generate a primitive: block-set
 * which take three paramter. 1 the arr, 2 the idx and 3 the value to update.
 *
 * arr(0) = 3;
 *
 * will be parsed to
 * Prim("block-set", List(Ref("arr"), Lit(0), Lit(3)))
 *
 * One idea to parse it it to follow the following process:
 *
 * parse a tight, if it returns a function application with only one argument
 * and the following token is an '=' then you are in the array update situation.
 *
 * TODO: Complete the methods
 *
 * <type>   ::= <ident>
 *            | <type> '=>' <type>
 *            | '('[<type>[','<type>]*]')' '=>' <type>
 *            | 'Array' '[' <type> ']'
 * <op>     ::= ['*' | '/' | '+' | '-' | '<' | '>' | '=' | '!']+
 * <bool>   ::= 'true' | 'false'
 * <atom>   ::= <number> | <bool> | '()'
 *            | '('<simp>')'
 *            | <ident>
 * <tight>  ::= <atom>['('[<simp>[','<simp>]*]')']*['('<simp>')' '=' <simp>]
 *            | '{'<exp>'}'
 * <utight> ::= [<op>]<tight>
 * <simp>   ::= <utight>[<op><utight>]*
 *            | 'if' '('<simp>')' <simp> ['else' <simp>]
 *            |  <ident> '=' <simp>
 *            | 'new' 'Array' '['<type> ']' '('<simpl>')' // type not optional '[' is the delimiter.
 * <exp>    ::= <simp>[;<exp>]
 *            | 'val' <ident> [':'<type>] '=' <simp>';' <exp>
 *            | 'var' <ident> [':'<type>] '=' <simp>';' <exp>
 *            | 'while' '('<simp>')'<simp>';' <exp>
 * <arg>    ::= <ident>':'<type>
 * <prog>   ::= ['def'<ident>'('[<arg>[','<arg>]*]')'[':' <type>] '=' <simp>';']*<exp>
 */
class ArrayParser(in: Scanner) extends FunctionParser(in) {
  import Language._
  import Tokens._

  override def parseType = in.peek match {
    case Ident("Array") => 
      in.next()
      accept('[')
      val tp = parseType
      accept(']')
      ArrayType(tp)
    case _ => super.parseType
  }

  /*
   * Parse array update
   *
   * TODO
   */
  override def parseTight = {
    val res = super.parseTight
    val pos = res.pos

    if (in.peek != Delim('=')) {
      res
    } else {
      res match {
        case App(f, args) =>
          if (args.length == 1) {
            in.next()
            val rhs = parseSimpleExpression
            Prim("block-set", List(f, args(0), rhs)).withPos(pos)
          } else {
            res
          }
        case _ => res
      }
    }
  }

  /*
   * Parse array declaration
   *
   * TODO
   */
  override def parseSimpleExpression = in.peek match {
    case Keyword("new") =>
      val pos = in.next().pos
      val tp = parseType

      val etp = tp match {
        case ArrayType(x) => x
        case _ =>
          expected("Array");
          UnknownType
      }

      accept('(')
      val size = parseSimpleExpression
      accept(')')

      ArrayDec(size, etp).withPos(pos)
    case _ => super.parseSimpleExpression
  }
}
