package miniscala

import scala.collection.mutable.{ Map => MutableMap }

abstract class CPSOptimizer[T <: CPSTreeModule { type Name = Symbol }]
  (val treeModule: T) {
  import treeModule._

  def apply(tree: Tree): Tree = {
    val simplifiedTree = fixedPoint(tree)(shrink)
    val maxSize = (size(simplifiedTree) * 1.5).toInt
    fixedPoint(simplifiedTree, 8) { t => inline(t, maxSize) }
  }

  /* Counts how many times a symbol is encountered as an applied function,
   * and how many as a value
   */
  private case class Count(applied: Int = 0, asValue: Int = 0)

  /* Local state of the optimization
   * Note: To update the state, use the with* methods
   */
  private case class State(
    /* How many times a symbol is encountered in the Tree. Note: The
     * census for the whole program gets calculated once in the
     * beginning, and passed to the initial state.
     */
    census: Map[Name, Count],
    // Name substitution that needs to be applied to the current tree
    subst: Substitution[Name] = Substitution.empty,
    // Names that have a constant value
    lEnv: Map[Name, Literal] = Map.empty,
    // The inverse of lEnv
    lInvEnv: Map[Literal, Name] = Map.empty,
    // A known block mapped to its tag and length
    bEnv: Map[Name, (Literal, Name)] = Map.empty,
    // ((p, args) -> n2) is included in eInvEnv iff n2 == p(args)
    // Note: useful for common-subexpression elimination
    eInvEnv: Map[(ValuePrimitive, Seq[Name]), Name] = Map.empty,
    // Continuations that will be inlined
    cEnv: Map[Name, CntDef] = Map.empty,
    // Functions that will be inlined
    fEnv: Map[Name, FunDef] = Map.empty) {

    // Checks whether a symbol is dead in the current state
    def dead(s: Name): Boolean =
      census get s map (_ == Count(applied = 0, asValue = 0)) getOrElse true
    // Checks whether a symbols is applied exactly once as a function
    // in the current State, and never used as a value
    def appliedOnce(s: Name): Boolean =
      census get s map (_ == Count(applied = 1, asValue = 0)) getOrElse false

    // Addas a substitution to the state
    def withSubst(from: Name, to: Name): State =
      copy(subst = subst + (from -> to))
    // Adds a Seq of substitutions to the state
    def withSubst(from: Seq[Name], to: Seq[Name]): State =
      copy(subst = subst ++ (from zip to))

    // Adds a constant to the State
    def withLit(name: Name, value: Literal) =
      copy(lEnv = lEnv + (name -> value), lInvEnv = lInvEnv + (value -> name))
    // Adds a block to the state
    def withBlock(name: Name, tag: Literal, size: Name) =
      copy(bEnv = bEnv + (name -> (tag, size)))
    // Adds a primitive assignment to the state
    def withExp(name: Name, prim: ValuePrimitive, args: Seq[Name]) =
      copy(eInvEnv = eInvEnv + ((prim, args) -> name))
    // Adds an inlinable continuation to the state
    def withCnt(cnt: CntDef) =
      copy(cEnv = cEnv + (cnt.name -> cnt))
    // Adds a Seq of inlinable continuations to the state
    def withCnts(cnts: Seq[CntDef]) =
      (this /: cnts) (_.withCnt(_))
    // Adds an inlinable function to the state
    def withFun(fun: FunDef) =
      copy(fEnv = fEnv + (fun.name -> fun))
    // Adds a Seq of inlinable functions to the state
    def withFuns(funs: Seq[FunDef]) =
      (this /: funs) (_.withFun(_))
    /*
     * The same state, with emply inverse environments.
     * Use this when entering a new FunDef, because assigned Name's may
     * come out of scope during hoisting.
     */
    def withEmptyInvEnvs =
      copy(lInvEnv = Map.empty, eInvEnv = Map.empty)
  }

  // Shrinking optimizations

  private def shrink(tree: Tree): Tree = {
    def shrinkT(tree: Tree)(implicit s: State): Tree = tree match {

      case LetL(name, value, body) =>
        if (s.dead(name)) {
          shrinkT(body)

        } else if (s.lInvEnv.contains(value)) {
          val ss = s.withSubst(name, s.lInvEnv(value))
          shrinkT(body.subst(ss.subst))(ss)

        } else {
          LetL(name, value, shrinkT(body)(s.withLit(name, value)))
        }
        
      case LetP(name, prim, args, body) =>
        if (s.dead(name) && !impure(prim)) {
          shrinkT(body)

        } else if (prim == identity) {
            val ss = s.withSubst(name, args(0))
            shrinkT(body.subst(ss.subst))(ss)

        } else if (blockAllocTag.isDefinedAt(prim)) {
          val ss = s.withBlock(name, blockAllocTag(prim), args(0));
          LetP(name, prim, args, shrinkT(body)(ss))

        } else if (prim == blockTag) {
          if (s.bEnv.contains(args(0))) {
            val (tag, _) = s.bEnv(args(0))
            LetL(name, tag, shrinkT(body));
          } else {
            LetP(name, prim, args, shrinkT(body)(s.withExp(name, prim, args)))
          }

        } else if (prim == blockLength) {
          if (s.bEnv.contains(args(0))) {
            val (_, lengthName) = s.bEnv(args(0))
            val ss = s.withSubst(name, lengthName)
            shrinkT(body.subst(ss.subst))(ss)

          } else {
            LetP(name, prim, args, shrinkT(body)(s.withExp(name, prim, args)))
          }

        } else if (s.eInvEnv.contains((prim, args)) && !impure(prim) && !unstable(prim)) {
          val ss = s.withSubst(name, s.eInvEnv((prim, args)))
          shrinkT(body.subst(ss.subst))(ss)

        } else if (args.forall(s.lEnv.contains(_)) && !impure(prim) && !unstable(prim)) {
          val literals = args.map { arg => s.lEnv(arg) }
          LetL(name, vEvaluator(prim, literals), shrinkT(body))

        } else if (args.length == 2 && !impure(prim) && !unstable(prim)) {
          if (s.lEnv.contains(args(0))) {
            if (leftNeutral((s.lEnv(args(0)), prim))) {
              val ss = s.withSubst(name, args(1))
              shrinkT(body.subst(ss.subst))(ss)

            } else if (leftAbsorbing((s.lEnv(args(0)), prim))) {
              val ss = s.withSubst(name, args(0))
              shrinkT(body.subst(ss.subst))(ss)

            } else {
              LetP(name, prim, args, shrinkT(body)(s.withExp(name, prim, args)))
            }

          } else if (s.lEnv.contains(args(1))) {
            if (rightNeutral((prim, s.lEnv(args(1))))) {
              val ss = s.withSubst(name, args(0))
              shrinkT(body.subst(ss.subst))(ss)

            } else if (rightAbsorbing((prim, s.lEnv(args(1))))) {
              val ss = s.withSubst(name, args(1))
              shrinkT(body.subst(ss.subst))(ss)

            } else {
              LetP(name, prim, args, shrinkT(body)(s.withExp(name, prim, args)))
            }

          } else if (args(0) == args(1) && sameArgReduce.isDefinedAt(prim)) {
            LetL(name, sameArgReduce(prim), shrinkT(body))

          } else {
            LetP(name, prim, args, shrinkT(body)(s.withExp(name, prim, args)))
          }

        } else {
          LetP(name, prim, args, shrinkT(body)(s.withExp(name, prim, args)))
        }

      case LetC(cnts, body) =>
        val liveCnts = cnts
                    .filter(cnt => !s.dead(cnt.name))
                    .map { cnt =>
                      val ss = s.withCnts(
                        cnts.filter(c => s.appliedOnce(c.name) && c != cnt)
                      )

                      CntDef(cnt.name, cnt.args, shrinkT(cnt.body)(ss))
                    }

        val ss = s.withCnts(
          cnts.filter(cnt => s.appliedOnce(cnt.name))
        )

        if (liveCnts.isEmpty)
          shrinkT(body)(ss)
        else
          LetC(liveCnts, shrinkT(body)(ss))

      case LetF(funs, body) =>
        val liveFuns = funs
                    .filter(fun => !s.dead(fun.name))
                    .map { fun => 
                      val ss = s.withFuns(
                        funs.filter(f => s.appliedOnce(f.name) && f != fun)
                      )

                      FunDef(fun.name, fun.retC, fun.args, shrinkT(fun.body)(ss.withEmptyInvEnvs))
                    }

        val ss = s.withFuns(
          funs.filter(fun => s.appliedOnce(fun.name))
        )

        if (liveFuns.isEmpty)
          shrinkT(body)(ss)
        else
          LetF(liveFuns, shrinkT(body)(ss))

      case AppC(cnt, args) =>
        if (s.cEnv.contains(cnt)) {
          val cntDef = s.cEnv(cnt)
          val ss = s.withSubst(cntDef.args, args)
          shrinkT(cntDef.body.subst(ss.subst))(ss)

        } else {
          tree
        }

      case AppF(fun, retC, args) => 
        if (s.fEnv.contains(fun)) {
          val funDef = s.fEnv(fun)
          val ss = s.withSubst(funDef.retC, retC).withSubst(funDef.args, args)
          shrinkT(funDef.body.subst(ss.subst))(ss)

        } else {
          tree
        }

      case If(cond, args, thenC, elseC) =>
        if (args.forall(s.lEnv.contains(_))) {
          val literals = args.map { arg => s.lEnv(arg) }
          val result = cEvaluator(cond, literals)

          if (result) AppC(thenC, Seq())
          else AppC(elseC, Seq())

        } else if (args.length == 2 && args(0) == args(1)) {
          val result = sameArgReduceC(cond)

          if (result) AppC(thenC, Seq())
          else AppC(elseC, Seq())

        } else {
          tree
        }

      case Halt(arg) => tree

      case _ => ???
    }

    shrinkT(tree)(State(census(tree)))
  }

  // (Non-shrinking) inlining

  private def inline(tree: Tree, maxSize: Int): Tree = {
    val fibonacci = Seq(1, 2, 3, 5, 8, 13)

    val trees = Stream.iterate((0, tree), fibonacci.length + 1) { case (i, tree) =>
      val funLimit = fibonacci(i)
      val cntLimit = i

      def inlineT(tree: Tree)(implicit s: State): Tree = tree match {

        case LetL(name, value, body) =>
          LetL(name, value, inlineT(body)(s.withLit(name, value)))

        case LetP(name, prim, args, body) =>
          LetP(name, prim, args, inlineT(body)(s.withExp(name, prim, args)))

        case If(cond, args, thenC, elseC) => tree

        case Halt(arg) => tree

        case LetC(cnts, body) =>
          val liveCnts = cnts
                      .filter(cnt => !s.dead(cnt.name))
                      .map { cnt => 
                        val ss = s.withCnts(
                          cnts.filter(c => size(c.body) <= cntLimit && c != cnt)
                        )

                        CntDef(cnt.name, cnt.args, inlineT(cnt.body)(ss))
                      }

          val ss = s.withCnts(
            cnts.filter(cnt => size(cnt.body) <= cntLimit)
          )

          if (liveCnts.isEmpty)
            inlineT(body)(ss)
          else
            LetC(liveCnts, inlineT(body)(ss))

        case LetF(funs, body) =>
          val liveFuns = funs
                      .filter(fun => !s.dead(fun.name))
                      .map { fun => 
                        val ss = s.withFuns(
                          funs.filter(f => size(f.body) <= funLimit && f != fun)
                        )

                        FunDef(fun.name, fun.retC, fun.args, inlineT(fun.body)(ss.withEmptyInvEnvs))
                      }

          val ss = s.withFuns(
            funs.filter(fun => size(fun.body) <= funLimit)
          )

          if (liveFuns.isEmpty)
            inlineT(body)(ss)
          else
            LetF(liveFuns, inlineT(body)(ss))

        case AppC(cnt, args) =>
          if (s.cEnv.contains(cnt)) {
            val cntDef = s.cEnv(cnt)
            val ss = s.withSubst(cntDef.args, args)
            
            val tBody = cntDef.body.subst(ss.subst)

            freshenLabels(tBody)(Map[Name, Name]())

          } else {
            tree
          }

        case AppF(fun, retC, args) => 
          if (s.fEnv.contains(fun)) {
            val funDef = s.fEnv(fun)
            val ss = s.withSubst(funDef.retC, retC).withSubst(funDef.args, args)
            val tBody = funDef.body.subst(ss.subst)

            freshenLabels(tBody)(Map[Name, Name]())

          } else {
            tree
          }

        case _ => tree
      }

      (i + 1, fixedPoint(inlineT(tree)(State(census(tree))))(shrink))
    }

    trees.takeWhile{ case (_, tree) => size(tree) <= maxSize }.last._2
  }

  // Fresh labels for entire tree
  private def freshenLabels(tree: Tree)
    (implicit transformed: Map[Name, Name]): Tree = tree match {
    
    case LetL(name, value, body) =>
      val newName = Symbol.fresh(s"${name}")
      LetL(newName, value, freshenLabels(body)(transformed + (name -> newName)))

    case LetP(name, prim, args, body) =>
      val newName = Symbol.fresh(s"${name}")
      val newArgs = args.map(arg => transformed.getOrElse(arg, arg))
      LetP(newName, prim, newArgs, freshenLabels(body)(transformed + (name -> newName)))

    case LetC(cnts, body) =>
      var newTransformed = transformed

      cnts.foreach { cnt =>
        val newContName = Symbol.fresh(s"${cnt.name}")
        newTransformed = newTransformed + (cnt.name -> newContName)

        cnt.args.foreach { arg =>
          val newArgName = Symbol.fresh(s"${arg}")
          newTransformed = newTransformed + (arg -> newArgName)
        }
      }

      val newCnts = cnts.map { cnt =>
        val newArgs = cnt.args.map(newTransformed(_))
        CntDef(newTransformed(cnt.name), newArgs, freshenLabels(cnt.body)(newTransformed))
      }

      LetC(newCnts, freshenLabels(body)(newTransformed))

    case LetF(funs, body) =>
      var newTransformed = transformed

      funs.foreach { fun =>
        val newFunName = Symbol.fresh(s"${fun.name}")
        newTransformed = newTransformed + (fun.name -> newFunName)

        val newRetCName = Symbol.fresh(s"${fun.retC}")
        newTransformed = newTransformed + (fun.retC -> newRetCName)
        
        fun.args.foreach { arg =>
          val newArgName = Symbol.fresh(s"${arg}")
          newTransformed = newTransformed + (arg -> newArgName)
        }
      }

      val newFuns = funs.map { fun =>
        val newArgs = fun.args.map(newTransformed(_))
        FunDef(newTransformed(fun.name), newTransformed(fun.retC), newArgs, freshenLabels(fun.body)(newTransformed))
      }

      LetF(newFuns, freshenLabels(body)(newTransformed))

    case AppC(cnt, args) => 
      val newArgs = args.map(arg => transformed.getOrElse(arg, arg))
      AppC(transformed.getOrElse(cnt, cnt), newArgs)

    case AppF(fun, retC, args) =>
      val newArgs = args.map(arg => transformed.getOrElse(arg, arg))
      AppF(transformed.getOrElse(fun, fun), transformed.getOrElse(retC, retC), newArgs)

    case If(cond, args, thenC, elseC) =>
      val newArgs = args.map(arg => transformed.getOrElse(arg, arg))
      If(cond, newArgs, transformed.getOrElse(thenC, thenC), transformed.getOrElse(elseC, elseC))

    case Halt(arg) =>
      Halt(transformed.getOrElse(arg, arg))

    case _ => ???
  }

  // Check for recursion
  private def isRecursive(current: Tree)(implicit name: Name): Boolean = {
    current match {
      case LetL(_, _, body) => isRecursive(body)
      case LetP(_, _, _, body) => isRecursive(body)
      case LetC(cnts, body) =>
        cnts.exists(cnt => isRecursive(cnt.body)) || isRecursive(body)
      case LetF(funs, body) =>
        funs.exists(fun => isRecursive(fun.body)) || isRecursive(body)
      case AppC(cnt, _) => cnt == name
      case AppF(fun, retC, _) => fun == name || retC == name
      case If(_, _, thenC, elseC) => thenC == name || elseC == name
      case Halt(_) => false
      case _ => false
    }
  }

  // Census computation
  private def census(tree: Tree): Map[Name, Count] = {
    val census = MutableMap[Name, Count]()
    val rhs = MutableMap[Name, Tree]()

    def incAppUse(symbol: Name): Unit = {
      val currCount = census.getOrElse(symbol, Count())
      census(symbol) = currCount.copy(applied = currCount.applied + 1)
      rhs remove symbol foreach addToCensus
    }

    def incValUse(symbol: Name): Unit = {
      val currCount = census.getOrElse(symbol, Count())
      census(symbol) = currCount.copy(asValue = currCount.asValue + 1)
      rhs remove symbol foreach addToCensus
    }

    def addToCensus(tree: Tree): Unit = (tree: @unchecked) match {
      case LetL(_, _, body) =>
        addToCensus(body)
      case LetP(name, prim, args, body) =>
        args foreach incValUse; addToCensus(body)
      case LetC(cnts, body) =>
        rhs ++= (cnts map { c => (c.name, c.body) }); addToCensus(body)
      case LetF(funs, body) =>
        rhs ++= (funs map { f => (f.name, f.body) }); addToCensus(body)
      case AppC(cnt, args) =>
        incAppUse(cnt); args foreach incValUse
      case AppF(fun, retC, args) =>
        incAppUse(fun); incValUse(retC); args foreach incValUse
      case If(_, args, thenC, elseC) =>
        args foreach incValUse; incValUse(thenC); incValUse(elseC)
      case Halt(arg) =>
        incValUse(arg)
    }

    addToCensus(tree)
    census.toMap
  }

  private def sameLen(formalArgs: Seq[Name], actualArgs: Seq[Name]): Boolean =
    formalArgs.length == actualArgs.length

  private def size(tree: Tree): Int = (tree: @unchecked) match {
    case LetL(_, _, body) => size(body) + 1
    case LetP(_, _, _, body) => size(body) + 1
    case LetC(cs, body) => (cs map { c => size(c.body) }).sum + size(body)
    case LetF(fs, body) => (fs map { f => size(f.body) }).sum + size(body)
    case AppC(_, _) | AppF(_, _, _) | If(_, _, _, _) | Halt(_) => 1
  }

  // Returns whether a ValuePrimitive has side-effects
  protected val impure: ValuePrimitive => Boolean
  // Returns whether different applications of a ValuePrimivite on the
  // same arguments may yield different results
  protected val unstable: ValuePrimitive => Boolean
  // Extracts the tag from a block allocation primitive
  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal]
  // Returns true for the block tag primitive
  protected val blockTag: ValuePrimitive
  // Returns true for the block length primitive
  protected val blockLength: ValuePrimitive
  // Returns true for the identity primitive
  protected val identity: ValuePrimitive

  // ValuePrimitives with their left-neutral elements
  protected val leftNeutral: Set[(Literal, ValuePrimitive)]
  // ValuePrimitives with their right-neutral elements
  protected val rightNeutral: Set[(ValuePrimitive, Literal)]
  // ValuePrimitives with their left-absorbing elements
  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)]
  // ValuePrimitives with their right-absorbing elements
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)]
  // ValuePrimitives with the value equal arguments reduce to
  protected val sameArgReduce: PartialFunction[ValuePrimitive, Literal]
  // TestPrimitives with the (boolean) value equal arguments reduce to
  protected val sameArgReduceC: TestPrimitive => Boolean
  // An evaluator for ValuePrimitives
  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Literal]),
                                            Literal]
  // An evaluator for TestPrimitives
  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Literal]),
                                            Boolean]
}

object CPSOptimizerHigh extends CPSOptimizer(SymbolicCPSTreeModule)
    with (SymbolicCPSTreeModule.Tree => SymbolicCPSTreeModule.Tree) {
  import treeModule._

  protected val impure: ValuePrimitive => Boolean =
    Set(MiniScalaBlockSet, MiniScalaByteRead, MiniScalaByteWrite)

  protected val unstable: ValuePrimitive => Boolean = {
    case MiniScalaBlockAlloc(_) | MiniScalaBlockGet | MiniScalaByteRead => true
    case _ => false
  }

  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal] = {
    case MiniScalaBlockAlloc(tag) => IntLit(tag)
  }
  protected val blockTag: ValuePrimitive = MiniScalaBlockTag
  protected val blockLength: ValuePrimitive = MiniScalaBlockLength

  protected val identity: ValuePrimitive = MiniScalaId

  protected val leftNeutral: Set[(Literal, ValuePrimitive)] =
    Set(
      (IntLit(0), MiniScalaIntAdd),
      (IntLit(1), MiniScalaIntMul),
      (IntLit(~0), MiniScalaIntBitwiseAnd),
      (IntLit(0), MiniScalaIntBitwiseOr),
      (IntLit(0), MiniScalaIntBitwiseXOr)
    )
  
  protected val rightNeutral: Set[(ValuePrimitive, Literal)] =
    Set(
      (MiniScalaIntAdd, IntLit(0)),
      (MiniScalaIntSub, IntLit(0)),
      (MiniScalaIntMul, IntLit(1)),
      (MiniScalaIntDiv, IntLit(1)),
      (MiniScalaIntArithShiftLeft, IntLit(0)),
      (MiniScalaIntArithShiftRight, IntLit(0)),
      (MiniScalaIntBitwiseAnd, IntLit(~0)),
      (MiniScalaIntBitwiseOr, IntLit(0)),
      (MiniScalaIntBitwiseXOr, IntLit(0))
    )

  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)] =
    Set(
      (IntLit(0), MiniScalaIntMul),
      (IntLit(0), MiniScalaIntBitwiseAnd),
      (IntLit(~0), MiniScalaIntBitwiseOr)
    )
 
 protected val rightAbsorbing: Set[(ValuePrimitive, Literal)] =
    Set(
      (MiniScalaIntMul, IntLit(0)),
      (MiniScalaIntBitwiseAnd, IntLit(0)),
      (MiniScalaIntBitwiseOr, IntLit(~0))
    )

  protected val sameArgReduce: PartialFunction[ValuePrimitive, Literal] =
    Map(
      MiniScalaIntSub -> IntLit(0),
      MiniScalaIntDiv -> IntLit(1),
      MiniScalaIntMod -> IntLit(0),
      MiniScalaIntBitwiseXOr -> IntLit(0)
    )

  protected val sameArgReduceC: PartialFunction[TestPrimitive, Boolean] = {
    case MiniScalaIntLe | MiniScalaIntGe | MiniScalaEq => true
    case MiniScalaIntLt | MiniScalaIntGt | MiniScalaNe => false
    case _ => ???
  }

  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Literal]),
                                            Literal] = {
    case (MiniScalaIntAdd, Seq(IntLit(x), IntLit(y))) => IntLit(x + y)
    case (MiniScalaIntSub, Seq(IntLit(x), IntLit(y))) => IntLit(x - y)
    case (MiniScalaIntSub, Seq(IntLit(x)))            => IntLit(-x)
    case (MiniScalaIntMul, Seq(IntLit(x), IntLit(y))) => IntLit(x * y)
    case (MiniScalaIntDiv, Seq(IntLit(x), IntLit(y))) if (y != 0) => IntLit(Math.floorDiv(x, y))
    case (MiniScalaIntMod, Seq(IntLit(x), IntLit(y))) if (y != 0) => IntLit(Math.floorMod(x, y))

    case (MiniScalaIntArithShiftLeft, Seq(IntLit(x), IntLit(y))) => IntLit(x << y)
    case (MiniScalaIntArithShiftRight, Seq(IntLit(x), IntLit(y))) => IntLit(x >> y)
    case (MiniScalaIntBitwiseAnd, Seq(IntLit(x), IntLit(y))) => IntLit(x & y)
    case (MiniScalaIntBitwiseOr, Seq(IntLit(x), IntLit(y))) => IntLit(x | y)
    case (MiniScalaIntBitwiseXOr, Seq(IntLit(x), IntLit(y))) => IntLit(x ^ y)

    case (MiniScalaCharToInt, Seq(CharLit(x))) => IntLit(x.toInt)
    case (MiniScalaIntToChar, Seq(IntLit(x))) => CharLit(x.toChar)
    case _ => ???
  }

  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Literal]),
                                            Boolean] = {
    case (MiniScalaIntP, Seq(IntLit(_))) => true
    case (MiniScalaIntP, Seq(_)) => false
    case (MiniScalaCharP, Seq(CharLit(_))) => true
    case (MiniScalaCharP, Seq(_)) => false
    case (MiniScalaBoolP, Seq(BooleanLit(_))) => true
    case (MiniScalaBoolP, Seq(_)) => false
    case (MiniScalaUnitP, Seq(UnitLit)) => true
    case (MiniScalaUnitP, Seq(_)) => false

    case (MiniScalaIntLt, Seq(IntLit(x), IntLit(y))) => x < y
    case (MiniScalaIntLe, Seq(IntLit(x), IntLit(y))) => x <= y
    case (MiniScalaIntGe, Seq(IntLit(x), IntLit(y))) => x >= y
    case (MiniScalaIntGt, Seq(IntLit(x), IntLit(y))) => x > y

    case (MiniScalaEq, Seq(x, y)) => x == y
    case (MiniScalaNe, Seq(x, y)) => x != y
    case _ => false
  }
}

object CPSOptimizerLow extends CPSOptimizer(SymbolicCPSTreeModuleLow)
    with (SymbolicCPSTreeModuleLow.Tree => SymbolicCPSTreeModuleLow.Tree) {
  import treeModule._

  protected val impure: ValuePrimitive => Boolean =
    Set(CPSBlockSet, CPSByteRead, CPSByteWrite)

  protected val unstable: ValuePrimitive => Boolean = {
    case CPSBlockAlloc(_) | CPSBlockGet | CPSByteRead => true
    case _ => false
  }

  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal] = {
    case CPSBlockAlloc(tag) => tag
  }
  protected val blockTag: ValuePrimitive = CPSBlockTag
  protected val blockLength: ValuePrimitive = CPSBlockLength

  protected val identity: ValuePrimitive = CPSId

  protected val leftNeutral: Set[(Literal, ValuePrimitive)] =
    Set((0, CPSAdd), (1, CPSMul), (~0, CPSAnd), (0, CPSOr), (0, CPSXOr))
  protected val rightNeutral: Set[(ValuePrimitive, Literal)] =
    Set((CPSAdd, 0), (CPSSub, 0), (CPSMul, 1), (CPSDiv, 1),
        (CPSArithShiftL, 0), (CPSArithShiftR, 0),
        (CPSAnd, ~0), (CPSOr, 0), (CPSXOr, 0))

  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)] =
    Set((0, CPSMul), (0, CPSAnd), (~0, CPSOr))
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)] =
    Set((CPSMul, 0), (CPSAnd, 0), (CPSOr, ~0))

  protected val sameArgReduce: Map[ValuePrimitive, Literal] =
    Map(CPSSub -> 0, CPSDiv -> 1, CPSMod -> 0, CPSXOr -> 0)

  protected val sameArgReduceC: PartialFunction[TestPrimitive, Boolean] = {
    case CPSLe | CPSGe | CPSEq => true
    case CPSLt | CPSGt | CPSNe => false
  }

  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Literal]),
                                            Literal] = {
    case (CPSAdd, Seq(x, y)) => x + y
    case (CPSSub, Seq(x, y)) => x - y
    case (CPSMul, Seq(x, y)) => x * y
    case (CPSDiv, Seq(x, y)) if (y != 0) => Math.floorDiv(x, y)
    case (CPSMod, Seq(x, y)) if (y != 0) => Math.floorMod(x, y)

    case (CPSArithShiftL, Seq(x, y)) => x << y
    case (CPSArithShiftR, Seq(x, y)) => x >> y
    case (CPSAnd, Seq(x, y)) => x & y
    case (CPSOr, Seq(x, y)) => x | y
    case (CPSXOr, Seq(x, y)) => x ^ y
  }

  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Literal]),
                                            Boolean] = {

    case (CPSLt, Seq(x, y)) => x < y
    case (CPSLe, Seq(x, y)) => x <= y
    case (CPSEq, Seq(x, y)) => x == y
    case (CPSNe, Seq(x, y)) => x != y
    case (CPSGe, Seq(x, y)) => x >= y
    case (CPSGt, Seq(x, y)) => x > y
  }
}
