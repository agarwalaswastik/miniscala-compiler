package miniscala

import miniscala.{ SymbolicCMScalaTreeModule => S }
import miniscala.{ SymbolicCPSTreeModule => C }

object CMScalaToCPSTranslator extends (S.Tree => C.Tree) {
  def apply(tree: S.Tree): C.Tree = {
    nonTail(tree){_ =>
      val z = Symbol.fresh("c0")
      C.LetL(z, IntLit(0), C.Halt(z))
    }(Set.empty)
  }

  private def nonTail(tree: S.Tree)(ctx: Symbol=>C.Tree)(implicit mut: Set[Symbol]): C.Tree = {
    // @unchecked to avoid bogus compiler warnings
    (tree: @unchecked) match {
      case S.Let(name, _, value, body) =>
        nonTail(value)(v =>
            C.LetP(name, MiniScalaId, Seq(v), nonTail(body)(ctx)))

      // Reference of an immutable variable
      case S.Ref(name) if !mut(name) =>
        ctx(name)

      // Reference of an mutable variable
      case S.Ref(name) => // if mut(name) =>
        val zSym = Symbol.fresh("z")
        val vSym = Symbol.fresh("v")

        C.LetL(zSym, IntLit(0), 
          C.LetP(vSym, MiniScalaBlockGet, Seq(name, zSym), ctx(vSym))
        )

      case S.Lit(lit) =>
        val nSym = Symbol.fresh("n")
        C.LetL(nSym, lit, ctx(nSym))

      case S.VarDec(n1, _, e1, e) =>
        val sSym = Symbol.fresh("s")
        val zSym = Symbol.fresh("z")
        val dSym = Symbol.fresh("d")

        C.LetL(sSym, IntLit(1),
          C.LetP(n1, MiniScalaBlockAlloc(BlockTag.Variable.id), Seq(sSym),
            C.LetL(zSym, IntLit(0),
              nonTail(e1)(v =>
                C.LetP(
                  dSym,
                  MiniScalaBlockSet,
                  Seq(n1, zSym, v),
                  nonTail(e)(ctx)(mut + n1)
                )
              )
            )
          )
        )

      case S.VarAssign(n1, e1) =>
        val zSym = Symbol.fresh("z")
        val dSym = Symbol.fresh("d")

        C.LetL(zSym, IntLit(0),
          nonTail(e1)(v =>
            C.LetP(dSym, MiniScalaBlockSet, Seq(n1, zSym, v), ctx(v))
          )
        )

      case S.LetRec(funs, e) =>
        val funDefs = funs.map { f =>
          val retC = Symbol.fresh(s"${f.name}_retC")
          val args = f.args.map(_.name)
          C.FunDef(f.name, retC, args, tail(f.body, retC))
        }

        C.LetF(funDefs, nonTail(e)(ctx))

      case S.App(f, _, args) =>
        val rSym = Symbol.fresh("r")

        nonTail(f)(v =>
          nonTail_*(args)(symbols =>
            tempLetC(s"${v.toString}_retC", Seq(rSym), ctx(rSym))(c =>
              C.AppF(v, c, symbols)
            )
          )
        )

      case S.If(e1, e2, e3) =>
        val rSym = Symbol.fresh("r")

        tempLetC("c", Seq(rSym), ctx(rSym))(c =>
          tempLetC("ct", Seq(), tail(e2, c))(ct =>
            tempLetC("cf", Seq(), tail(e3, c))(cf => 
              cond(e1, ct, cf)
            )
          )
        )

      case S.While(e1, e2, e3) =>
        val loopSym = Symbol.fresh("loop")
        val dParam = Symbol.fresh("d")
        val dArg = Symbol.fresh("d")

        C.LetC(
          Seq(C.CntDef(loopSym, Seq(dParam), 
            tempLetC("c", Seq(), nonTail(e3)(ctx))(c =>
              tempLetC("ct", Seq(), tail(e2, loopSym))(ct =>
                cond(e1, ct, c)
              )
            )
          )),
          C.LetL(dArg, UnitLit,
            C.AppC(loopSym, Seq(dArg))
          )
        )

      case p@S.Prim(op: MiniScalaTestPrimitive, _) =>
        nonTail(S.If(p, S.Lit(BooleanLit(true)), S.Lit(BooleanLit(false))))(ctx)

      case S.Prim(op: MiniScalaValuePrimitive, args) =>
        val nSym = Symbol.fresh("n")
        nonTail_*(args)(symbols =>
          C.LetP(nSym, op, symbols, ctx(nSym))
        )

      case S.Halt(exitVal) =>
        nonTail(exitVal)(v => C.Halt(v))

      case _ => ???
    }
  }
  
  // nonTail_* takes a sequence of S.Tree, and a continuation that takes a
  // sequence of symbols.  The sequence of symbols in the continuation
  // represents the transformed result of `trees`.  This is particularly useful
  // for the App case in nonTail.
  private def nonTail_*(trees: Seq[S.Tree])(ctx: Seq[Symbol]=>C.Tree)(implicit mut: Set[Symbol]): C.Tree =
    trees match {
      case Seq() => 
        ctx(Seq())
      case t +: ts =>
        nonTail(t)(tSym => nonTail_*(ts)(tSyms => ctx(tSym +: tSyms)))
    }

  private def tail(tree: S.Tree, c: Symbol)(implicit mut: Set[Symbol]): C.Tree = {
    // @unchecked to avoid bogus compiler warnings
    (tree: @unchecked) match {
      case S.Let(name, _, value, body) =>
        nonTail(value)(v =>
            C.LetP(name, MiniScalaId, Seq(v), tail(body, c)))

      // Reference of an immutable variable
      case S.Ref(name) if !mut(name) =>
        C.AppC(c, Seq(name))

      // Reference of an mutable variable
      case S.Ref(name) => // if mut(name) =>
        val zSym = Symbol.fresh("z")
        val vSym = Symbol.fresh("v")

        C.LetL(zSym, IntLit(0), 
          C.LetP(vSym, MiniScalaBlockGet, Seq(name, zSym), C.AppC(c, Seq(vSym)))
        )

      case S.Lit(lit) =>
        val nSym = Symbol.fresh("n")
        C.LetL(nSym, lit, C.AppC(c, Seq(nSym)))

      case S.VarDec(n1, _, e1, e) =>
        val sSym = Symbol.fresh("s")
        val zSym = Symbol.fresh("z")
        val dSym = Symbol.fresh("d")

        C.LetL(sSym, IntLit(1),
          C.LetP(n1, MiniScalaBlockAlloc(BlockTag.Variable.id), Seq(sSym),
            C.LetL(zSym, IntLit(0),
              nonTail(e1)(v =>
                C.LetP(
                  dSym,
                  MiniScalaBlockSet,
                  Seq(n1, zSym, v),
                  tail(e, c)(mut + n1)
                )
              )
            )
          )
        )

      case S.VarAssign(n1, e1) =>
        val zSym = Symbol.fresh("z")
        val dSym = Symbol.fresh("d")

        C.LetL(zSym, IntLit(0),
          nonTail(e1)(v =>
            C.LetP(dSym, MiniScalaBlockSet, Seq(n1, zSym, v), C.AppC(c, Seq(v)))
          )
        )

      case S.LetRec(funs, e) =>
        val funDefs = funs.map { f =>
          val retC = Symbol.fresh(s"${f.name}_retC")
          val args = f.args.map(_.name)
          C.FunDef(f.name, retC, args, tail(f.body, retC))
        }

        C.LetF(funDefs, tail(e, c))

      case S.App(f, _, args) =>
        nonTail(f)(v =>
          nonTail_*(args)(symbols =>
            C.AppF(v, c, symbols)
          )
        )

      case S.If(e1, e2, e3) =>
        tempLetC("ct", Seq(), tail(e2, c))(ct =>
          tempLetC("cf", Seq(), tail(e3, c))(cf => 
            cond(e1, ct, cf)
          )
        )

      case S.While(e1, e2, e3) =>
        val loopSym = Symbol.fresh("loop")
        val dParam = Symbol.fresh("d")
        val dArg = Symbol.fresh("d")

        C.LetC(
          Seq(C.CntDef(loopSym, Seq(dParam), 
            tempLetC("c", Seq(), tail(e3, c))(cc =>
              tempLetC("ct", Seq(), tail(e2, loopSym))(ct =>
                cond(e1, ct, cc)
              )
            )
          )),
          C.LetL(dArg, UnitLit,
            C.AppC(loopSym, Seq(dArg))
          )
        )

      case p@S.Prim(op: MiniScalaTestPrimitive, _) =>
        tail(S.If(p, S.Lit(BooleanLit(true)), S.Lit(BooleanLit(false))), c)

      case S.Prim(op: MiniScalaValuePrimitive, args) =>
        val nSym = Symbol.fresh("n")
        nonTail_*(args)(symbols =>
          C.LetP(nSym, op, symbols, C.AppC(c, Seq(nSym)))
        )

      case S.Halt(exitVal) =>
        nonTail(exitVal)(v => C.Halt(v))

      case _ => ???
    }
  }

  private def cond(tree: S.Tree, trueC: Symbol, falseC: Symbol)(implicit mut: Set[Symbol]): C.Tree = {
    def litToCont(l: CMScalaLiteral): Symbol =
      if (l != BooleanLit(false)) trueC else falseC

    tree match {
      case S.If(condE, S.Lit(tl), S.Lit(fl)) =>
        cond(condE, litToCont(tl), litToCont(fl))

      case S.If(e1, e2, S.Lit(l)) =>
        tempLetC("ac", Seq(), cond(e2, trueC, falseC))(ac =>
          cond(e1, ac, litToCont(l)))

      case S.If(e1, S.Lit(l), e3) =>
        tempLetC("bc", Seq(), cond(e3, trueC, falseC))(bc =>
          cond(e1, litToCont(l), bc))

      case S.Prim(p: MiniScalaTestPrimitive, args) =>
        nonTail_*(args)(as => C.If(p, as, trueC, falseC))

      case other =>
        nonTail(other)(o =>
          nonTail(S.Lit(BooleanLit(false)))(n =>
            C.If(MiniScalaNe, Seq(o, n), trueC, falseC)))
    }
  }

  // Helper function for defining a continuation.
  // Example:
  // tempLetC("c", Seq(r), ctx(r))(k => App(f, k, as))
  private def tempLetC(cName: String, args: Seq[C.Name], cBody: C.Tree)
                      (body: C.Name=>C.Tree): C.Tree = {
    val cSym = Symbol.fresh(cName)
    C.LetC(Seq(C.CntDef(cSym, args, cBody)), body(cSym))
  }
}
