/*
 * Copyright (C) 2012-2018 Lightbend Inc. <http://www.lightbend.com>
 */

package scala.async.internal.transform

import scala.Predef._
import scala.reflect.internal.util.Collections.map2

private[async] trait AnfTransform extends TransformUtils {
  import c.universe._
  import Flag._
  import c.internal.{decorators, gen, typingTransform, valDef}
  import decorators._

  def anfTransform(tree: Tree, owner: Symbol): Block = {
    // Must prepend the () for issue #31.
    val block = c.typecheck(atPos(tree.pos)(newBlock(List(literalUnit), tree))).setType(tree.tpe)

    sealed abstract class AnfMode
    case object Anf extends AnfMode
    case object Linearizing extends AnfMode

    val tree1 = adjustTypeOfTranslatedPatternMatches(block, owner)

    var mode: AnfMode = Anf

    object trace {
      private var indent = -1

      private def indentString = "  " * indent

      def apply[T](args: Any)(t: => T): T = {
        def prefix = mode.toString.toLowerCase
        indent += 1
        def oneLine(s: Any) = s.toString.replaceAll("""\n""", "\\\\n").take(127)
        try {
          if(AsyncUtils.trace)
            AsyncUtils.trace(s"$indentString$prefix(${oneLine(args)})")
          val result = t
          if(AsyncUtils.trace)
            AsyncUtils.trace(s"$indentString= ${oneLine(result)}")
          result
        } finally {
          indent -= 1
        }
      }
    }

    // creates a subclass of TypingTransformer
    c.internal.typingTransform(tree1, owner)((tree, api) => {
      import api.{atOwner, currentOwner}

      // localTyper
      def typed(tree: Tree) = api.typecheck(tree)
      def typedAt(exprPos: Position, tree: Tree) = api.typecheck(atPos(exprPos)(tree))

      def blockToList(tree: Tree): List[Tree] = tree match {
        case Block(stats, expr) => stats :+ expr
        case t                  => t :: Nil
      }

      def listToBlock(trees: List[Tree]): Block = trees match {
        case trees @ (init :+ last) =>
          val pos = trees.map(_.pos).reduceLeft(_ union _)
          newBlock(init, last).setType(last.tpe).setPos(pos)
      }

      object linearize {
        def transformToList(tree: Tree): List[Tree] = {
          mode = Linearizing; blockToList(api.recur(tree))
        }

        def transformToBlock(tree: Tree): Block = listToBlock(transformToList(tree))

        def _transformToList(tree: Tree): List[Tree] = trace(tree) {
          val stats :+ expr = _anf.transformToList(tree)
          def statsExprUnit = {
            stats :+ expr :+ typedAt(expr.pos, literalUnit)
          }
          def statsExprThrow =
            stats :+ expr :+ typedAt(expr.pos, Throw(Apply(Select(New(gen.mkAttributedRef(defn.IllegalStateExceptionClass)), nme.CONSTRUCTOR), Nil)))
          expr match {
            case Apply(fun, args) if isAwait(fun) =>
              val valDef = defineVal(name.await(), expr, tree.pos)
              val ref = gen.mkAttributedStableRef(valDef.symbol).setType(tree.tpe)
              val ref1 = if (ref.tpe =:= definitions.UnitTpe)
                // https://github.com/scala/async/issues/74
                // Use a cast to hide from "pure expression does nothing" error
                //
                // TODO avoid creating a ValDef for the result of this await to avoid this tree shape altogether.
                // This will require some deeper changes to the later parts of the macro which currently assume regular
                // tree structure around `await` calls.
                typedAt(tree.pos, gen.mkCast(ref, definitions.UnitTpe))
              else ref
              stats :+ valDef :+ atPos(tree.pos)(ref1)

            case If(cond, thenp, elsep) =>
              // If we run the ANF transform post patmat, deal with trees like `(if (cond) jump1(){String} else jump2(){String}){String}`
              // as though it was typed with `Unit`.
              def isPatMatGeneratedJump(t: Tree): Boolean = t match {
                case Block(_, expr) => isPatMatGeneratedJump(expr)
                case If(_, thenp, elsep) => isPatMatGeneratedJump(thenp) && isPatMatGeneratedJump(elsep)
                case _: Apply if isLabel(t.symbol) => true
                case _ => false
              }
              if (isPatMatGeneratedJump(expr)) {
                internal.setType(expr, definitions.UnitTpe)
              }
              // if type of if-else is Unit don't introduce assignment,
              // but add Unit value to bring it into form expected by async transform
              if (expr.tpe =:= definitions.UnitTpe) {
                statsExprUnit
              } else if (expr.tpe =:= definitions.NothingTpe) {
                statsExprThrow
              } else {
                val varDef = defineVar(name.ifRes(), expr.tpe, tree.pos)
                def typedAssign(lhs: Tree) =
                  typedAt(lhs.pos, Assign(Ident(varDef.symbol), mkAttributedCastPreservingAnnotations(lhs, tpe(varDef.symbol))))

                def branchWithAssign(t: Tree): Tree = {
                  t match {
                    case MatchEnd(ld) =>
                      deriveLabelDef(ld, branchWithAssign)
                    case blk @ Block(thenStats, thenExpr) =>
                      treeCopy.Block(blk, thenStats, branchWithAssign(thenExpr)).setType(definitions.UnitTpe)
                    case _ =>
                      typedAssign(t)
                  }
                }
                val ifWithAssign = treeCopy.If(tree, cond, branchWithAssign(thenp), branchWithAssign(elsep)).setType(definitions.UnitTpe)
                stats :+ varDef :+ ifWithAssign :+ atPos(tree.pos)(gen.mkAttributedStableRef(varDef.symbol)).setType(tree.tpe)
              }
            case ld @ LabelDef(name, params, rhs) =>
              if (isUnitType(ld.symbol.info.resultType))
                statsExprUnit
              else
                stats :+ expr

            case Match(scrut, cases) =>
              // if type of match is Unit don't introduce assignment,
              // but add Unit value to bring it into form expected by async transform
              if (expr.tpe =:= definitions.UnitTpe) {
                statsExprUnit
              } else if (expr.tpe =:= definitions.NothingTpe) {
                statsExprThrow
              } else {
                val varDef = defineVar(name.matchRes(), expr.tpe, tree.pos)
                def typedAssign(lhs: Tree) =
                  typedAt(lhs.pos, Assign(Ident(varDef.symbol), mkAttributedCastPreservingAnnotations(lhs, tpe(varDef.symbol))))
                val casesWithAssign = cases map {
                  case cd@CaseDef(pat, guard, body) =>
                    def bodyWithAssign(t: Tree): Tree = {
                      t match {
                        case MatchEnd(ld) => deriveLabelDef(ld, bodyWithAssign)
                        case b@Block(caseStats, caseExpr) => treeCopy.Block(b, caseStats, bodyWithAssign(caseExpr)).setType(definitions.UnitTpe)
                        case _ => typedAssign(t)
                      }
                    }
                    treeCopy.CaseDef(cd, pat, guard, bodyWithAssign(body)).setType(definitions.UnitTpe)
                }
                val matchWithAssign = treeCopy.Match(tree, scrut, casesWithAssign).setType(definitions.UnitTpe)
                require(matchWithAssign.tpe != null, matchWithAssign)
                stats :+ varDef :+ matchWithAssign :+ atPos(tree.pos)(gen.mkAttributedStableRef(varDef.symbol)).setType(tree.tpe)
              }
            case _                   =>
              stats :+ expr
          }
        }

        def defineVar(name: TermName, tp: Type, pos: Position): ValDef = {
          val sym = currentOwner.newTermSymbol(name, pos, MUTABLE | SYNTHETIC).setInfo(uncheckedBounds(tp))
          valDef(sym, mkZero(uncheckedBounds(tp))).setType(NoType).setPos(pos)
        }
      }

      def defineVal(name: TermName, lhs: Tree, pos: Position): ValDef = {
        val sym = currentOwner.newTermSymbol(name, pos, SYNTHETIC).setInfo(uncheckedBounds(lhs.tpe))
        internal.valDef(sym, internal.changeOwner(lhs, currentOwner, sym)).setType(NoType).setPos(pos)
      }

      object _anf {
        def transformToList(tree: Tree): List[Tree] = {
          mode = Anf; blockToList(api.recur(tree))
        }

        def _transformToList(tree: Tree): List[Tree] = trace(tree) {
          if (!containsAwait(tree)) {
            tree match {
              case Block(stats, expr) =>
                // avoids nested block in `while(await(false)) ...`.
                // TODO I think `containsAwait` really should return true if the code contains a label jump to an enclosing
                // while/doWhile and there is an await *anywhere* inside that construct.
                stats :+ expr
              case _ => List(tree)
            }
          } else tree match {
            case Select(qual, sel) =>
              val stats :+ expr = linearize.transformToList(qual)
              stats :+ treeCopy.Select(tree, expr, sel)

            case Throw(expr) =>
              val stats :+ expr1 = linearize.transformToList(expr)
              stats :+ treeCopy.Throw(tree, expr1)

            case Typed(expr, tpt) =>
              val stats :+ expr1 = linearize.transformToList(expr)
              stats :+ treeCopy.Typed(tree, expr1, tpt)

            case Applied(fun, targs, argss) if argss.nonEmpty =>
              // we can assume that no await call appears in a by-name argument position,
              // this has already been checked.
              val funStats :+ simpleFun = linearize.transformToList(fun)
              val (argStatss, argExprss): (List[List[List[Tree]]], List[List[Tree]]) =
                mapArgumentss[List[Tree]](fun, argss) {
                  case Arg(expr, byName, _) if byName /*|| isPure(expr) TODO */ => (Nil, expr)
                  case Arg(expr, _, argName)                                    =>
                    linearize.transformToList(expr) match {
                      case stats :+ expr1 =>
                        val valDef = defineVal(name.freshen(argName), expr1, expr1.pos)
                        require(valDef.tpe != null, valDef)
                        val stats1 = stats :+ valDef
                        (stats1, atPos(tree.pos.makeTransparent)(gen.stabilize(gen.mkAttributedIdent(valDef.symbol))))
                    }
                }

              def copyApplied(tree: Tree, depth: Int): Tree = {
                tree match {
                  case TypeApply(_, targs) => treeCopy.TypeApply(tree, simpleFun, targs)
                  case _ if depth == 0     => simpleFun
                  case Apply(fun, args)    =>
                    val newTypedArgs = map2(args.map(_.pos), argExprss(depth - 1))((pos, arg) => typedAt(pos, arg))
                    treeCopy.Apply(tree, copyApplied(fun, depth - 1), newTypedArgs)
                }
              }

              val typedNewApply = copyApplied(tree, argss.length)

              funStats ++ argStatss.flatten.flatten :+ typedNewApply

            case Block(stats, expr)                                    =>
              val stats1 = stats.flatMap(linearize.transformToList).filterNot(isLiteralUnit)
              val exprs1 = linearize.transformToList(expr)
              val trees = stats1 ::: exprs1
              def groupsEndingWith[T](ts: List[T])(f: T => Boolean): List[List[T]] = if (ts.isEmpty) Nil else {
                ts.indexWhere(f) match {
                  case -1 => List(ts)
                  case i =>
                    val (ts1, ts2) = ts.splitAt(i + 1)
                    ts1 :: groupsEndingWith(ts2)(f)
                }
              }
              val matchGroups = groupsEndingWith(trees){ case MatchEnd(_) => true; case _ => false }
              val trees1 = matchGroups.flatMap(eliminateMatchEndLabelParameter)
              val result = trees1 flatMap {
                case Block(stats, expr) => stats :+ expr
                case t => t :: Nil
              }
              result

            case ValDef(mods, name, tpt, rhs) =>
              if (containsAwait(rhs)) {
                val stats :+ expr = atOwner(currentOwner.owner)(linearize.transformToList(rhs))
                stats.foreach(_.changeOwner(currentOwner, currentOwner.owner))
                stats :+ treeCopy.ValDef(tree, mods, name, tpt, expr)
              } else List(tree)

            case Assign(lhs, rhs) =>
              val stats :+ expr = linearize.transformToList(rhs)
              stats :+ treeCopy.Assign(tree, lhs, expr)

            case If(cond, thenp, elsep) =>
              val condStats :+ condExpr = linearize.transformToList(cond)
              val thenBlock = linearize.transformToBlock(thenp)
              val elseBlock = linearize.transformToBlock(elsep)
              condStats :+ treeCopy.If(tree, condExpr, thenBlock, elseBlock)

            case Match(scrut, cases) =>
              val scrutStats :+ scrutExpr = linearize.transformToList(scrut)
              val caseDefs = cases map {
                case CaseDef(pat, guard, body) =>
                  // extract local variables for all names bound in `pat`, and rewrite `body`
                  // to refer to these.
                  // TODO we can move this into ExprBuilder once we get rid of `AsyncDefinitionUseAnalyzer`.
                  val block = linearize.transformToBlock(body)
                  val (valDefs, mappings) = (pat collect {
                    case b@Bind(bindName, _) =>
                      val vd = defineVal(name.freshen(bindName.toTermName), gen.mkAttributedStableRef(b.symbol).setPos(b.pos), b.pos)
                      vd.symbol.updateAttachment(SyntheticBindVal)
                      (vd, (b.symbol, vd.symbol))
                  }).unzip
                  val (from, to) = mappings.unzip
                  val b@Block(stats1, expr1) = block.substituteSymbols(from, to).asInstanceOf[Block]
                  val newBlock = treeCopy.Block(b, valDefs ++ stats1, expr1)
                  treeCopy.CaseDef(tree, pat, guard, newBlock)
              }
              scrutStats :+ treeCopy.Match(tree, scrutExpr, caseDefs)

            case LabelDef(name, params, rhs) =>
              if (isUnitType(tree.symbol.info))
                List(treeCopy.LabelDef(tree, name, params, typed(newBlock(linearize.transformToList(rhs), literalUnit))).setSymbol(tree.symbol))
              else
                List(treeCopy.LabelDef(tree, name, params, typed(listToBlock(linearize.transformToList(rhs)))).setSymbol(tree.symbol))

            case TypeApply(fun, targs) =>
              val funStats :+ simpleFun = linearize.transformToList(fun)
              funStats :+ treeCopy.TypeApply(tree, simpleFun, targs)

            case _ =>
              List(tree)
          }
        }
      }

      // Replace the label parameters on `matchEnd` with use of a `matchRes` temporary variable
      //
      // CaseDefs are translated to labels without parameters. A terminal label, `matchEnd`, accepts
      // a parameter which is the result of the match (this is regular, so even Unit-typed matches have this).
      //
      // For our purposes, it is easier to:
      //   - extract a `matchRes` variable
      //   - rewrite the terminal label def to take no parameters, and instead read this temp variable
      //   - change jumps to the terminal label to an assignment and a no-arg label application
      def eliminateMatchEndLabelParameter(statsExpr: List[Tree]): List[Tree] = {
        import internal.{methodType, setInfo}
        val caseDefToMatchResult = collection.mutable.Map[Symbol, Symbol]()

        val matchResults = collection.mutable.Buffer[Tree]()
        def modifyLabelDef(ld: LabelDef): (Tree, Tree) = {
          val param = ld.params.head
          val ld2 =
            if (isUnitType(ld.params.head.tpe)) {
              // Unit typed match: eliminate the label def parameter, but don't create a matchres temp variable to
              // store the result for cleaner generated code.
              caseDefToMatchResult(ld.symbol) = NoSymbol
              val rhs2 = substituteTrees(ld.rhs, param.symbol :: Nil, typed(literalUnit) :: Nil)
              val tree: Tree = literalUnit
              (treeCopy.LabelDef(ld, ld.name, Nil, typed(tree)), rhs2)
            } else {
              // Otherwise, create the matchres var. We'll callers of the label def below.
              // Remember: we're iterating through the statement sequence in reverse, so we'll get
              // to the LabelDef and mutate `matchResults` before we'll get to its callers.
              val matchResult = linearize.defineVar(name.matchRes(), param.tpe, ld.pos)
              matchResults += matchResult
              caseDefToMatchResult(ld.symbol) = matchResult.symbol
              val rhs2 = ld.rhs.substituteSymbols(param.symbol :: Nil, matchResult.symbol :: Nil)
              (treeCopy.LabelDef(ld, ld.name, Nil, typed(literalUnit)), rhs2)
            }
          setInfo(ld.symbol, methodType(Nil, definitions.UnitTpe))
          ld2
        }
        val statsExpr0 = statsExpr.reverse.flatMap {
          case ld @ LabelDef(_, param :: Nil, _) =>
            val (ld1, after) = modifyLabelDef(ld)
            List(after, ld1)
          case a @ ValDef(mods, name, tpt, ld @ LabelDef(_, param :: Nil, _)) =>
            val (ld1, after) = modifyLabelDef(ld)
            List(treeCopy.ValDef(a, mods, name, tpt, after), ld1)
          case t =>
            if (caseDefToMatchResult.isEmpty) t :: Nil
            else typingTransform(t)((tree, api) => {
              def typedPos(pos: Position)(t: Tree): Tree = api.typecheck(atPos(pos)(t))
              def transform(tree: Tree) = api.recur(tree)
              def superTransform = api.default(tree)

              tree match {
                case Apply(fun, arg :: Nil) if isLabel(fun.symbol) && caseDefToMatchResult.contains(fun.symbol) =>
                  val temp = caseDefToMatchResult(fun.symbol)
                  if (temp == NoSymbol)
                    typedPos(tree.pos)(newBlock(transform(arg) :: Nil, treeCopy.Apply(tree, fun, Nil)))
                  else
                    // setType needed for LateExpansion.shadowingRefinedType test case. There seems to be an inconsistency
                    // in the trees after pattern matcher.
                    // TODO miminize the problem in patmat and fix in scalac.
                    typedPos(tree.pos)(newBlock(Assign(Ident(temp), transform(internal.setType(arg, fun.tpe.paramLists.head.head.info))) :: Nil, treeCopy.Apply(tree, fun, Nil)))
                case Block(stats, expr: Apply) if isLabel(expr.symbol) =>
                  superTransform match {
                    case Block(stats0, Block(stats1, expr1)) =>
                      // flatten the block returned by `case Apply` above into the enclosing block for
                      // cleaner generated code.
                      treeCopy.Block(tree, stats0 ::: stats1, expr1)
                    case t => t
                  }
                case _ =>
                  superTransform
              }
            }) :: Nil
        }
        matchResults.toList match {
          case _ if caseDefToMatchResult.isEmpty =>
            statsExpr // return the original trees if nothing changed
          case Nil =>
            statsExpr0.reverse :+ literalUnit // must have been a unit-typed match, no matchRes variable to definne or refer to
          case r1 :: Nil =>
            // { var matchRes = _; ....; matchRes }
            (r1 +: statsExpr0.reverse) :+ atPos(tree.pos)(gen.mkAttributedIdent(r1.symbol))
          case _ => c.error(macroPos, "Internal error: unexpected tree encountered during ANF transform " + statsExpr); statsExpr
        }
      }

      def anfLinearize(tree: Tree): Block = {
        val trees: List[Tree] = mode match {
          case Anf         => _anf._transformToList(tree)
          case Linearizing => linearize._transformToList(tree)
        }
        listToBlock(trees)
      }

      tree match {
        case _: ValDef | _: DefDef | _: Function | _: ClassDef | _: TypeDef =>
          atOwner(tree.symbol)(anfLinearize(tree))
        case _: ModuleDef                                                   =>
          atOwner(tree.symbol.asModule.moduleClass orElse tree.symbol)(anfLinearize(tree))
        case _                                                              =>
          anfLinearize(tree)
      }
    }).asInstanceOf[Block]
  }
}

object SyntheticBindVal
