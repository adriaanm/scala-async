/*
 * Copyright (C) 2012-2018 Lightbend Inc. <http://www.lightbend.com>
 */
package scala.async.internal.transform

import scala.async.internal.{AsyncBase, AsyncNames}
import scala.collection.mutable
import scala.collection.mutable.ListBuffer
import scala.reflect.internal.Flags
import scala.reflect.macros.{Aliases, Internals}

private[async] trait AsyncContext {
  val u: scala.reflect.internal.SymbolTable
  import u._

  val body: Tree
  val macroPos: Position
  val asyncBase: AsyncBase
  def asyncMacroSymbol: Symbol
  def enclosingOwner: Symbol

  def emitTryCatch: Boolean = asyncBase.futureSystem.emitTryCatch

  // TODO does need to be a var??
  var containsAwait: Tree => Boolean

  // macro context interface -- the rest is meant to be independent of our being a macro (planning to move async into the compiler)
  def abort(pos: Position, msg: String): Nothing
  def error(pos: Position, msg: String): Unit
  def typecheck(tree: Tree): Tree
  val typingTransformers: (Aliases with Internals{val universe: u.type})#ContextInternalApi

  lazy val asyncNames: AsyncNames[u.type] = rootMirror.RootClass.attachments.get[AsyncNames[u.type]].getOrElse {
    val names = new AsyncNames[u.type](u)
    rootMirror.RootClass.attachments.update(names)
    names
  }

  object name extends asyncNames.AsyncName {
    def fresh(name: TermName): TermName = freshenIfNeeded(name)
    def fresh(name: String): String = currentFreshNameCreator.newName(name) // TODO ok? was c.freshName
  }
}

// Logic sensitive to where we are in the pipeline
// (intend to move the transformation as late as possible, to avoid lugging all these trees around)
trait PhasedTransform extends AsyncContext {
  import u._

  def atMacroPos(t: Tree): Tree = atPos(macroPos)(t)

  def literalNull = Literal(Constant(null))

  def typeEqualsNothing(tp: Type) = tp =:= definitions.NothingTpe

  def typeEqualsUnit(tp: Type) = tp =:= definitions.UnitTpe
  def castToUnit(t: Tree) = gen.mkCast(t, definitions.UnitTpe)

  def assignUnitType(t: Tree): t.type = internal.setType(t, definitions.UnitTpe)
  def setUnitMethodInfo(sym: Symbol): sym.type = internal.setInfo(sym, MethodType(Nil, definitions.UnitTpe))

  def isUnitType(tp: Type) = tp.typeSymbol == definitions.UnitClass
  def isNothingClass(sym: Symbol) = sym == definitions.NothingClass

  def literalUnit = Literal(Constant(())) // a def to avoid sharing trees

  def isLiteralUnit(t: Tree) = t match {
    case Literal(Constant(())) => true
    case _ => false
  }

  def function0ToUnit = typeOf[() => Unit]
  def apply0DefDef: DefDef =
    DefDef(NoMods, name.apply, Nil, Nil, TypeTree(definitions.UnitTpe), Apply(Ident(name.apply), literalNull :: Nil))

  def function1ToUnit(argTp: Type, useClass: Boolean) = {
    val fun =
      if (useClass) symbolOf[scala.runtime.AbstractFunction1[Any, Any]]
      else symbolOf[scala.Function1[Any, Any]]

    appliedType(fun, argTp, typeOf[Unit])
  }
  def apply1ToUnitDefDef(argTp: Type): DefDef = {
    val applyVParamss = List(List(ValDef(Modifiers(Flags.PARAM), name.tr, TypeTree(argTp), EmptyTree)))
    DefDef(NoMods, name.apply, Nil, applyVParamss, TypeTree(definitions.UnitTpe), literalUnit)
  }


  def mkAsInstanceOf(qual: Tree, tp: Type) =
    TypeApply(Select(qual, nme.asInstanceOf_), List(TypeTree(tp)))

  private def tpeOf(t: Tree): Type = t match {
    case _ if t.tpe != null                      => t.tpe
    case Try(body, Nil, _)                       => tpeOf(body)
    case Block(_, expr)                          => tpeOf(expr)
    case Literal(Constant(value)) if value == () => definitions.UnitTpe
    case Return(_)                               => definitions.NothingTpe
    case _                                       => NoType
  }

  def adaptToUnit(rhs: List[Tree]): Block =
    rhs match {
      case (rhs: Block) :: Nil if tpeOf(rhs) <:< definitions.UnitTpe  =>
        rhs
      case init :+ last if tpeOf(last) <:< definitions.UnitTpe        =>
        Block(init, last)
      case init :+ (last@Literal(Constant(())))                       =>
        Block(init, last)
      case init :+ (last@Block(_, Return(_) | Literal(Constant(())))) =>
        Block(init, last)
      case init :+ Block(stats, expr)                                 =>
        Block(init, Block(stats :+ expr, literalUnit))
      case _                                                          =>
        Block(rhs, literalUnit)
    }

  // TODO: why add the :Any type ascription to hide a tree of type Nothing? adaptToUnit doesn't seem to care
  def adaptToUnitIgnoringNothing(stats: List[Tree]): Block =
    stats match {
      case init :+ last if tpeOf(last) =:= definitions.NothingTpe =>
        adaptToUnit(init :+ Typed(last, TypeTree(definitions.AnyTpe)))
      case _                                                      =>
        adaptToUnit(stats)
    }



  private def derivedValueClassUnbox(cls: Symbol) =
    (cls.info.decls.find(sym => sym.isMethod && sym.asTerm.isParamAccessor) getOrElse NoSymbol)

  def mkZero(tp: Type): Tree = {
    val tpSym = tp.typeSymbol
    if (tpSym.isClass && tpSym.asClass.isDerivedValueClass) {
      val argZero = mkZero(derivedValueClassUnbox(tpSym).infoIn(tp).resultType)
      val baseType = tp.baseType(tpSym) // use base type here to dealias / strip phantom "tagged types" etc.

      // By explicitly attributing the types and symbols here, we subvert privacy.
      // Otherwise, ticket86PrivateValueClass would fail.

      // Approximately:
      // q"new ${valueClass}[$..targs](argZero)"
      val target: Tree = gen.mkAttributedSelect(
                                                 typecheck(atMacroPos(New(TypeTree(baseType)))), tpSym.asClass.primaryConstructor)

      val zero = gen.mkMethodCall(target, argZero :: Nil)
      // restore the original type which we might otherwise have weakened with `baseType` above
      typecheck(atMacroPos(gen.mkCast(zero, tp)))
    } else {
      gen.mkZero(tp)
    }
  }

  // TODO: when we run after erasure the annotation is not needed
  final def uncheckedBounds(tp: Type): Type = u.uncheckedBounds(tp)

  def uncheckedBoundsIfNeeded(t: Type): Type = {
    var quantified: List[Symbol] = Nil
    var badSkolemRefs: List[Symbol] = Nil
    t.foreach {
      case et: ExistentialType =>
        quantified :::= et.quantified
      case TypeRef(pre, sym, args) =>
        val illScopedSkolems = args.map(_.typeSymbol).filter(arg => arg.isExistentialSkolem && !quantified.contains(arg))
        badSkolemRefs :::= illScopedSkolems
      case _ =>
    }
    if (badSkolemRefs.isEmpty) t
    else t.map {
      case tp @ TypeRef(pre, sym, args) if args.exists(a => badSkolemRefs.contains(a.typeSymbol)) =>
        uncheckedBounds(tp)
      case t => t
    }
  }
}


/**
 * Utilities used in both `ExprBuilder` and `AnfTransform`.
 */
private[async] trait TransformUtils extends AsyncContext with PhasedTransform {
  import typingTransformers.{TypingTransformApi, typingTransform}
  import u._


  def maybeTry(block: Tree, catches: List[CaseDef], finalizer: Tree) =
    if (emitTryCatch) Try(block, catches, finalizer) else block

  lazy val IllegalStateExceptionClass = rootMirror.staticClass("java.lang.IllegalStateException")

  private lazy val Async_async   = asyncBase.asyncMethod(u)(asyncMacroSymbol)
  private lazy val Async_await   = asyncBase.awaitMethod(u)(asyncMacroSymbol)

  def isAsync(fun: Tree) = fun.symbol == Async_async
  def isAwait(fun: Tree) = fun.symbol == Async_await


  private lazy val Boolean_ShortCircuits: Set[Symbol] = {
    import definitions.BooleanClass
    def BooleanTermMember(name: String) = BooleanClass.typeSignature.member(newTermName(name).encodedName)
    val Boolean_&& = BooleanTermMember("&&")
    val Boolean_|| = BooleanTermMember("||")
    Set(Boolean_&&, Boolean_||)
  }

  private def isByName(fun: Tree): ((Int, Int) => Boolean) = {
    if (Boolean_ShortCircuits contains fun.symbol) (i, j) => true
    else if (fun.tpe == null) (x, y) => false
    else {
      val paramss = fun.tpe.paramss
      val byNamess = paramss.map(_.map(_.asTerm.isByNameParam))
      (i, j) => util.Try(byNamess(i)(j)).getOrElse(false)
    }
  }
  private def argName(fun: Tree): ((Int, Int) => TermName) = {
    val paramss = fun.tpe.paramss
    val namess = paramss.map(_.map(_.name.toTermName))
    (i, j) => util.Try(namess(i)(j)).getOrElse(TermName(s"arg_${i}_${j}"))
  }

  def isLabel(sym: Symbol): Boolean = sym.isLabel

  def substituteTrees(t: Tree, from: List[Symbol], to: List[Tree]): Tree =
    (new TreeSubstituter(from, to)).transform(t)

  /** Map a list of arguments to:
    * - A list of argument Trees
    * - A list of auxillary results.
    *
    * The function unwraps and rewraps the `arg :_*` construct.
    *
    * @param args The original argument trees
    * @param f  A function from argument (with '_*' unwrapped) and argument index to argument.
    * @tparam A The type of the auxillary result
    */
  private def mapArguments[A](args: List[Tree])(f: (Tree, Int) => (A, Tree)): (List[A], List[Tree]) = {
    args match {
      case args :+ Typed(tree, Ident(tpnme.WILDCARD_STAR)) =>
        val (a, argExprs :+ lastArgExpr) = (args :+ tree).zipWithIndex.map(f.tupled).unzip
        val exprs = argExprs :+ atPos(lastArgExpr.pos.makeTransparent)(Typed(lastArgExpr, Ident(tpnme.WILDCARD_STAR)))
        (a, exprs)
      case args                                            =>
        args.zipWithIndex.map(f.tupled).unzip
    }
  }

  case class Arg(expr: Tree, isByName: Boolean, argName: TermName)

  /**
   * Transform a list of argument lists, producing the transformed lists, and lists of auxillary
   * results.
   *
   * The function `f` need not concern itself with varargs arguments e.g (`xs : _*`). It will
   * receive `xs`, and it's result will be re-wrapped as `f(xs) : _*`.
   *
   * @param fun   The function being applied
   * @param argss The argument lists
   * @return      (auxillary results, mapped argument trees)
   */
  def mapArgumentss[A](fun: Tree, argss: List[List[Tree]])(f: Arg => (A, Tree)): (List[List[A]], List[List[Tree]]) = {
    val isByNamess: (Int, Int) => Boolean = isByName(fun)
    val argNamess: (Int, Int) => TermName = argName(fun)
    argss.zipWithIndex.map { case (args, i) =>
      mapArguments[A](args) {
        (tree, j) => f(Arg(tree, isByNamess(i, j), argNamess(i, j)))
      }
    }.unzip
  }


  def statsAndExpr(tree: Tree): (List[Tree], Tree) = tree match {
    case Block(stats, expr) => (stats, expr)
    case _                  => (List(tree), Literal(Constant(())))
  }

  def blockToList(tree: Tree): List[Tree] = tree match {
    case Block(stats, expr) => stats :+ expr
    case t                  => t :: Nil
  }

  def listToBlock(trees: List[Tree]): Block = trees match {
    case trees @ (init :+ last) =>
      val pos = trees.map(_.pos).reduceLeft(_ union _)
      Block(init, last).setType(last.tpe).setPos(pos)
  }

  def emptyConstructor: DefDef = {
    val emptySuperCall = Apply(Select(Super(This(tpnme.EMPTY), tpnme.EMPTY), nme.CONSTRUCTOR), Nil)
    DefDef(NoMods, nme.CONSTRUCTOR, List(), List(List()), TypeTree(), Block(List(emptySuperCall), Literal(Constant(()))))
  }

  /** Descends into the regions of the tree that are subject to the
    * translation to a state machine by `async`. When a nested template,
    * function, or by-name argument is encountered, the descent stops,
    * and `nestedClass` etc are invoked.
    */
  trait AsyncTraverser extends Traverser {
    def nestedClass(classDef: ClassDef): Unit = {
    }

    def nestedModule(module: ModuleDef): Unit = {
    }

    def nestedMethod(defdef: DefDef): Unit = {
    }

    def byNameArgument(arg: Tree): Unit = {
    }

    def function(function: Function): Unit = {
    }

    def patMatFunction(tree: Match): Unit = {
    }

    override def traverse(tree: Tree): Unit = {
      tree match {
        case _ if isAsync(tree) =>
          // Under -Ymacro-expand:discard, used in the IDE, nested async blocks will be visible to the outer blocks
        case cd: ClassDef          => nestedClass(cd)
        case md: ModuleDef         => nestedModule(md)
        case dd: DefDef            => nestedMethod(dd)
        case fun: Function         => function(fun)
        case m@Match(EmptyTree, _) => patMatFunction(m) // Pattern matching anonymous function under -Xoldpatmat of after `restorePatternMatchingFunctions`
        case q"$fun[..$targs](...$argss)" if argss.nonEmpty =>
          val isInByName = isByName(fun)
          for ((args, i) <- argss.zipWithIndex) {
            for ((arg, j) <- args.zipWithIndex) {
              if (!isInByName(i, j)) traverse(arg)
              else byNameArgument(arg)
            }
          }
          traverse(fun)
        case _                     => super.traverse(tree)
      }
    }
  }

  def transformAt(tree: Tree)(f: PartialFunction[Tree, (TypingTransformApi => Tree)]) = {
    typingTransform(tree)((tree, api) => {
      if (f.isDefinedAt(tree)) f(tree)(api)
      else api.default(tree)
    })
  }

  def toMultiMap[A, B](abs: Iterable[(A, B)]): mutable.LinkedHashMap[A, List[B]] = {
    // LinkedHashMap for stable order of results.
    val result = new mutable.LinkedHashMap[A, ListBuffer[B]]()
    for ((a, b) <- abs) {
      val buffer = result.getOrElseUpdate(a, new ListBuffer[B])
      buffer += b
    }
    result.map { case (a, b) => (a, b.toList) }
  }

  // Attributed version of `TreeGen#mkCastPreservingAnnotations`
  def mkAttributedCastPreservingAnnotations(tree: Tree, tp: Type): Tree = {
    atPos(tree.pos) {
      val casted = typecheck(gen.mkCast(tree, uncheckedBounds(tp.withoutAnnotations).dealias))
      Typed(casted, TypeTree(tp)).setType(tp)
    }
  }

  def withAnnotation(tp: Type, ann: Annotation): Type = withAnnotations(tp, List(ann))

  def withAnnotations(tp: Type, anns: List[Annotation]): Type = tp match {
    case AnnotatedType(existingAnns, underlying) => annotatedType(anns ::: existingAnns, underlying)
    case ExistentialType(quants, underlying) => existentialAbstraction(quants, withAnnotations(underlying, anns))
    case _ => annotatedType(anns, tp)
  }


  def thisType(sym: Symbol): Type = {
    if (sym.isClass) sym.asClass.thisPrefix
    else NoPrefix
  }


  /**
   * Efficiently decorate each subtree within `t` with the result of `t exists isAwait`,
   * and return a function that can be used on derived trees to efficiently test the
   * same condition.
   *
   * If the derived tree contains synthetic wrapper trees, these will be recursed into
   * in search of a sub tree that was decorated with the cached answer.
   */
  final def containsAwaitCached(t: Tree): Tree => Boolean = {
    if (asyncMacroSymbol == null) return (t => false)

    def treeCannotContainAwait(t: Tree) = t match {
      case _: Ident | _: TypeTree | _: Literal => true
      case _ => isAsync(t)
    }
    def shouldAttach(t: Tree) = !treeCannotContainAwait(t)
    def attachContainsAwait(t: Tree): Unit = if (shouldAttach(t)) {
      t.updateAttachment(ContainsAwait)
      t.removeAttachment[NoAwait.type]
    }
    def attachNoAwait(t: Tree): Unit = if (shouldAttach(t)) {
      t.updateAttachment(NoAwait)
    }
    object markContainsAwaitTraverser extends Traverser {
      var stack: List[Tree] = Nil

      override def traverse(tree: Tree): Unit = {
        stack ::= tree
        try {
          if (isAsync(tree)) {
            ;
          } else {
            if (isAwait(tree))
              stack.foreach(attachContainsAwait)
            else
              attachNoAwait(tree)
            super.traverse(tree)
          }
        } finally stack = stack.tail
      }
    }
    markContainsAwaitTraverser.traverse(t)

    (t: Tree) => {
      object traverser extends Traverser {
        var containsAwait = false
        override def traverse(tree: Tree): Unit = {
          if (!tree.hasAttachment[NoAwait.type]) {
            if (tree.hasAttachment[ContainsAwait.type])
              containsAwait = true
            else if (!treeCannotContainAwait(t))
              super.traverse(tree)
          }
        }
      }
      traverser.traverse(t)
      traverser.containsAwait
    }
  }

  final def cleanupContainsAwaitAttachments(t: Tree): t.type = {
    t.foreach {t =>
      t.removeAttachment[ContainsAwait.type]
      t.removeAttachment[NoAwait.type]
    }
    t
  }

  // First modification to translated patterns:
  //  - Set the type of label jumps to `Unit`
  //  - Propagate this change to trees known to directly enclose them:
  //    ``If` / `Block`) adjust types of enclosing
  final def adjustTypeOfTranslatedPatternMatches(t: Tree, owner: Symbol): Tree = {
    import definitions.UnitTpe

    typingTransform(t, owner) {
      (tree, api) =>
        tree match {
          case LabelDef(name, params, rhs) =>
            val rhs1 = api.recur(rhs)
            if (rhs1.tpe =:= UnitTpe) {
              internal.setInfo(tree.symbol, internal.methodType(tree.symbol.info.paramLists.head, UnitTpe))
              treeCopy.LabelDef(tree, name, params, rhs1)
            } else {
              treeCopy.LabelDef(tree, name, params, rhs1)
            }
          case Block(stats, expr) =>
            val stats1 = stats map api.recur
            val expr1 = api.recur(expr)
            if (expr1.tpe =:= UnitTpe)
              internal.setType(treeCopy.Block(tree, stats1, expr1), UnitTpe)
            else
              treeCopy.Block(tree, stats1, expr1)
          case If(cond, thenp, elsep) =>
            val cond1 = api.recur(cond)
            val thenp1 = api.recur(thenp)
            val elsep1 = api.recur(elsep)
            if (thenp1.tpe =:= definitions.UnitTpe && elsep.tpe =:= UnitTpe)
              internal.setType(treeCopy.If(tree, cond1, thenp1, elsep1), UnitTpe)
            else
              treeCopy.If(tree, cond1, thenp1, elsep1)
          case Apply(fun, args) if isLabel(fun.symbol) =>
            internal.setType(treeCopy.Apply(tree, api.recur(fun), args map api.recur), UnitTpe)
          case vd @ ValDef(mods, name, tpt, rhs) if isCaseTempVal(vd.symbol) =>
            def addUncheckedBounds(t: Tree) = {
              typingTransform(t, owner) {
                (tree, api) =>
                  if (tree.tpe == null) tree else internal.setType(api.default(tree), uncheckedBoundsIfNeeded(tree.tpe))
              }

            }
            val uncheckedRhs = addUncheckedBounds(api.recur(rhs))
            val uncheckedTpt = addUncheckedBounds(tpt)
            internal.setInfo(vd.symbol, uncheckedBoundsIfNeeded(vd.symbol.info))
            treeCopy.ValDef(vd, mods, name, uncheckedTpt, uncheckedRhs)
          case t => api.default(t)
        }
    }
  }

  private def isCaseTempVal(s: Symbol) = {
    s.isTerm && s.asTerm.isVal && s.isSynthetic && s.name.toString.startsWith("x")
  }


  final def mkMutableField(tpt: Type, name: TermName, init: Tree): List[Tree] = {
    if (isPastTyper) {
      import scala.reflect.internal.Flags._
      // If we are running after the typer phase (ie being called from a compiler plugin)
      // we have to create the trio of members manually.
      val field = ValDef(Modifiers(MUTABLE | PRIVATE | LOCAL), name + " ", TypeTree(tpt), init)
      val getter = DefDef(Modifiers(ACCESSOR | STABLE), name, Nil, Nil, TypeTree(tpt), Select(This(tpnme.EMPTY), field.name))
      val setter = DefDef(Modifiers(ACCESSOR), name + "_=", Nil, List(List(ValDef(NoMods, TermName("x"), TypeTree(tpt), EmptyTree))), TypeTree(definitions.UnitTpe), Assign(Select(This(tpnme.EMPTY), field.name), Ident(TermName("x"))))
      field :: getter :: setter :: Nil
    } else {
      val result = ValDef(NoMods, name, TypeTree(tpt), init)
      result :: Nil
    }
  }

  def deriveLabelDef(ld: LabelDef, applyToRhs: Tree => Tree): LabelDef = {
    val rhs2 = applyToRhs(ld.rhs)
    val ld2 = treeCopy.LabelDef(ld, ld.name, ld.params, rhs2)
    if (ld eq ld2) ld
    else {
      val info2 = ld2.symbol.info match {
        case MethodType(params, p) => internal.methodType(params, rhs2.tpe)
        case t => t
      }
      internal.setInfo(ld2.symbol, info2)
      ld2
    }
  }
  object MatchEnd {
    def unapply(t: Tree): Option[LabelDef] = t match {
      case ValDef(_, _, _, t) => unapply(t)
      case ld: LabelDef if ld.name.toString.startsWith("matchEnd") => Some(ld)
      case _ => None
    }
  }
}

case object ContainsAwait
case object NoAwait
