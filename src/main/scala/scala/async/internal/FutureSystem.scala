/*
 * Copyright (C) 2012-2018 Lightbend Inc. <http://www.lightbend.com>
 */
package scala.async.internal

import scala.language.higherKinds
import scala.reflect.internal.SymbolTable

/**
 * An abstraction over a future system.
 *
 * Used by the macro implementations in [[scala.async.AsyncBase]] to
 * customize the code generation.
 *
 * The API mirrors that of `scala.concurrent.Future`, see the instance
 * [[ScalaConcurrentFutureSystem]] for an example of how
 * to implement this.
 */
trait FutureSystem {
  /** A container to receive the final value of the computation */
  type Prom[A]
  /** A (potentially in-progress) computation */
  type Fut[A]
  /** An execution context, required to create or register an on completion callback on a Future. */
  type ExecContext
  /** Any data type isomorphic to scala.util.Try. */
  type Tryy[T]

  // We could do with just Universe <: reflect.api.Universe if it wasn't Expr and WeakTypeTag
  // (the api effectively doesn't let you call these factories since there's no way to get at the Tree- and TypeCreators)
  abstract class Ops[Universe <: SymbolTable](val u: Universe, val isPastErasure: Boolean) {
    import u._

    def Expr[T: WeakTypeTag](tree: Tree): Expr[T] = u.Expr[T](rootMirror, FixedMirrorTreeCreator(rootMirror, tree))
    def WeakTypeTag[T](tpe: Type): WeakTypeTag[T] = u.WeakTypeTag[T](rootMirror, FixedMirrorTypeCreator(rootMirror, tpe))

    def literalUnitExpr = Expr[Unit](Literal(Constant(())))

    def promType(tp: Type): Type
    def tryType(tp: Type): Type
//    def execContextType: Type
    def stateMachineClassParents: List[Type] = Nil

    /** Create an empty promise */
    def createProm[A: WeakTypeTag]: Expr[Prom[A]]

    /** Extract a future from the given promise. */
    def promiseToFuture[A: WeakTypeTag](prom: Expr[Prom[A]]): Expr[Fut[A]]

    /** Construct a future to asynchronously compute the given expression */
    def future[A: WeakTypeTag](a: Expr[A])(execContext: Expr[ExecContext]): Expr[Fut[A]]

    /** Register an call back to run on completion of the given future */
    def onComplete[A, B](future: Expr[Fut[A]], fun: Expr[Tryy[A] => B],
                         execContext: Expr[ExecContext]): Expr[Unit]

    def continueCompletedFutureOnSameThread = false

    /** Return `null` if this future is not yet completed, or `Tryy[A]` with the completed result
      * otherwise
      */
    def getCompleted[A: WeakTypeTag](future: Expr[Fut[A]]): Expr[Tryy[A]] =
      throw new UnsupportedOperationException("getCompleted not supported by this FutureSystem")

    /** Complete a promise with a value */
    def completeProm[A](prom: Expr[Prom[A]], value: Expr[Tryy[A]]): Expr[Unit]
    def completeWithSuccess[A: WeakTypeTag](prom: Expr[Prom[A]], value: Expr[A]): Expr[Unit] = completeProm(prom, tryySuccess(value))

    def tryyIsFailure[A](tryy: Expr[Tryy[A]]): Expr[Boolean]

    def tryyGet[A](tryy: Expr[Tryy[A]]): Expr[A]
    def tryySuccess[A: WeakTypeTag](a: Expr[A]): Expr[Tryy[A]]
    def tryyFailure[A: WeakTypeTag](a: Expr[Throwable]): Expr[Tryy[A]]

    /** A hook for custom macros to transform the tree post-ANF transform */
    def postAnfTransform(tree: Block): Block = tree

    /** A hook for custom macros to selectively generate and process a Graphviz visualization of the transformed state machine */
    def dot(enclosingOwner: Symbol, macroApplication: Tree): Option[(String => Unit)] = None
  }

  def mkOps(u: SymbolTable, isPastErasure: Boolean = false): Ops[u.type]

  @deprecated("No longer honoured by the macro, all generated names now contain $async to avoid accidental clashes with lambda lifted names", "0.9.7")
  def freshenAllNames: Boolean = false
  def emitTryCatch: Boolean = true
  @deprecated("No longer honoured by the macro, all generated names now contain $async to avoid accidental clashes with lambda lifted names", "0.9.7")
  def resultFieldName: String = "result"
}

object ScalaConcurrentFutureSystem extends FutureSystem {
  import scala.concurrent._

  type Prom[A] = Promise[A]
  type Fut[A] = Future[A]
  type ExecContext = ExecutionContext
  type Tryy[A] = scala.util.Try[A]

  def mkOps(u: SymbolTable, isPastErasure: Boolean = false): Ops[u.type] = new ScalaConcurrentOps[u.type](u, isPastErasure)
  class ScalaConcurrentOps[Universe <: SymbolTable](u0: Universe, isPastErasure: Boolean) extends Ops[Universe](u0, isPastErasure) {
    import u._

    def promType(tp: Type): Type = appliedType(weakTypeOf[Promise[_]], tp)
    def tryType(tp: Type): Type = appliedType(weakTypeOf[scala.util.Try[_]], tp)
//    def execContextType: Type = weakTypeOf[ExecutionContext]

    def createProm[A: WeakTypeTag]: Expr[Prom[A]] = reify {
      Promise[A]()
    }

    def promiseToFuture[A: WeakTypeTag](prom: Expr[Prom[A]]) = reify {
      prom.splice.future
    }

    def future[A: WeakTypeTag](a: Expr[A])(execContext: Expr[ExecContext]) = reify {
      Future(a.splice)(execContext.splice)
    }

    def onComplete[A, B](future: Expr[Fut[A]], fun: Expr[scala.util.Try[A] => B],
                         execContext: Expr[ExecContext]): Expr[Unit] = reify {
      future.splice.onComplete(fun.splice)(execContext.splice)
    }

    override def continueCompletedFutureOnSameThread: Boolean = true

    override def getCompleted[A: WeakTypeTag](future: Expr[Fut[A]]): Expr[Tryy[A]] = reify {
      if (future.splice.isCompleted) future.splice.value.get else null
    }

    def completeProm[A](prom: Expr[Prom[A]], value: Expr[scala.util.Try[A]]): Expr[Unit] = reify {
      prom.splice.complete(value.splice)
      literalUnitExpr.splice
    }

    def tryyIsFailure[A](tryy: Expr[scala.util.Try[A]]): Expr[Boolean] = reify {
      tryy.splice.isFailure
    }

    def tryyGet[A](tryy: Expr[Tryy[A]]): Expr[A] = reify {
      tryy.splice.get
    }
    def tryySuccess[A: WeakTypeTag](a: Expr[A]): Expr[Tryy[A]] = reify {
      scala.util.Success[A](a.splice)
    }
    def tryyFailure[A: WeakTypeTag](a: Expr[Throwable]): Expr[Tryy[A]] = reify {
      scala.util.Failure[A](a.splice)
    }
  }
}
