/*
 * Copyright (C) 2012-2018 Lightbend Inc. <http://www.lightbend.com>
 */

package scala.async.internal

import scala.language.experimental.macros
import scala.reflect.api.Universe
import scala.reflect.internal.SymbolTable
import scala.reflect.macros.Context

object AsyncId extends AsyncBase {
  lazy val futureSystem = IdentityFutureSystem
  type FS = IdentityFutureSystem.type

  def async[T](body: => T) = macro asyncIdImpl[T]

  def asyncIdImpl[T: c.WeakTypeTag](c: Context)(body: c.Expr[T]): c.Expr[T] = asyncImpl[T](c)(body)(c.literalUnit)
}

object AsyncTestLV extends AsyncBase {
  lazy val futureSystem = IdentityFutureSystem
  type FS = IdentityFutureSystem.type

  def async[T](body: T) = macro asyncIdImpl[T]

  def asyncIdImpl[T: c.WeakTypeTag](c: Context)(body: c.Expr[T]): c.Expr[T] = asyncImpl[T](c)(body)(c.literalUnit)

  var log: List[(String, Any)] = Nil
  def assertNulledOut(a: Any): Unit = assert(log.exists(_._2 == a), AsyncTestLV.log)
  def assertNotNulledOut(a: Any): Unit = assert(!log.exists(_._2 == a), AsyncTestLV.log)
  def clear(): Unit = log = Nil

  def apply(name: String, v: Any): Unit =
    log ::= (name -> v)

  protected[async] override def nullOut(u: Universe)(name: u.Expr[String], v: u.Expr[Any]): u.Expr[Unit] =
    u.reify { scala.async.internal.AsyncTestLV(name.splice, v.splice) }
}

/**
 * A trivial implementation of [[FutureSystem]] that performs computations
 * on the current thread. Useful for testing.
 */
class Box[A] {
  var a: A = _
}
object IdentityFutureSystem extends FutureSystem {
  type Prom[A] = Box[A]

  type Fut[A] = A
  type ExecContext = Unit
  type Tryy[A] = scala.util.Try[A]

  def mkOps(u: SymbolTable): Ops[u.type] = new IdentityOps[u.type](u)
  class IdentityOps[U <: SymbolTable](u0: U) extends Ops[U](u0) {
    import u._

    def execContext: u.Expr[Unit] = literalUnitExpr

    def promType[A: WeakTypeTag]: Type = weakTypeOf[Box[A]]
    def tryType[A: WeakTypeTag]: Type = weakTypeOf[scala.util.Try[A]]
    def execContextType: Type = weakTypeOf[Unit]

    def createProm[A: WeakTypeTag]: Expr[Prom[A]] = reify {
      new Prom[A]()
    }

    def promiseToFuture[A: WeakTypeTag](prom: Expr[Prom[A]]) = reify {
      prom.splice.a
    }

    def future[A: WeakTypeTag](t: Expr[A])(execContext: Expr[ExecContext]) = t

    def onComplete[A, U](future: Expr[Fut[A]], fun: Expr[Tryy[A] => U],
                         execContext: Expr[ExecContext]): Expr[Unit] = reify {
      fun.splice.apply(util.Success(future.splice))
      literalUnitExpr.splice
    }

    def completeProm[A](prom: Expr[Prom[A]], value: Expr[Tryy[A]]): Expr[Unit] = reify {
      prom.splice.a = value.splice.get
      literalUnitExpr.splice
    }

    def tryyIsFailure[A](tryy: Expr[Tryy[A]]): Expr[Boolean] = reify {
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
