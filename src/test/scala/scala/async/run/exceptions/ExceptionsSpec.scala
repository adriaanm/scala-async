/*
 * Copyright (C) 2012-2018 Lightbend Inc. <http://www.lightbend.com>
 */

package scala.async
package run
package exceptions

import scala.async.Async.{async, await}

import scala.concurrent.{Future, ExecutionContext, Await}
import ExecutionContext.Implicits._
import scala.concurrent.duration._
import scala.reflect.ClassTag

import org.junit.Test

class ExceptionsSpec {

  @Test
  def `uncaught exception within async`(): Unit = {
    val fut = async { throw new Exception("problem") }
    intercept[Exception] { Await.result(fut, 2.seconds) }
  }

  @Test
  def `uncaught exception within async after await`(): Unit = {
    val base = Future { "five!".length }
    val fut = async {
      val len = await(base)
      throw new Exception(s"illegal length: $len")
    }
    intercept[Exception] { Await.result(fut, 2.seconds) }
  }

  @Test
  def `await failing future within async`(): Unit = {
    val base = Future[Int] { throw new Exception("problem") }
    val fut = async {
      val x = await(base)
      x * 2
    }
    intercept[Exception] { Await.result(fut, 2.seconds) }
  }

  @Test
  def `await failing future within async after await`(): Unit = {
    val base = Future[Any] { "five!".length }
    val fut = async {
      val a = await(base.mapTo[Int])                          // result: 5
      val b = await((Future { (a * 2).toString }).mapTo[Int]) // result: ClassCastException
      val c = await(Future { (7 * 2).toString })              // result: "14"
      b + "-" + c
    }
    intercept[ClassCastException] { Await.result(fut, 2.seconds) }
  }

}
