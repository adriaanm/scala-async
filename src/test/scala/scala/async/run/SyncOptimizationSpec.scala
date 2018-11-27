/*
 * Copyright (C) 2012-2018 Lightbend Inc. <http://www.lightbend.com>
 */

package scala.async.run

import org.junit.Test
import scala.async.Async._
import scala.concurrent._
import scala.concurrent.duration._
import ExecutionContext.Implicits._

class SyncOptimizationSpec {
  @Test
  def awaitOnCompletedFutureRunsOnSameThread: Unit = {

    def stackDepth = Thread.currentThread().getStackTrace.length

    val future = async {
      val thread1 = Thread.currentThread
      val stackDepth1 = stackDepth

      val f = await(Future.successful(1))
      val thread2 = Thread.currentThread
      val stackDepth2 = stackDepth
      assert(thread1 == thread2)
      assert(stackDepth1 == stackDepth2)
    }
    Await.result(future, 10.seconds)
  }

}
