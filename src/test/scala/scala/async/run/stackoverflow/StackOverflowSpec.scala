/*
 * Copyright (C) 2012-2018 Lightbend Inc. <http://www.lightbend.com>
 */

package scala.async
package run
package stackoverflow

import org.junit.Test
import scala.async.internal.AsyncId


class StackOverflowSpec {

  @Test
  def stackSafety(): Unit = {
    import AsyncId._
    async {
      var i = 100000000
      while (i > 0) {
        if (false) {
          await(())
        }
        i -= 1
      }
    }
  }
}
