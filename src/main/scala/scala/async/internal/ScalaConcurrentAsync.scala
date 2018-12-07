/*
 * Copyright (C) 2012-2018 Lightbend Inc. <http://www.lightbend.com>
 */

package scala
package async
package internal

import scala.concurrent.Future
import scala.reflect.macros.whitebox.Context

object ScalaConcurrentAsync extends AsyncBase {
  type FS = ScalaConcurrentFutureSystem.type
  val futureSystem: FS = ScalaConcurrentFutureSystem

  override def asyncImpl[T: c.WeakTypeTag](c: Context)
                                          (body: c.Expr[T])
                                          (execContext: c.Expr[futureSystem.ExecContext]): c.Expr[Future[T]] = {
    super.asyncImpl[T](c)(body)(execContext)
  }
}
