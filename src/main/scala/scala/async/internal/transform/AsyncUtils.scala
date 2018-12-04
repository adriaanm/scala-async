/*
 * Copyright (C) 2012-2018 Lightbend Inc. <http://www.lightbend.com>
 */

package scala.async.internal.transform

object AsyncUtils {
  private def enabled(level: String) = sys.props.getOrElse(s"scala.async.$level", "false").equalsIgnoreCase("true")

  private[async] val verbose = true //enabled("debug")
  private[async] val trace   = true  //enabled("trace")

  @inline private[async] def vprintln(s: => Any): Unit = if (verbose) println(s"[async] $s")

  @inline private[async] def trace(s: => Any): Unit = if (trace) println(s"[async] $s")
}
