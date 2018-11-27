/*
 * Copyright (C) 2012-2018 Lightbend Inc. <http://www.lightbend.com>
 */

package scala.async.internal.transform

private[async] final class StateAssigner {
  private var current = StateAssigner.Initial

  def nextState(): Int = try current finally current += 1
}

object StateAssigner {
  final val Initial = 0
}
