package simulator

import scala.swing.event.Event

//we will use our own event so as to process java event in a clean way
trait SimulatorEvent extends Event

final case class ToggleColorEvent(field: String) extends SimulatorEvent

final case class ExpandLayer(field: String) extends SimulatorEvent

final case class CollapseLayer(field: String) extends SimulatorEvent