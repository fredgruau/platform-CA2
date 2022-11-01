package simulator

import java.awt.{Color, Graphics2D, Point, Polygon, geom}
import simulator.Simulator.CAtype.myGraphics2D
import scala.swing.Swing._
import scala.swing.event._
import scala.swing.{Frame, MainFrame, Panel, SimpleSwingApplication}

/** draws CA */
class CApannel(env: Env) extends Panel {

  background = Color.white
  preferredSize = (300, 200)
  focusable = true

  /*    listenTo(mouse.clicks, mouse.moves, keys)

      reactions += {
        case e: MousePressed =>
          moveTo(e.point)
          requestFocusInWindow()
        case e: MouseDragged => lineTo(e.point)
        case e: MouseReleased => lineTo(e.point)
        case KeyTyped(_, 'c', _, _) =>
          path = new geom.GeneralPath
          repaint()
        case _: FocusLost => repaint()
      }*/


  def polygoneTest(j: Int, k: Int): Polygon = {
    val p = new Polygon
    for (i <- 0 until 5) {
      p.addPoint((j + 50 * Math.cos(i * 2 * Math.PI / 5)).toInt, (k + 50 * Math.sin(i * 2 * Math.PI / 5)).toInt)
    }
    p


  }

  override def paintComponent(g: Graphics2D): Unit = {
    super.paintComponent(g)
    val gscreen = new myGraphics2D {
      override def setColor(c: Color): Unit = g.setColor(c)

      override def fillPolygon(p: Polygon): Unit = g.fillPolygon(p)

      override def drawPolygon(p: Polygon): Unit = g.drawPolygon(p)
    }
    drawCA(gscreen, env)
    val h = size.height
  }


  def drawCA(g: myGraphics2D, env: Env) = {}

}
