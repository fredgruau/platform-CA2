package simulator

import java.awt.{Color, Graphics2D, Point, Polygon, geom}

import simulator.Simulator.CAtype.myGraphics2D

import scala.swing.Swing._
import scala.swing.event._
import scala.swing.{Dimension, Frame, MainFrame, Panel, SimpleSwingApplication}
import java.awt.Dimension
import java.awt.Image

import triangulation.{DelaunayTriangulator, NotEnoughPointsException, Triangle2D, Vector2D}
import scala.collection.JavaConverters._
import triangulation.Utility._
import Color._

/**
 * pannel for drawing one CA , together with relevant information
 *
 * @param env contains all what's needed to draw
 */
class CApannel(width: Int, height: Int, env: Env, progCA: CAloops) extends Panel {
  background = Color.black
  preferredSize = (width, height)
  focusable = true


  /** when zooming on a sub part we need to draw only a small portion */
  private val subca: Dimension = null
  /** rendering is improved by first drawing in an image buffer */
  private var imageBuffer: Image = null


  /** called by the system, in order to paint or repaint the pannel */
  override def paintComponent(g: Graphics2D): Unit = {
    super.paintComponent(g)
    val gscreen = new myGraphics2D {
      override def setColor(c: Color): Unit = g.setColor(c)

      override def fillPolygon(p: Polygon): Unit = g.fillPolygon(p)

      override def drawPolygon(p: Polygon): Unit = g.drawPolygon(p)
    }
    drawCA(gscreen, env)
  }

  /**
   *
   * @param g delegate the fillPolygone to either printing on the screen, or in a svg file
   * @param env
   */
  def drawCA(g: myGraphics2D, env: Env) = {
    def drawCAinsideContour(c: Color) = {
      g.setColor(c);
      for ((_, v) <- env.medium.voronoi)
        if (v.sides.isEmpty)
          g.drawPolygon(v.polygon)
    }

    def drawCA1DborderContour(c: Color) = {
      g.setColor(c);
      for ((_, v) <- env.medium.voronoi)
        if (v.sides.nonEmpty)
          g.drawPolygon(v.polygon)
    }

    def drawCAtestInit(initMethod: env.medium.InitMold, c: Color) = {
      g.setColor(c)
      for (i <- 0 until initMethod.boolVField.size)
        for (j <- 0 until initMethod.boolVField(0).size)
          if (initMethod.boolVField(i)(j)) {
            val v: Vector2D = env.medium.vertice(i)(j).get
            g.fillPolygon(env.medium.voronoi(v).polygon)
          }
    }

    def drawCAcolorVoronoi() = {
      //env.computeVoronoirColors() //painting allways need to recompute the colors, it would seem
      for (v <- env.medium.voronoi.values)
        if (v.color != Color.black) {
          g.setColor(v.color)
          g.fillPolygon(v.polygon)
        }
    }

    drawCAinsideContour(gray)
    drawCA1DborderContour(white)
    // drawCAtestInit(env.medium.centerInit,red)
    drawCAcolorVoronoi()
  }

}




