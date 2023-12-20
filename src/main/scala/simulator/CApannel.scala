package simulator

import java.awt.{BasicStroke, Color, Dimension, Graphics2D, Image, Point, Polygon, geom}
import simulator.CAtype._

import scala.swing.Swing._
import scala.swing.event._
import scala.swing.{Dimension, Frame, MainFrame, Panel, SimpleSwingApplication}
import triangulation.{DelaunayTriangulator, NotEnoughPointsException, Triangle2D, Vector2D, Voronoi}

import scala.collection.JavaConverters._
import triangulation.Utility._

import Color._
import compiler.E

/**
 * pannel for drawing one CA , together with relevant information
 * @param env contains all what's needed to draw
 */
class CApannel(width: Int, height: Int, env: Env, progCA: CAloops2) extends Panel {
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

      override def drawText(s: String, i: Int, j: Int) = g.drawString(s, i, j)
      override def drawPoint(x: Int, y: Int): Unit = {
        g.setStroke(new BasicStroke(2))
        g.drawLine(x, y, x, y)
      }
    }
    drawCA(gscreen, env)
  }

  /**
   *
   * @param g delegate the fillPolygone to either printing on the screen, or in a svg file
   * @param env
   */
  def drawCA(g: myGraphics2D, env: Env) = {
    def drawPoints(c: Color) = {
      g.setColor(c);
      for (p <- env.medium.displayedPoint)
        g.drawPoint(p.x.toInt, p.y.toInt)
    }

    def drawText(c: Color) = {
      g.setColor(c);
      g.drawText(env.bugs.mkString(","), 0, height - 10)
    }

    def drawTriangles(c: Color) = {
      g.setColor(c);
      for (t <- env.medium.triangleSoup) {
        g.drawPolygon(toPolygon(t))
      }
    }

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
    /*

        def drawCAtestInitBoolV(initMethod: env.medium.InitMold, c: Color) = {
          g.setColor(c)
          for (i <- 0 until initMethod.boolVField.size)
            for (j <- 0 until initMethod.boolVField(0).size)
              if (initMethod.boolVField(i)(j)) {
                val v: Vector2D = env.medium.vertice(i)(j).get
                g.fillPolygon(env.medium.voronoi(v).polygon)
              }
        }

        def drawCAtestInit(initMethod: env.medium.InitMold, c: Color) = {
          g.setColor(c)
          for (d <- 0 until initMethod.locus.density)
            for (i <- 0 until env.medium.nbLineCA)
              for (j <- 0 until env.medium.nbColCA)
                if (initMethod.memFields(d)(i)(j)) {
                  assert(env.medium.locusPlane(initMethod.locus)(d)(i)(j).isDefined, "defined is defined exactly when the point exists")
                  val v: Vector2D = env.medium.locusPlane(initMethod.locus)(d)(i)(j).get
                  g.fillPolygon(env.medium.voronoi(v).polygon)
                }
        }
    */

    def drawCAcolorVoronoi() = {
      //env.computeVoronoirColors() //painting allways need to recompute the colors, it would seem
      for (v: Voronoi <- env.medium.voronoi.values)
        if (v.color != Color.black || v.corner.isDefined //we print the corners even it they are black, because they can overlap
        ) {
          g.setColor(v.color)
          g.fillPolygon(v.polygon)
        }
    }

    //drawCAtestInit(env.medium.defInit(E()),red)
    drawCAcolorVoronoi()
    drawCAinsideContour(gray)
    drawCA1DborderContour(white)
    //drawTriangles(gray)
    drawPoints(white)
    drawText(white)
  }

}




