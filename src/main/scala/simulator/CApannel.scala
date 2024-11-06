package simulator

import compiler.Locus.{allLocus, locusEv, locusV}

import java.awt.{BasicStroke, Color, Dimension, Graphics2D, Image, Point, Polygon, geom}
import simulator.CAtype._

import scala.swing.Swing._
import scala.swing.event._
import scala.swing.{Dimension, Font, Frame, MainFrame, Panel, SimpleSwingApplication}
import triangulation.{DelaunayTriangulator, NotEnoughPointsException, Triangle2D, Vector2D, Voroonoi}

import scala.collection.JavaConverters._
import triangulation.Utility._

import Color._
import compiler.{E, Locus}
import dataStruc.Coord2D

import scala.collection.immutable
import scala.collection.immutable.HashSet
import scala.swing.MenuBar.NoMenuBar.font
import scala.util.Random

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
      import java.awt.{Font}
      override def drawText(s: String, i: Int, j: Int) = {
        val font = new Font("Serif", Font.PLAIN, 24); // Remplace "Serif" par le nom de la police souhaitée et 24 par la taille de police désirée
        g.setFont(font);
        g.drawString(s, i, j)
      }
      override def drawPoint(x: Int, y: Int, size:Int): Unit = {
        g.setStroke(new BasicStroke(size))
        g.drawLine(x, y, x, y)
      }

      override def drawLine(x: Int, y: Int, x2: Int, y2: Int): Unit = {
        g.setStroke(new BasicStroke(1))
        g.drawLine(x, y, x2, y2)
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

    val rand = new Random()
    def randColor=new Color(rand.nextFloat, rand.nextFloat, rand.nextFloat)


    def drawText(c: Color) = {
      g.setColor(c);
      if(env.bugs.nonEmpty)
        g.drawText("BUG: "+env.bugs.mkString(","), 100, /*height -*/ 100)
    }
    def drawTriangles(c: Color,triangleSoup:List[Triangle2D]) = {
      g.setColor(c);
      for (t <- triangleSoup)
        g.drawPolygon(toPolygon(t))
    }

    def fillTriangles(c: Color,triangleSoup:List[Triangle2D]) = {
      g.setColor(c);
      for (t <- triangleSoup)
        g.fillPolygon(toPolygon(t))
    }

    def drawTrianglesVEv(c: Color,triangleSoup:List[Triangle2D]) = {
      g.setColor(c);
      val targetLoci: Set[Locus]=HashSet(locusV,locusEv)
      val locusOfPoint:immutable.HashMap[Vector2D,Locus]=immutable.HashMap.empty++allLocus.map((l:Locus) => env.medium.pointSet(l).toList.map((v:Vector2D)=>(v->l))).flatten


      for (t <- triangleSoup) {
        val lociSummit: Set[Locus] =HashSet(t.a,t.b,t.c).map (locusOfPoint(_))
        if(  targetLoci.subsetOf(lociSummit))
        //g.setColor(randColor);
        g.drawPolygon(toPolygon(t))
      }
    }

    def drawdebug(c:Color)={
      g.setColor(c)
      for ((p1,p2)<-env.medium.bug) {
        g.drawLine(p1.x.toInt,p1.y.toInt,p2.x.toInt,p2.y.toInt)
        g.drawPoint(p1.x.toInt, p1.y.toInt,6)
        g.drawPoint(p2.x.toInt, p2.y.toInt,6)
      }
    }

    def drawEdges(c: Color) = {
      g.setColor(c);
     // env.medium.resetLocusNeigbors
     // for (p <- env.medium.displayedPoint)
      //  for (p2<- env.medium.locusNeighbors(p))
      //  g.drawLine(p.x.toInt,p.y.toInt,p2.x.toInt,p2.y.toInt)
      for(e<-env.medium.planarGraph.edges)
        g.drawLine(e.src.x.toInt,e.src.y.toInt,e.target.x.toInt,e.target.y.toInt)
    }
    /** used for debug */
    def drawFaces(): Unit = {
      for(f<-env.medium.planarGraph.faces)
        if( f.border.size>6 && !f.outerBorder && rand.nextBoolean()&& rand.nextBoolean()  )//
        {
          g.setColor(WHITE)
          g.fillPolygon(f.toPolygon)
          g.setColor(black)

          g.drawPolygon(f.toPolygon)
          for(p<-f.border)
            g.drawPoint(p.src.x.toInt,p.src.y.toInt,6)
        }
    }

    def drawCrossedFaces(): Unit = {
      g.setColor(gray)
      for(f<-env.medium.planarGraph.faces)
        if(f.isCrossing && f.border.size<31 && rand.nextBoolean()&& rand.nextBoolean() )  //we do not fill the outer border which is allowed to have crossing, due to two pending edges
          g.fillPolygon(f.toPolygon)
    }


    def drawCAinsideContour(c: Color) = {
      g.setColor(c);
      for ((_, v) <- env.medium.theVoronois)
        if (v.sides.isEmpty)
          g.drawPolygon(v.polygon)
    }

    def drawCA1DborderContour(c: Color) = {
      g.setColor(c);
      for ((_, v) <- env.medium.theVoronois)
        if (v.isBorder)
          g.drawPolygon(v.polygon)
    }
    def drawOutsideFace()={
      env.medium.planarGraph.setOuterBorder()
      val outBorder=env.medium.planarGraph.outerBorder.border
      for(e<-outBorder) {
        if(outBorder.contains(e.miror))g.setColor(pink)  //we use a distinct color for crossed edge
        else g.setColor(orange)
        g.drawLine(e.src.x.toInt,e.src.y.toInt,e.target.x.toInt,e.target.y.toInt)
      }
    }


    def drawPoints() = {

      for (p <- env.medium.displayedPoint) {
        val v2=env.medium.theVoronois(Coord2D(p.x,p.y))
        if(v2.trianglesOK) {
          g.setColor(gray)
          g.drawPoint(p.x.toInt, p.y.toInt,2)
        }
        else  {
          g.setColor(white)
          g.drawPoint(p.x.toInt, p.y.toInt,4)
        }

      }
    }
    def drawCAcolorVoronoi() = {
      //env.computeVoronoirColors() //painting allways need to recompute the colors, it would seem
      //for (v: Voroonoi <- env.medium.voronoi.values) {
        for(p<-env.medium.displayedPoint){
          val v2=env.medium.theVoronois(Coord2D(p.x,p.y))
        if (v2.polygon.npoints==0){ //we could not build the voronoi, we just draw a point.
          g.setColor(v2.color)
          g.drawPoint(p.x.toInt, p.y.toInt,10)
          g.drawPoint(p.x.toInt, p.y.toInt,1)} //on veut que le stroke revient a 1.
        else if
          (v2.color != Color.black || v2.corner.isDefined //we print the corners even it they are black, because they can overlap
        ) {
          g.setColor(v2.color)
          g.fillPolygon(v2.polygon)
        }
        }
    }

    //drawCAtestInit(env.medium.defInit(E()),red)
    drawCAcolorVoronoi()
   // drawCAinsideContour(gray)
   // drawCA1DborderContour(white)

    //

//     drawTriangles(blue,env.medium.triangleSoupDelaunay)
   // drawTriangles(green,env.medium.triangleSoupGraph)
   // drawEdges(red)
    drawPoints()
    drawText(white)


    //drawdebug(green)
     if(env.controller.showMore)
        {drawCrossedFaces();drawFaces()}
   // drawTriangles(blue,env.medium.triangleSoupDelaunay)
  //   drawTrianglesVEv(blue,env.medium.triangleSoupDelaunay)
    // drawOutsideFace() plante si y ajuste V()
  }

}




