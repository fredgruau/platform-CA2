/*
package triangulation;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.Frame;
import java.awt.Point;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.awt.geom.Line2D;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.PrintWriter;
import java.nio.ByteBuffer;
import java.nio.FloatBuffer;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.StringTokenizer;
import java.util.TreeSet;

import com.jogamp.nativewindow.util.Rectangle;
import com.jogamp.opengl.GL;
import com.jogamp.opengl.GL2;
import com.jogamp.opengl.GL2ES1;
import com.jogamp.opengl.GLAutoDrawable;
import com.jogamp.opengl.GLCapabilities;
import com.jogamp.opengl.GLEventListener;
import com.jogamp.opengl.GLProfile;
import com.jogamp.opengl.awt.GLCanvas;
import com.jogamp.opengl.fixedfunc.GLMatrixFunc;
import com.jogamp.opengl.util.FPSAnimator;
 
import triangulation.DelaunayTriangulator;
import triangulation.NotEnoughPointsException;
import triangulation.Triangle2D;
import triangulation.Vector2D;

*/
/**
 * Simple implementation of an incremental 2D Delaunay triangulation algorithm
 * written in Java.
 *
 * @author Johannes Diemke
 * Pour comparer deux points, on utilise leur noms si les coordonnées sont différentes.
 *//*

public class DelaunayTriangulationExample implements GLEventListener, MouseListener {

    public static final Dimension DIMENSION = Vector2D.DIMENSION;
    public static final int SIDE=60;
    public static final double DENSITY= 0.3;

  //  private static final Color COLOR_TRIANGLE_FILL = new Color(26, 121, 121);
    private static final Color COLOR_TRIANGLE_FILL = new Color(255,255,255);
    private static final Color COLOR_TRIANGLE_EDGES = new Color(5, 234, 234);
    private static final Color COLOR_LATTICE_EDGES = new Color(234, 5, 234);
    private static final Color COLOR_TRIANGLE_BORDER = new Color(241, 241, 121);
    private static final Color COLOR_BACKGROUND = new Color(47, 47, 47);

    DelaunayTriangulator delaunayTriangulator;
    List<Vector2D> pointSet = new ArrayList<>();
    List<Vector2D> pointSetSave = new ArrayList<>();
    List<Triangle2D> triangles;
    List<Vector2D> center = new ArrayList<>(); 
    TreeSet<Vector2D>  midleEdge = new TreeSet<Vector2D>(new    TheComparator()); 
            
    List<Vector2D> barycenterFace  = new ArrayList<>();
    List<Vector2D> centerTriangle  = new ArrayList<>();
    Vector2D [][] lattice = new Vector2D[(int)DIMENSION.width/SIDE][(int)DIMENSION.height/SIDE];
    private Vector2D middle(Vector2D p1, Vector2D p2) {
    	return new Vector2D(moyenne(p1.x,p2.x),moyenne(p1.y,p2.y));
    }
    public double moyenne(double x, double y) {
    	if (x>y) return (y+x)/2; else return (x+y)/2;  } //ainsi pas d'erreur d'arrondis dependant de l'ordre
                        //Car en double, x=y n'est pas egal a y+x
    
    public boolean near (double x, double y) {return x==y;}// Math.abs(x-y)<=0.000000001;}
class TheComparator implements java.util.Comparator<Vector2D> {
	

*/
/**Pour comparer deux points, on utilise leur noms si les coordonnées sont différentes. *//*

	public int compare(Vector2D u, Vector2D v) {
		if (near(u.x,v.x) && near(u.y, v.y)) return 0; 
	    else return u.toString().compareTo(v.toString()); 
	}
}
      
    public void middleOfEdge() {
    	for (Triangle2D t: delaunayTriangulator.getTriangles()) {
    		midleEdge.add(middle(t.a,t.b));  
            midleEdge.add(middle(t.c,t.b));         
            midleEdge.add(middle(t.a,t.c));
        }
    	System.out.println("nombre de middle edge"+ midleEdge.size() );
    }
     
    public void initPointHex(double rayon,int height,int width,Vector2D corner) {
    	Vector2D col1=new Vector2D(corner.x, corner.y);
    	  double deltax= rayon*Math.cos(1/12.0 *2*Math.PI);
    	    double deltay=rayon*3/2.0;int pair =1;
    	    for(int j=-2;  j<width*1.2; j =j+1, col1.y +=deltay,col1.x+=deltax*pair,pair=-pair ) {
    	    	Vector2D p=new Vector2D(col1.x,col1.y);
    	    	for(int i=-2;i<height*1.2;i++,p.x+=2*deltax) 
    	    		  pointSet.add(new Vector2D(p.x ,p.y ));
    	    }
    }





    public void barycenterOfFace() {
    	for (Triangle2D t: delaunayTriangulator.getTriangles()) 
    		 barycenterFace.add(t.barycenter()); 
}
    public void centerOfTriangle() {
    	for (Triangle2D t: delaunayTriangulator.getTriangles())
    	{Vector2D p=t.computeCenter();
    	if (p!=null)  centerTriangle.add(p); 
    	}
}
    
    public static void main(String[] args) {
        Frame frame = new Frame("Delaunay Triangulation Example");
        frame.setResizable(false);
       //  GLCapabilities caps = new GLCapabilities(GLProfile.getMinimum(true));
       GLCapabilities caps = new GLCapabilities(GLProfile.get("GL2"));
        caps.setSampleBuffers(true);
        caps.setNumSamples(8);

        GLCanvas canvas = new GLCanvas(caps);

        DelaunayTriangulationExample ex = new DelaunayTriangulationExample();
        MouseListener lister = ex;
        canvas.addGLEventListener(ex);
        canvas.setPreferredSize(DIMENSION);
        canvas.addMouseListener(lister);

        frame.add(canvas);

        final FPSAnimator animator = new FPSAnimator(canvas, 25);

        frame.addWindowListener(new WindowAdapter() {
            public void windowClosing(WindowEvent e) {
                new Thread(new Runnable() {
                    public void run() {
                        animator.stop();
                        System.exit(0);
                    }
                }).start();
            }
        });

        frame.setVisible(true);
        frame.pack();
        animator.start();
    }
    
    String output;
    public void init(GLAutoDrawable drawable) {
    	 
    	 GL gl = drawable.getGL();

        //GL2 gl = drawable.getGL().getGL2();
        
        gl.glDisable(GL.GL_CULL_FACE);
       // gl.glShadeModel(GL2.GL_SMOOTH);
        gl.glClearColor(COLOR_BACKGROUND.getRed() / 255.0f, COLOR_BACKGROUND.getGreen() / 255.0f,
                COLOR_BACKGROUND.getBlue() / 255.0f, 1);
        gl.glClearDepth(1.0f);
        gl.glEnable(GL.GL_DEPTH_TEST);
        gl.glDepthFunc(GL.GL_LEQUAL);
        gl.glHint(GL2.GL_PERSPECTIVE_CORRECTION_HINT, GL.GL_NICEST);

        gl.setSwapInterval(1);
        gl.glDisable(GL2.GL_CULL_FACE);
       initPointFpo(110, 3.4);
       // initPointHex ( SIDE/1.02,  (int)(DIMENSION.width/(SIDE)) ,       (int)(DIMENSION.height/(1.2*SIDE)) ,new Vector2D(-SIDE*1,-SIDE*1));
      //initPointSetPoisson();
        delaunayTriangulator = new DelaunayTriangulator(pointSet);
        pointSetSave.addAll(pointSet);
        try { delaunayTriangulator.triangulate();
        	   triangles= delaunayTriangulator.getTriangles();
        	     middleOfEdge(); pointSet.addAll(new ArrayList<Vector2D>(midleEdge ));  
               //centerOfTriangle(); pointSet.addAll(centerTriangle);
               barycenterOfFace(); pointSet.addAll(barycenterFace);
                  delaunayTriangulator = new DelaunayTriangulator(pointSet); 
              delaunayTriangulator.triangulate();
        } catch (NotEnoughPointsException e1) {
         
        }
    }

    public void reshape(GLAutoDrawable drawable, int x, int y, int width, int height) {
        
    	//GL gl = drawable.getGL()	;
    	GL2 gl = drawable.getGL().getGL2();
      ((GLMatrixFunc) gl).glMatrixMode(GL2.GL_PROJECTION);
        ((GLMatrixFunc) gl).glLoadIdentity();
        ((GL2ES1) gl).glOrtho(0, DIMENSION.getWidth(), DIMENSION.getHeight(), 0, 1.0, -1.0);
        ((GLMatrixFunc) gl).glMatrixMode(GL2.GL_MODELVIEW);
        ((GLMatrixFunc) gl).glLoadIdentity();
    }
    private void displayFond( List<Triangle2D> l,GL2 gl,Color co) {
        gl.glColor3ub((byte) co.getRed(), (byte) co.getGreen(), (byte) co.getBlue());
        gl.glBegin(GL.GL_TRIANGLES);
        for(Triangle2D triangle:l) if(triangle.allNeighbor()) {
        	Vector2D a = triangle.a;
        	Vector2D b = triangle.b;
        	Vector2D c = triangle.c;
        	gl.glVertex2d(a.x, a.y);
        	gl.glVertex2d(b.x, b.y);
        	gl.glVertex2d(c.x, c.y);}
        gl.glEnd();
    }
    
    private void hexagon(GL2 gl,Vector2D center,double rayon) { 
    	Vector2D V[]=new Vector2D[6];
    	   for(int i = 0; i < 6; ++i)  
    	        V[i]=new Vector2D(rayon*Math.sin(i/6.0*2*Math.PI)+center.x,
    	        		          rayon*Math.cos(i/6.0*2*Math.PI)+center.y);
    	   for(int i = 0; i < 6; ++i) 
    	   {   gl.glVertex2d(V[i].x, V[i].y);
               gl.glVertex2d(V[(i+1)%6].x, V[(i+1)%6].y);
    	   }
    }
    private void hexLattice(GL2 gl,Color c,double rayon, Vector2D corner, int width,int height){
    gl.glColor3ub((byte) c.getRed(), (byte)c.getGreen(), (byte) c.getBlue());
    gl.glBegin(GL.GL_LINES);  Vector2D col1=new Vector2D(corner.x, corner.y); 
    double deltax= rayon*Math.cos(1/12.0 *2*Math.PI);
    double deltay=rayon*3/2.0;int pair =1;
    for(int j=0;  j<width; j =j+1, col1.y +=deltay,col1.x+=deltax*pair,pair=-pair ) {
    	Vector2D p=new Vector2D(col1.x,col1.y);
    	for(int i=0;i<height;i++,p.x+=2*deltax) 
    		hexagon(gl, p,rayon); 
    }
    gl.glEnd();
}  

private void displayPointList(GL2 gl,Color c, List<Vector2D> l) { 
    	gl.glPointSize(7.5f);    gl.glColor3f(0.2f, 1.2f, 0.25f);
        gl.glColor3ub((byte) c.getRed(),(byte)c.getGreen(),(byte)c.getBlue());
        gl.glBegin(GL.GL_POINTS); output+="<g>\n";
        for ( Vector2D p: l) if(p.inside()) {   gl.glVertex2d(p.x, p.y); 
     	String circle="<circle cx=\"$cx\" cy=\"$cy\" r=\"3\" fill=\"blue\"/>\n";
     	circle=circle.replace("$cx",""+p.x);
      	circle=circle.replace("$cy",""+p.y); 
         output=output+ circle;    
        }
        gl.glEnd();output+="</g>\n";
    }  
    
    public void displayTriangle(GL2 gl,Color co, List<Triangle2D> t ) {
   	 gl.glColor3ub((byte)co.getRed(), (byte)co.getGreen(),(byte)co.getBlue());
         gl.glLineWidth(1.0f);  gl.glBegin(GL.GL_LINES);
        for (Triangle2D triangle : t) {
            Vector2D a = triangle.a,     b = triangle.b, c = triangle.c ;
            drawLine(gl,a,b);  drawLine(gl,a,c);    drawLine(gl,c,b);
             // gl.glVertex2d(a.x, a.y); gl.glVertex2d(b.x, b.y);  gl.glVertex2d(b.x, b.y);   gl.glVertex2d(c.x, c.y); gl.glVertex2d(c.x, c.y);  gl.glVertex2d(a.x, a.y);
        }
        gl.glEnd(); 
   }
    private void displayNeighbor(GL2 gl, Vector2D p, Triangle2D t ) {
    	if (t!=null) if(t.center!=null) { Vector2D p1=p.clone();Vector2D p2=t.center.clone();
    		drawLine(gl,p1,p2);
    	}   
    }
    void drawLine(GL2 gl,Vector2D p1,Vector2D p2) {
    	Vector2D q1=p1.clone(),q2=p2.clone();
    	if(Vector2D.tronque(q1,q2)) {
    	 gl.glVertex2d(q1.x, q1.y);gl.glVertex2d(q2.x, q2.y);
	String line="<line x1=\"$x1\" y1=\"$y1\" x2=\"$x2\" y2=\"$y2\" stroke=\"black\" />\n";
  	line=line.replace("$x1",""+q1.x).replace("$y1",""+q1.y).replace("$x2",""+q2.x).replace("$y2",""+q2.y);
     output=output+ line; }}


    private void voronoiEdge(GL2 gl,Color c) { 
    	 delaunayTriangulator.computeNeighbor();
         gl.glColor3ub((byte)c.getRed(), (byte) c.getGreen(),  (byte) c.getBlue());
          gl.glLineWidth(1.0f);
          gl.glBegin(GL.GL_LINES);    output+="<g>\n";
        for ( Triangle2D triangle: delaunayTriangulator.getTriangles())
            if(triangle.center!=null) {
            displayNeighbor(  gl,    triangle.center, triangle.ta);
            displayNeighbor(  gl,  triangle.center,triangle.tb);
            displayNeighbor(  gl,  triangle.center,triangle.tc); 
        }
        gl.glEnd();    output+="</g>\n";
        
    	 
   }
     
 
    public void display(GLAutoDrawable drawable) {
    	output="<?xml version=\"1.0\" encoding=\"utf-8\"?>\n"  + "<svg  width=\"$width\" height=\"$height\">\n"     	  ;
       	output=output.replace("$width",""+DIMENSION.width); output=output.replace("$height",""+DIMENSION.height);
 	    String chip="<rect width=\"$width\" height=\"$height\" x=\"0\" y=\"0\" stroke=\"black\"   stroke-width=\"2\" style=\"opacity:1;fill:none\" />";
     	chip=chip.replace("$width",""+DIMENSION.width);  	chip=chip.replace("$height",""+DIMENSION.height);
     	output+=chip;
        GL gl = drawable.getGL()   ;  
       // GL2 gl = drawable.getGL().getGL2();
        gl.glClear(GL.GL_COLOR_BUFFER_BIT | GL.GL_DEPTH_BUFFER_BIT);
        ((GLMatrixFunc) gl).glLoadIdentity();     gl.glTranslatef(0.0f, 0.0f, 0.0f);
		//displayFond(delaunayTriangulator.getTriangles(),gl,COLOR_TRIANGLE_FILL);
       //hexLattice(gl ,COLOR_LATTICE_EDGES, SIDE*1.3 ,new Vector2D(30,30), 
        //		 (int) (DIMENSION.height/(1.2*SIDE)) , (int)(DIMENSION.width/(1.2*SIDE)));
         // displayPointList(gl,COLOR_TRIANGLE_BORDER,new ArrayList<Vector2D>(midleEdge ));
        centerOfTriangle();
         // displayPointList(gl,COLOR_LATTICE_EDGES,centerTriangle);
        displayPointList(gl,COLOR_TRIANGLE_BORDER,pointSet); //afffiche les points originaux
      //  voronoiEdge(gl,COLOR_LATTICE_EDGES);
          displayTriangle(gl,COLOR_TRIANGLE_EDGES,triangles);
       output=output   + "</svg>\n"; 	storeFile(output,"src/voronoi.svg");
   }
  

    public void displayChanged(GLAutoDrawable drawable, boolean modeChanged, boolean deviceChanged) {
    }

    @Override
    public void dispose(GLAutoDrawable drawable) {
    }

    @Override
    public void mouseClicked(MouseEvent e) {
    }

    boolean tooNear(Vector2D p1, Vector2D p2) {
    	return (p1.x-p2.x)*(p1.x-p2.x)+(p1.y-p2.y)*(p1.y-p2.y)<2*SIDE*SIDE;
    }
    
    boolean noPointNear(Vector2D p) {
    	int pi= (int)(p.x/SIDE);int pj= (int)(p.y/SIDE);
    	for(int i=pi-2;i<=pi+2;i++)
        	for(int j=pj-2;j<=pj+2;j++)
        		if(i>=0 && i< lattice.length &&j>=0 && j< lattice[0].length  )
    		       if(lattice[i][j]!=null)
    		    	    if(tooNear(p,lattice[i][j]))
    		    	    	return false;
    	lattice[pi][pj]=p;
    	return true;
    }
    public Vector2D randPoint() {
    	return new Vector2D(Math.random()*DIMENSION.getWidth(),Math.random()*DIMENSION.getHeight());
    }
    

    public void initPointFpo(double marge, double space) {
    	Vector2D p; 
		try{
		InputStream flux=new FileInputStream("src/fpo.txt"); 
		InputStreamReader lecture=new InputStreamReader(flux);
		BufferedReader buff=new BufferedReader(lecture);
		String ligne;
		while ((ligne=buff.readLine())!=null){
		  	StringTokenizer st = new StringTokenizer(ligne);
			System.out.println("Nombre de mots:" + st.countTokens());
			p=new Vector2D( Double.parseDouble(st.nextToken())*DIMENSION.width*space-marge,Double.parseDouble(st.nextToken())* DIMENSION.width*space-marge);
		 	if(p.inside(marge))pointSet.add(p);
			//pour dupliquer la distribution p=new Vector2D(  p.x+DIMENSION.width/2, p.y);	//rectangle(p,x,X,y,Y);
		}
		buff.close(); 
		}		
		catch (Exception e){
		System.out.println(e.toString());
		}

}
    
    
    
    public static void storeFile(String source, String fileName) {
   
         final File fichier =new File(fileName); 
           try {fichier .createNewFile(); final FileWriter writer = new FileWriter(fichier);
               try { writer.write(source); } finally {writer.close();           }
             } catch (Exception e) {
               System.out.println("Impossible de creer le fichier");
           }
       }
	 
   
    public void initPointSetPoisson() {
    	Vector2D p;
        for(int i=0; i<DENSITY*lattice.length*lattice[0].length;i++) {
        	do {p=randPoint();} while (  ! noPointNear(p) );
            pointSet.add(p);
           
        }
    }
    
    public void initPointSetLattice() {
        for(int i=0; i<10;i++)
            for(int j=0; j<10;j++)
            	pointSet.add(new Vector2D(i*100,j*100));
       
    }
    @Override
    public void mousePressed(MouseEvent e) {
        Point p = e.getPoint();
        pointSet.add(new Vector2D(p.x, p.y));
        ByteBuffer RGB = ByteBuffer.allocateDirect(3); //create a new byte buffer (r, g, b)
        try {
            delaunayTriangulator.triangulate();
        } catch (NotEnoughPointsException e1) {
        }
    }
    @Override
    public void mouseReleased(MouseEvent e) {
    }

    @Override
    public void mouseEntered(MouseEvent e) {
    }

    @Override
    public void mouseExited(MouseEvent e) {
    }

}
*/
