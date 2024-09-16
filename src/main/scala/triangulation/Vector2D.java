package triangulation;

import java.awt.Dimension;

/**
 * 2D vector class implementation.
 *
 * @author Johannes Diemke
 */

public class Vector2D implements Cloneable {
    public static final Dimension DIMENSION = new Dimension(800, 600);

    public double x;
    public double y;

    /**
     * Constructor of the 2D vector class used to create new vector instances.
     *
     * @param x The x coordinate of the new vector
     * @param y The y coordinate of the new vector
     */
    public Vector2D(double x, double y) {
        this.x = x;
        this.y = y;
    }

    public Vector2D(int x, int y) {
        this.x = x;
        this.y = y;
    }

    public boolean isEqual(Vector2D v) {return x == v.x && y == v.y;
    }
    public boolean isEqual2(Vector2D v) {return almostEqualS(x,v.x) && almostEqualS(y,v.y);
    }
    public static boolean almostEqualS(double x, double y){return(Math.abs(x-y)  < 0.000001);}
    public double distance(Vector2D other){ return (sub(other).mag());}
    public boolean almostEqual(Vector2D v) {
        return (sub(v).mag() < 0.000001);
    }

    /**
     * Subtracts the given vector from this.
     *
     * @param vector The vector to be subtracted from this
     * @return A new instance holding the result of the vector subtraction
     */
    public Vector2D sub(Vector2D vector) {
        return new Vector2D(this.x - vector.x, this.y - vector.y);
    }

    /**
     * Adds the given vector to this.
     *
     * @param vector The vector to be added to this
     * @return A new instance holding the result of the vector addition
     */
    public Vector2D add(Vector2D vector) {
        return new Vector2D(this.x + vector.x, this.y + vector.y);
    }

    public Vector2D barycenter(Vector2D v,double coeff) {
        Vector2D res=mult(coeff).add(v.mult(1-coeff));
        return (res);
    }

    public Vector2D middle(Vector2D v) {
        return (add(v).mult(0.5));
    }

    public Vector2D rotpisur2() {
        return (new Vector2D(-1 * y, x));
    }

    /**
     * Multiplies this by the given scalar.
     *
     * @param scalar The scalar to be multiplied by this
     * @return A new instance holding the result of the multiplication
     */
    public Vector2D mult(double scalar) {
        return new Vector2D(this.x * scalar, this.y * scalar);
    }

    /**
     * Computes the magnitude or length of this.
     *
     * @return The magnitude of this
     */
    public double mag() {
        return Math.sqrt(this.x * this.x + this.y * this.y);
    }

    /**
     * Computes the dot product of this and the given vector.
     *
     * @param vector The vector to be multiplied by this
     * @return A new instance holding the result of the multiplication
     */
    public double dot(Vector2D vector) {
        return this.x * vector.x + this.y * vector.y;
    }

    /**
     * Computes the 2D pseudo cross product Dot(Perp(this), vector) of this and
     * the given vector.
     *
     * @param vector The vector to be multiplied to the perpendicular vector of
     *               this
     * @return A new instance holding the result of the pseudo cross product
     */
    public double cross(Vector2D vector) {
        return this.y * vector.x - this.x * vector.y;
    }

    @Override
    public String toString() {
        return "Vector2D[" + x + ", " + y + "]";
    }


    public Vector2D clone() {
        return new Vector2D(x, y);
    }

    /**
     * Renvoie vrai si y a qqc a afficher et modifie p1 et p2 s'il y a lieu
     * pour n'afficher que le segment visible
     */

    public static boolean inside(double xmin, double xmax, double x) {
        return x >= xmin && x <= xmax;
    }

    public boolean inside() {
        return inside(0, DIMENSION.width, x) && inside(0, DIMENSION.height, y);
    }

    public boolean inside(double marge) {
        return inside(-marge, DIMENSION.width + marge, x) && inside(-marge, DIMENSION.height + marge, y);
    }

    static Vector2D c1 = new Vector2D(0.0, 0.0), c2 = new Vector2D(DIMENSION.width, 0.0),
            c3 = new Vector2D(DIMENSION.width, DIMENSION.height), c4 = new Vector2D(0.0, DIMENSION.height);
    static Line square[] = {new Line(c1, c2), new Line(c2, c3), new Line(c3, c4), new Line(c4, c1)};

    public static boolean tronque(Vector2D p1, Vector2D p2) {
        boolean i1 = p1.inside(), i2 = p2.inside();
        if (!i1 && !i2) return false;
        if (i1 && i2) return true;
        if (!i1) {
            Vector2D tmp = p1;
            p1 = p2;
            p2 = tmp;
        }
        Line segment = new Line(p1, p2);
        //p1 est dedans la fenetre, remplacer p2 par l'intersection de p1,p2, et l'un des quatres cotés.
        for (Line l : square)
            if (intersect(segment, l)) {
                Vector2D p = intersection(segment, l);
                p2.x = p.x;
                p2.y = p.y;
                return true;
            }
        return false;
    }

    public double sinus(Vector2D v) {
        return (x * v.y - y * v.x);
    }


    public static boolean onSegment(Vector2D p, Vector2D q, Vector2D r) {
        if (q.x <= Math.max(p.x, r.x) && q.x >= Math.min(p.x, r.x) &&
                q.y <= Math.max(p.y, r.y) && q.y >= Math.min(p.y, r.y))
            return true;
        return false;
    }


// To find orientation of ordered triplet (p, q, r). 
// The function returns following values 
// 0 --> p, q and r are colinear 
// 1 --> Clockwise 
// 2 --> Counterclockwise 


    public static int orientation(Vector2D p, Vector2D q, Vector2D r) {
        // See https://www.geeksforgeeks.org/orientation-3-ordered-Vector2Ds/
        // for details of below formula.
        double val = (q.y - p.y) * (r.x - q.x) -
                (q.x - p.x) * (r.y - q.y);

        if (Math.abs(val) < 0.001) return 0;  // colinear

        return (val > 0) ? 1 : 2; // clock or counterclock wise
    }


    public static boolean intersect(Line l1, Line l2) {
        return intersect(l1.s, l1.e, l2.s, l2.e);
    }

// The main function that returns true if line segment 'p1q1' 
// and 'p2q2' intersect. 

    public static boolean intersect(Vector2D p1, Vector2D q1, Vector2D p2, Vector2D q2) {
        // Find the four orientations needed for general and
        // special cases
        int o1 = orientation(p1, q1, p2);
        int o2 = orientation(p1, q1, q2);
        int o3 = orientation(p2, q2, p1);
        int o4 = orientation(p2, q2, q1);

        // General case
        if (o1 != o2 && o3 != o4)
            return true;

        // Special Cases
        // p1, q1 and p2 are colinear and p2 lies on segment p1q1
        if (o1 == 0 && onSegment(p1, p2, q1)) return true;

        // p1, q1 and q2 are colinear and q2 lies on segment p1q1
        if (o2 == 0 && onSegment(p1, q2, q1)) return true;

        // p2, q2 and p1 are colinear and p1 lies on segment p2q2
        if (o3 == 0 && onSegment(p2, p1, q2)) return true;

        // p2, q2 and q1 are colinear and q1 lies on segment p2q2
        if (o4 == 0 && onSegment(p2, q1, q2)) return true;

        return false; // Doesn't fall in any of the above cases
    }


    private static class Line {
        Vector2D s, e;

        Line(Vector2D s, Vector2D e) {
            this.s = s;
            this.e = e;
        }
    }

   public static Vector2D intersection(Line l1, Line l2) {
        double a1 = l1.e.y - l1.s.y, b1 = l1.s.x - l1.e.x, c1 = a1 * l1.s.x + b1 * l1.s.y;
        double a2 = l2.e.y - l2.s.y, b2 = l2.s.x - l2.e.x, c2 = a2 * l2.s.x + b2 * l2.s.y;
        double delta = a1 * b2 - a2 * b1;
        return new Vector2D((b2 * c1 - b1 * c2) / delta, (a1 * c2 - a2 * c1) / delta);
    }

}