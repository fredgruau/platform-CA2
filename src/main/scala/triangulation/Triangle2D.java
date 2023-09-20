package triangulation;

import java.util.Arrays;

/**
 * 2D triangle class implementation.
 *
 * @author Johannes Diemke
 */
public class Triangle2D {

    public Vector2D a;
    public Vector2D b;
    public Vector2D c;

    public Vector2D center = null;
    public Triangle2D ta;
    public Triangle2D tb;
    public Triangle2D tc;

    /**
     * Constructor of the 2D triangle class used to create a new triangle
     * instance from three 2D vectors describing the triangle's vertices.
     *
     * @param a The first vertex of the triangle
     * @param b The second vertex of the triangle
     * @param c The third vertex of the triangle
     */
    public Triangle2D(Vector2D a, Vector2D b, Vector2D c) {
        this.a = a;
        this.b = b;
        this.c = c;
    }

    public Vector2D barycenter() {
        return new Vector2D((a.x + b.x + c.x) / 3, (a.y + b.y + c.y) / 3);
    }

    /**
     * Tests if a 2D point lies inside this 2D triangle. See Real-Time Collision
     * Detection, chap. 5, p. 206.
     *
     * @param point The point to be tested
     * @return Returns true iff the point lies inside this 2D triangle
     */
    public boolean contains(Vector2D point) {
        double pab = point.sub(a).cross(b.sub(a));
        double pbc = point.sub(b).cross(c.sub(b));

        if (!hasSameSign(pab, pbc)) {
            return false;
        }

        double pca = point.sub(c).cross(a.sub(c));

        if (!hasSameSign(pab, pca)) {
            return false;
        }

        return true;
    }

    /**
     * Tests if a given point lies in the circumcircle of this triangle. Let the
     * triangle ABC appear in counterclockwise (CCW) order. Then when det &gt;
     * 0, the point lies inside the circumcircle through the three points a, b
     * and c. If instead det &lt; 0, the point lies outside the circumcircle.
     * When det = 0, the four points are cocircular. If the triangle is oriented
     * clockwise (CW) the result is reversed. See Real-Time Collision Detection,
     * chap. 3, p. 34.
     *
     * @param point The point to be tested
     * @return Returns true iff the point lies inside the circumcircle through
     * the three points a, b, and c of the triangle
     */
    public boolean isPointInCircumcircle(Vector2D point) {
        double a11 = a.x - point.x;
        double a21 = b.x - point.x;
        double a31 = c.x - point.x;

        double a12 = a.y - point.y;
        double a22 = b.y - point.y;
        double a32 = c.y - point.y;

        double a13 = (a.x - point.x) * (a.x - point.x) + (a.y - point.y) * (a.y - point.y);
        double a23 = (b.x - point.x) * (b.x - point.x) + (b.y - point.y) * (b.y - point.y);
        double a33 = (c.x - point.x) * (c.x - point.x) + (c.y - point.y) * (c.y - point.y);

        double det = a11 * a22 * a33 + a12 * a23 * a31 + a13 * a21 * a32 - a13 * a22 * a31 - a12 * a21 * a33
                - a11 * a23 * a32;

        if (isOrientedCCW()) {
            return det > 0.0d;
        }

        return det < 0.0d;
    }

    /**
     * Test if this triangle is oriented counterclockwise (CCW). Let A, B and C
     * be three 2D points. If det &gt; 0, C lies to the left of the directed
     * line AB. Equivalently the triangle ABC is oriented counterclockwise. When
     * det &lt; 0, C lies to the right of the directed line AB, and the triangle
     * ABC is oriented clockwise. When det = 0, the three points are colinear.
     * See Real-Time Collision Detection, chap. 3, p. 32
     *
     * @return Returns true iff the triangle ABC is oriented counterclockwise
     * (CCW)
     */
    public boolean isOrientedCCW() {
        double a11 = a.x - c.x;
        double a21 = b.x - c.x;

        double a12 = a.y - c.y;
        double a22 = b.y - c.y;

        double det = a11 * a22 - a12 * a21;

        return det > 0.0d;
    }

    /**
     * orient the trianble in CCW
     */
    public void orientCCW() {
        if (!isOrientedCCW()) {
            Vector2D tmp = a;
            a = b;
            b = tmp;
        }

    }


    /**
     * Returns true if this triangle contains the given edge.
     *
     * @param edge The edge to be tested
     * @return Returns true if this triangle contains the edge
     */
    public boolean isNeighbour(Edge2D edge) {
        return (a == edge.a || b == edge.a || c == edge.a) && (a == edge.b || b == edge.b || c == edge.b);
    }

    public boolean isSummit(Vector2D p) {
        return a == p || b == p || c == p;
    }

    public boolean isNeighbour(Triangle2D t) {
        boolean hasa = t.isSummit(a);
        boolean hasb = t.isSummit(b);
        boolean hasc = t.isSummit(c);
        return ((hasa && hasb) || (hasa && hasc) || (hasc && hasb));
    }

    public void permute() {
        Vector2D tmp = a;
        a = b;
        b = c;
        c = tmp;
    }

    /**
     * @param t potential neighbors.
     *          t is a neighbor if it has two summits in common, in which case we will link it to the third summit
     */
    public void computeNeighbour(Triangle2D t) {
        if (t != this) {
            boolean na = t.isSummit(a), nb = t.isSummit(b), nc = t.isSummit(c);
            if (na && nb) tc = t;
            if (na && nc) tb = t;
            if (nc && nb) ta = t;
        }
    }

    /**
     * Returns the vertex of this triangle that is not part of the given edge.
     *
     * @param edge The edge
     * @return The vertex of this triangle that is not part of the edge
     */
    public Vector2D getNoneEdgeVertex(Edge2D edge) {
        if (a != edge.a && a != edge.b) {
            return a;
        } else if (b != edge.a && b != edge.b) {
            return b;
        } else if (c != edge.a && c != edge.b) {
            return c;
        }

        return null;
    }

    /**
     * Returns true if the given vertex is one of the vertices describing this
     * triangle.
     *
     * @param vertex The vertex to be tested
     * @return Returns true if the Vertex is one of the vertices describing this
     * triangle
     */
    public boolean hasVertex(Vector2D vertex) {
        if (a == vertex || b == vertex || c == vertex) {
            return true;
        }

        return false;
    }

    /**
     * Returns an EdgeDistancePack containing the edge and its distance nearest
     * to the specified point.
     *
     * @param point The point the nearest edge is queried for
     * @return The edge of this triangle that is nearest to the specified point
     */
    public EdgeDistancePack findNearestEdge(Vector2D point) {
        EdgeDistancePack[] edges = new EdgeDistancePack[3];

        edges[0] = new EdgeDistancePack(new Edge2D(a, b),
                computeClosestPoint(new Edge2D(a, b), point).sub(point).mag());
        edges[1] = new EdgeDistancePack(new Edge2D(b, c),
                computeClosestPoint(new Edge2D(b, c), point).sub(point).mag());
        edges[2] = new EdgeDistancePack(new Edge2D(c, a),
                computeClosestPoint(new Edge2D(c, a), point).sub(point).mag());

        Arrays.sort(edges);
        return edges[0];
    }

    /**
     * Computes the closest point on the given edge to the specified point.
     *
     * @param edge  The edge on which we search the closest point to the specified
     *              point
     * @param point The point to which we search the closest point on the edge
     * @return The closest point on the given edge to the specified point
     */
    private Vector2D computeClosestPoint(Edge2D edge, Vector2D point) {
        Vector2D ab = edge.b.sub(edge.a);
        double t = point.sub(edge.a).dot(ab) / ab.dot(ab);

        if (t < 0.0d) {
            t = 0.0d;
        } else if (t > 1.0d) {
            t = 1.0d;
        }

        return edge.a.add(ab.mult(t));
    }

    /**
     * Tests if the two arguments have the same sign.
     *
     * @param a The first floating point argument
     * @param b The second floating point argument
     * @return Returns true iff both arguments have the same sign
     */
    private boolean hasSameSign(double a, double b) {
        return Math.signum(a) == Math.signum(b);
    }

    @Override
    public String toString() {
        return "Triangle2D[" + a + ", " + b + ", " + c + "]";
    }


    static final double TOL = 0.0000001;

    /**
     * retourne le centre du cercle dans lequel le triangle est inscrit
     **/
    public static Vector2D centerFromPoints(final Vector2D p1, final Vector2D p2, final Vector2D p3) {
        final double offset = Math.pow(p2.x, 2) + Math.pow(p2.y, 2);
        final double bc = (Math.pow(p1.x, 2) + Math.pow(p1.y, 2) - offset) / 2.0;
        final double cd = (offset - Math.pow(p3.x, 2) - Math.pow(p3.y, 2)) / 2.0;
        final double det = (p1.x - p2.x) * (p2.y - p3.y) - (p2.x - p3.x) * (p1.y - p2.y);

        if (Math.abs(det) < TOL) {
            return null;
        }// throw new IllegalArgumentException("Yeah, lazy."); }

        final double idet = 1 / det;

        final double centerx = (bc * (p2.y - p3.y) - cd * (p1.y - p2.y)) * idet;
        final double centery = (cd * (p1.x - p2.x) - bc * (p2.x - p3.x)) * idet;
        // final double radius =        Math.sqrt( Math.pow(p2.x - centerx,2) + Math.pow(p2.y-centery,2));

        return new Vector2D(centerx, centery);
    }

    /**
     * retourne le centre du cercle dans lequel le triangle est inscrit
     **/
    public Vector2D computeCenter() {
        center = centerFromPoints(a, b, c);
        return center;
    }

    public static double matrixDeterminant(double[][] matrix) {
        double temporary[][];
        double result = 0;

        if (matrix.length == 1) {
            result = matrix[0][0];
            return (result);
        }

        if (matrix.length == 2) {
            result = ((matrix[0][0] * matrix[1][1]) - (matrix[0][1] * matrix[1][0]));
            return (result);
        }

        for (int i = 0; i < matrix[0].length; i++) {
            temporary = new double[matrix.length - 1][matrix[0].length - 1];

            for (int j = 1; j < matrix.length; j++) {
                for (int k = 0; k < matrix[0].length; k++) {
                    if (k < i) {
                        temporary[j - 1][k] = matrix[j][k];
                    } else if (k > i) {
                        temporary[j - 1][k - 1] = matrix[j][k];
                    }
                }
            }

            result += matrix[0][i] * Math.pow(-1, (double) i) * matrixDeterminant(temporary);
        }
        return (result);
    }

    public boolean allNeighbor() {
        return ta != null && tb != null && tc != null;
    }


}