package simulator;

import compiler.Locus;

import javax.swing.*;
import java.awt.*;
import java.awt.Color;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.FontMetrics;
import java.awt.Graphics;
import java.awt.GridLayout;
import java.awt.Image;
import java.awt.Insets;
import java.awt.Polygon;

class DiamondIcon implements Icon {
    private Color color;
    private boolean selected;
    private int width;
    private int height;
    private Polygon poly;
    private static final int DEFAULT_WIDTH = 10;
    private static final int DEFAULT_HEIGHT = 10;

    public DiamondIcon(Locus s, Color color, boolean selected) {
        this(s, color, selected, DEFAULT_WIDTH, DEFAULT_HEIGHT);
    }

    public DiamondIcon(Locus s, Color color, boolean selected, int width, int height) {
        this.color = color;
        this.selected = selected;
        this.width = width;
        this.height = height;
        initPolygon(s);
    }

    private void initPolygon(Locus s) {
        poly = new Polygon();
        int halfWidth = width / 2;
        int halfHeight = height / 2;
        switch ("" + s) {
            case "V()":
                poly.addPoint(0, 0);
                poly.addPoint(width, 0);
                poly.addPoint(width, height);
                poly.addPoint(0, height);
                break;
            case "E()":
                poly.addPoint(width / 4, 0);
                poly.addPoint(3 * width / 4, 0);
                poly.addPoint(3 * width / 4, height);
                poly.addPoint(width / 4, height);
                break;
            case "F()":
                poly.addPoint(width / 4, 0);
                poly.addPoint(3 * width / 4, 0);
                poly.addPoint(3 * width / 4, height);
                poly.addPoint(width / 4, height);
                break;
            default:
                poly.addPoint(0, halfHeight);
                poly.addPoint(halfWidth, 0);
                poly.addPoint(width, halfHeight);
                poly.addPoint(halfWidth, height);
                break;


        }

    }

    @Override
    public void paintIcon(Component c, Graphics g, int x, int y) {
        g.setColor(color);
        g.translate(x, y);
        if (selected) {
            g.fillPolygon(poly);
        } else {
            g.drawPolygon(poly);
        }
        g.translate(-x, -y);
    }

    @Override
    public int getIconWidth() {
        return width;
    }

    @Override
    public int getIconHeight() {
        return height;
    }
}