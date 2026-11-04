// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Entry point `@symjs/symjs/geometry`: geometric entities in two and
 * three dimensions (SymPy sympy.geometry: points, lines, rays, segments,
 * planes, polygons, triangles, ellipses, circles, curves and parabolas)
 * and the functions of several entities (intersection, convex hull,
 * centroid, similarity, implicit differentiation).
 */

// every entry point brings the core with its registrations
import './core';

export { GeometryEntity, GeometrySet } from './geometry/entity';
export type { PointInput, ReflectionLine } from './geometry/entity';
export { GeometryError, Undecidable } from './geometry/exceptions';
export { Point, Point2D, Point3D } from './geometry/point';
export type { PointNode, Point2DNode, Point3DNode, PointOptions } from './geometry/point';
export { LinearEntity, Line, Line2D, Line3D, Ray, Ray2D, Ray3D, Segment, Segment2D, Segment3D } from './geometry/line';
export type { LineNode, Line2DNode, Line3DNode, RayNode, Ray2DNode, Ray3DNode, SegmentNode, Segment2DNode, Segment3DNode, LineOptions, RayOptions } from './geometry/line';
export { Plane } from './geometry/plane';
export type { PlaneNode, PlaneOptions } from './geometry/plane';
export { Ellipse, Circle } from './geometry/ellipse';
export type { EllipseNode, CircleNode, EllipseOptions } from './geometry/ellipse';
export { Polygon, RegularPolygon, Triangle, rad, deg } from './geometry/polygon';
export type { PolygonNode, RegularPolygonNode, TriangleNode, PolygonOptions, TriangleOptions } from './geometry/polygon';
export { Curve } from './geometry/curve';
export type { CurveNode } from './geometry/curve';
export { Parabola } from './geometry/parabola';
export type { ParabolaNode } from './geometry/parabola';
export { intersection, areSimilar, centroid, closestPoints, convexHull, farthestPoints, idiff, areCoplanar } from './geometry/util';
