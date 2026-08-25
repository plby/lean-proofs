import StackExchange.Puzzling139335.RectangularHull.Transport.Isometry
import StackExchange.Puzzling139335.RectangularHull.Transport.Normalization

/-!
# Transport and affine normalization of rectangular hulls

`Frame.map` transports a rectangle by an affine isometry, while
`Frame.fromUnitSquare` is an affine homeomorphism from the unit square onto
the rectangle.  The latter also transports the four vertices, center,
interior, and frontier, and normalizes arbitrary sets with the given
rectangular convex hull.
-/
