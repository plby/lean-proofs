import StackExchange.Puzzling139335.RectangularHull.Frames

/-!
# The rectangular-hull hypothesis

The hypothesis is an equality of actual convex hulls with a nondegenerate
rectangle. In particular it does not assume that the piece itself is convex.
-/

open Set

namespace Puzzling139335

def HasRectangularHull (P : Set Plane) : Prop :=
  ∃ R : RectangularHull.Frame, convexHull ℝ P = R.carrier

namespace HasRectangularHull

/-- Four orthogonal rectangle vertices and their exact hull give a
rectangular-hull witness. The fourth vertex is expressed by vector addition. -/
theorem of_vertices {P : Set Plane} {a u v : Plane}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : inner ℝ u v = 0)
    (hHull : convexHull ℝ P = convexHull ℝ {a, a + u, a + u + v, a + v}) :
    HasRectangularHull P :=
  ⟨⟨a, u, v, hu, hv, huv⟩, hHull⟩

end HasRectangularHull

end Puzzling139335
