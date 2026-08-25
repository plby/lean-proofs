import StackExchange.Puzzling139335.RectangularHull.Frames

/-!
# Transport of rectangular frames by affine isometries

The four vertices, filled rectangle, and center all commute with an affine
isometry.  Consequently, so does the assertion that a set has the rectangle
as its convex hull.
-/

open Set

namespace Puzzling139335.RectangularHull

/-- Apply an affine isometry to a rectangle and its two edge vectors. -/
noncomputable def Frame.map (R : Frame) (e : Plane ≃ᵃⁱ[ℝ] Plane) : Frame where
  origin := e R.origin
  first := e.linearIsometryEquiv R.first
  second := e.linearIsometryEquiv R.second
  first_ne_zero := by simpa using R.first_ne_zero
  second_ne_zero := by simpa using R.second_ne_zero
  orthogonal := by
    rw [e.linearIsometryEquiv.inner_map_map]
    exact R.orthogonal

@[simp]
lemma Frame.map_origin (R : Frame) (e : Plane ≃ᵃⁱ[ℝ] Plane) :
    (R.map e).origin = e R.origin := rfl

@[simp]
lemma Frame.map_first (R : Frame) (e : Plane ≃ᵃⁱ[ℝ] Plane) :
    (R.map e).first = e.linearIsometryEquiv R.first := rfl

@[simp]
lemma Frame.map_second (R : Frame) (e : Plane ≃ᵃⁱ[ℝ] Plane) :
    (R.map e).second = e.linearIsometryEquiv R.second := rfl

private lemma affine_isometry_map_add (e : Plane ≃ᵃⁱ[ℝ] Plane) (p v : Plane) :
    e (p + v) = e p + e.linearIsometryEquiv v := by
  simpa only [vadd_eq_add, add_comm] using e.map_vadd p v

lemma Frame.map_vertices (R : Frame) (e : Plane ≃ᵃⁱ[ℝ] Plane) :
    (R.map e).vertices = e '' R.vertices := by
  simp only [vertices, map_origin, map_first, map_second,
    Set.image_insert_eq, Set.image_singleton, affine_isometry_map_add]

lemma Frame.map_carrier (R : Frame) (e : Plane ≃ᵃⁱ[ℝ] Plane) :
    (R.map e).carrier = e '' R.carrier := by
  change convexHull ℝ (R.map e).vertices = e '' convexHull ℝ R.vertices
  rw [R.map_vertices e]
  exact (e.toAffineEquiv.toAffineMap.image_convexHull R.vertices).symm

@[simp]
lemma Frame.map_center (R : Frame) (e : Plane ≃ᵃⁱ[ℝ] Plane) :
    (R.map e).center = e R.center := by
  simp only [center, map_origin, map_first, map_second,
    affine_isometry_map_add, map_smul, map_add]

/-- Transport a concrete rectangular convex-hull equality by an isometry. -/
lemma Frame.image_convexHull_eq_map_carrier (R : Frame) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    {P : Set Plane} (hP : convexHull ℝ P = R.carrier) :
    convexHull ℝ (e '' P) = (R.map e).carrier := by
  rw [R.map_carrier e]
  calc
    convexHull ℝ (e '' P) = e '' convexHull ℝ P :=
      (e.toAffineEquiv.toAffineMap.image_convexHull P).symm
    _ = e '' R.carrier := by rw [hP]

end Puzzling139335.RectangularHull
