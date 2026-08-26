import ErdosProblems.Erdos633b.BoundaryRayCoordinates
import ErdosProblems.Erdos633b.HalfPlaneAngles

/-! A constructed angular coordinate on the inward half-plane at an outer
open-side point. Barycentric nonnegativity supplies every orientation hypothesis. -/

namespace Erdos633b.Triangle

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

noncomputable def boundaryOrientation (T : Triangle) (i : Fin 3) (p : Plane) :
    Orientation ℝ Plane (Fin 2) :=
  let o : Orientation ℝ Plane (Fin 2) := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  if 0 ≤ (o.oangle (T.points (i + 1) - p) (T.points i - p)).sign then o else -o

theorem boundaryOrientation_sign (T : Triangle) (i : Fin 3) (p : Plane) :
    0 ≤ ((T.boundaryOrientation i p).oangle (T.points (i + 1) - p) (T.points i - p)).sign := by
  unfold boundaryOrientation
  dsimp only
  split_ifs with h
  · exact h
  · rw [Orientation.oangle_neg_orientation_eq_neg, Real.Angle.sign_neg]
    exact (by decide : ∀ s : SignType, ¬0 ≤ s → 0 ≤ -s) _ h

theorem boundary_point_sign (T : Triangle) (i : Fin 3) {p : Plane}
    (hp : p ∈ T.openEdge i) {q : Plane} (hq : q ∈ T.support) :
    0 ≤ ((T.boundaryOrientation i p).oangle (T.points (i + 1) - p) (q - p)).sign := by
  rw [T.boundary_relative_coordinates i hp q,
    Orientation.oangle_sign_smul_add_smul_right]
  rcases (T.coord_nonneg hq i).eq_or_lt with ht | ht
  · rw [← ht, sign_zero, zero_mul]
  · rw [sign_pos ht, one_mul]
    exact T.boundaryOrientation_sign i p

noncomputable def boundaryAngle (T : Triangle) (i : Fin 3) (p q : Plane) : ℝ :=
  EuclideanGeometry.angle (T.points (i + 1)) p q

theorem boundaryAngle_nonneg (T : Triangle) (i : Fin 3) (p q : Plane) :
    0 ≤ T.boundaryAngle i p q := EuclideanGeometry.angle_nonneg _ _ _

theorem boundaryAngle_le_pi (T : Triangle) (i : Fin 3) (p q : Plane) :
    T.boundaryAngle i p q ≤ Real.pi := EuclideanGeometry.angle_le_pi _ _ _

theorem boundaryAngle_difference (T : Triangle) (i : Fin 3) {p q r : Plane}
    (hp : p ∈ T.openEdge i) (hq : q ∈ T.support) (hr : r ∈ T.support)
    (hqp : q ≠ p) (hrp : r ≠ p) :
    EuclideanGeometry.angle q p r = |T.boundaryAngle i p r - T.boundaryAngle i p q| := by
  exact HalfPlaneAngles.angle_eq_abs_sub (T.boundaryOrientation i p)
    (T.boundary_ray_ne_zero i hp (i + 1)) (sub_ne_zero.mpr hqp) (sub_ne_zero.mpr hrp)
    (T.boundary_point_sign i hp hq) (T.boundary_point_sign i hp hr)

theorem boundaryAngle_sameRay (T : Triangle) (i : Fin 3) {p q r : Plane}
    (hp : p ∈ T.openEdge i) (hq : q ∈ T.support) (hr : r ∈ T.support)
    (hqp : q ≠ p) (hrp : r ≠ p) (he : T.boundaryAngle i p q = T.boundaryAngle i p r) :
    SameRay ℝ (q - p) (r - p) := by
  exact HalfPlaneAngles.sameRay_of_angle_eq (T.boundaryOrientation i p)
    (T.boundary_ray_ne_zero i hp (i + 1)) (sub_ne_zero.mpr hqp) (sub_ne_zero.mpr hrp)
    (T.boundary_point_sign i hp hq) (T.boundary_point_sign i hp hr) he

theorem boundaryAngle_first_endpoint (T : Triangle) (i : Fin 3) {p : Plane}
    (hp : p ∈ T.openEdge i) : T.boundaryAngle i p (T.points (i + 1)) = 0 := by
  exact EuclideanGeometry.angle_self_of_ne
    (sub_ne_zero.mp (T.boundary_ray_ne_zero i hp (i + 1)))

theorem boundaryAngle_second_endpoint (T : Triangle) (i : Fin 3) {p : Plane}
    (hp : p ∈ T.openEdge i) : T.boundaryAngle i p (T.points (i + 2)) = Real.pi := by
  apply InnerProductGeometry.angle_eq_pi_iff.mpr
  refine ⟨T.boundary_ray_ne_zero i hp (i + 1),
    -(T.coord (i + 1) p / T.coord (i + 2) p), ?_, T.boundary_opposite_ray i hp⟩
  apply neg_neg_of_pos
  exact div_pos (hp.2 (i + 1) ((by decide : ∀ i : Fin 3, i + 1 ≠ i) i))
    (hp.2 (i + 2) ((by decide : ∀ i : Fin 3, i + 2 ≠ i) i))

end Erdos633b.Triangle
