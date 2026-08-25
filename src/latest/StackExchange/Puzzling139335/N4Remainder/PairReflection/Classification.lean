import StackExchange.Puzzling139335.PlaneIsometries.Matrix
import StackExchange.Puzzling139335.ReflectionSeparation.Maps
import StackExchange.Puzzling139335.SquareSymmetry.SideRigidity

/-!
# A reversing isometry preserving the bottom corner pair

Preserving the pair and fitting a set with nonempty interior in the square
forces the square center to be fixed. The two endpoint images and the
center image then determine every matrix entry. Determinant minus one
selects the vertical reflection; involutivity need not be assumed.
-/

open Set

namespace Puzzling139335.N4Remainder

open PlaneIsometries

private lemma eq_vertical_of_endpoint_coordinates (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hdet : (linearMatrix e).det = -1) (hcenter : e squareCenter = squareCenter)
    (a : ℝ) (hzero : e 0 = !₂[a, 0])
    (hfirst : e (EuclideanSpace.single 0 1) = !₂[1 - a, 0]) :
    e = ReflectionSeparation.vertical := by
  have h00 : linearMatrix e 0 0 = 1 - 2 * a := by
    rw [linearMatrix_apply_eq_sub, hfirst, hzero]
    simp only [Matrix.cons_val_zero]
    ring
  have h10 : linearMatrix e 1 0 = 0 := by
    rw [linearMatrix_apply_eq_sub, hfirst, hzero]
    simp
  have hx := congrArg (fun p : Plane => p 0)
    (affine_apply_eq_matrix_coordinates e squareCenter)
  have hy := congrArg (fun p : Plane => p 1)
    (affine_apply_eq_matrix_coordinates e squareCenter)
  rw [hcenter, hzero, h00] at hx
  rw [hcenter, hzero, h10] at hy
  norm_num [squareCenter] at hx hy
  have h01 : linearMatrix e 0 1 = 0 := by linarith only [hx]
  have h11 : linearMatrix e 1 1 = 1 := by linarith only [hy]
  rw [Matrix.det_fin_two, h00, h01, h10, h11] at hdet
  have ha : a = 1 := by linarith only [hdet]
  apply AffineIsometryEquiv.ext
  intro p
  rw [affine_apply_eq_matrix_coordinates e p]
  apply plane_ext
  · simp [h00, h01, hzero, ha, sub_eq_add_neg, add_comm]
    ring
  · simp [h10, h11, hzero]

/-- A reversing isometry fixing the square center and the bottom endpoint
pair is the vertical reflection. -/
theorem eq_vertical_of_center_fixed_and_bottom_pair (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hdet : (linearMatrix e).det = -1) (hcenter : e squareCenter = squareCenter)
    (hpair : e '' {corner 0, corner 1} = {corner 0, corner 1}) :
    e = ReflectionSeparation.vertical := by
  have hcorner0 : corner 0 = (0 : Plane) := by
    apply plane_ext <;> norm_num [corner, Fin.ext_iff]
  have hcorner1 : corner 1 = EuclideanSpace.single 0 (1 : ℝ) := by
    apply plane_ext <;> norm_num [corner, Fin.ext_iff]
  have hv0 : (!₂[(0 : ℝ), 0] : Plane) = 0 := by
    apply plane_ext <;> rfl
  have hv1 : EuclideanSpace.single 0 (1 : ℝ) = (!₂[(1 : ℝ), 0] : Plane) := by
    apply plane_ext <;> simp
  rcases SquareSymmetry.side_endpoints_either_order e 0 0 hpair with
    ⟨hzero, hfirst⟩ | ⟨hzero, hfirst⟩
  · apply eq_vertical_of_endpoint_coordinates e hdet hcenter 0
    · simpa only [zero_add, hcorner0, hv0] using hzero
    · simpa only [zero_add, hcorner1, sub_zero, ← hv1] using hfirst
  · apply eq_vertical_of_endpoint_coordinates e hdet hcenter 1
    · simpa only [zero_add, hcorner0, hcorner1, hv1] using hzero
    · simpa only [zero_add, hcorner0, hcorner1, sub_self, hv0] using hfirst

/-- An invariant set with nonempty interior inside the square rules out
reflection across the bottom supporting line. No involutivity assumption
is needed beyond the determinant and endpoint-pair hypotheses. -/
theorem eq_vertical_of_invariant_bottom_pair {P : Set Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hdet : (linearMatrix e).det = -1)
    (hpair : e '' {corner 0, corner 1} = {corner 0, corner 1})
    (hP : P ⊆ unitSquare) (hint : (interior P).Nonempty) (heP : e '' P = P) :
    e = ReflectionSeparation.vertical := by
  have htarget : e '' P ⊆ unitSquare := by
    rw [heP]
    exact hP
  have hcenter := SquareSymmetry.center_fixed_of_side_endpoints e 0 0
    hpair hP htarget hint
  exact eq_vertical_of_center_fixed_and_bottom_pair e hdet hcenter hpair

end Puzzling139335.N4Remainder
