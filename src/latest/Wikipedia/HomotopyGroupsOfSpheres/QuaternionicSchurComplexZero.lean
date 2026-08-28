import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexComponents
import Wikipedia.HomotopyGroupsOfSpheres.ComplexUnitaryEntryNorm

/-!
# A vanishing constraint for the complex Schur component

The normalized cubic term cannot cancel a nonzero middle entry when the
two outer entries have norm at most one. This supplies an exact preimage
constraint for the midpoint of the projected matrix family.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexPlane

theorem schur_component_eq_zero_iff (x z y : ℂ) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    z - (1 + Complex.normSq z)⁻¹ • (x * star z * y) = 0 ↔ z = 0 := by
  constructor
  · intro h
    let d : ℝ := 1 + Complex.normSq z
    have hd : 0 < d := add_pos_of_pos_of_nonneg zero_lt_one (Complex.normSq_nonneg z)
    have he : d • z = x * star z * y := by
      calc
        d • z = d • (d⁻¹ • (x * star z * y)) := congrArg (fun w : ℂ ↦ d • w) (sub_eq_zero.mp h)
        _ = _ := by rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hd), one_smul]
    have hn := congrArg norm he
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd, norm_mul, norm_mul, norm_star] at hn
    have hb : ‖x‖ * ‖z‖ * ‖y‖ ≤ ‖z‖ := by
      calc
        _ ≤ 1 * ‖z‖ * ‖y‖ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hx (norm_nonneg z)) (norm_nonneg y)
        _ ≤ 1 * ‖z‖ * 1 := mul_le_mul_of_nonneg_left hy (by positivity)
        _ = _ := by ring
    rw [← hn] at hb
    by_contra hz
    have hp : 0 < Complex.normSq z * ‖z‖ :=
      mul_pos (Complex.normSq_pos.mpr hz) (norm_pos_iff.mpr hz)
    dsimp [d] at hb
    nlinarith
  · rintro rfl
    simp

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexPlane
