import Wikipedia.SmoothSixDPoincare.ComplementCoefficientDeterminant
import Wikipedia.SmoothSixDPoincare.SmoothComplementQuotient
import Mathlib.Topology.Order.IntermediateValue

/-!
# Transfer endpoint determinant signs from actual frames to quotient coefficients

The determinant of a continuous invertible splitting cannot change sign
along the interval. The proved block determinant identity therefore makes
the endpoint coefficient sign condition equivalent to the endpoint sign
condition on the two actual full normal frames, in any one fixed model.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.FrameField

/-- A continuous real function avoiding zero has same-sign values at the interval endpoints. -/
theorem mul_endpoints_pos_of_continuous_nonzero {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) (hne : ∀ t ∈ Icc (0 : ℝ) 1, f t ≠ 0) :
    0 < f 0 * f 1 := by
  by_contra h
  rcases mul_nonpos_iff.mp (le_of_not_gt h) with h | h
  · obtain ⟨t, ht, hft⟩ :=
      intermediate_value_Icc' (show (0 : ℝ) ≤ 1 by norm_num) hf ⟨h.2, h.1⟩
    exact hne t ht hft
  · obtain ⟨t, ht, hft⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hf h
    exact hne t ht hft

section Endomorphisms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Actual continuous invertible operator fields have same-sign endpoint determinants. -/
theorem det_mul_endpoints_pos {T : ℝ → (E →L[ℝ] E)}
    (hT : ContinuousOn T (Icc (0 : ℝ) 1))
    (hi : ∀ t ∈ Icc (0 : ℝ) 1, Bijective (T t)) :
    0 < (T 0).toLinearMap.det * (T 1).toLinearMap.det := by
  apply mul_endpoints_pos_of_continuous_nonzero
    (ContinuousLinearMap.continuous_det.comp_continuousOn hT)
  intro t ht hz
  have hker : (T t).toLinearMap.ker ≠ ⊥ := LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz
  exact hker (LinearMap.ker_eq_bot.mpr (hi t ht).1)

end Endomorphisms

variable {D Z F : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The smooth splitting contributes no endpoint sign change to the actual coefficient field. -/
theorem same_sign_frames_iff_coefficients
    (j : (D × Z) ≃L[ℝ] F) {G : ℝ → (D →L[ℝ] F)} {C L : ℝ → (Z →L[ℝ] F)}
    (hG : ContDiffOn ℝ ∞ G (Icc (0 : ℝ) 1))
    (hC : ContDiffOn ℝ ∞ C (Icc (0 : ℝ) 1))
    (hi : ∀ t ∈ Icc (0 : ℝ) 1, ((G t).coprod (C t)).IsInvertible) :
    (0 < (j.symm.toContinuousLinearMap.comp ((G 0).coprod (L 0))).toLinearMap.det *
      (j.symm.toContinuousLinearMap.comp ((G 1).coprod (L 1))).toLinearMap.det) ↔
    (0 < ((complementQuotient (G 0) (C 0)).comp (L 0)).toLinearMap.det *
      ((complementQuotient (G 1) (C 1)).comp (L 1)).toLinearMap.det) := by
  let T (t : ℝ) := j.symm.toContinuousLinearMap.comp ((G t).coprod (C t))
  have hs : ContDiffOn ℝ ∞ T (Icc (0 : ℝ) 1) :=
    contDiffOn_const.clm_comp (contDiffOn_coprod hG hC)
  have hT : ∀ t ∈ Icc (0 : ℝ) 1, Bijective (T t) :=
    fun t ht => j.symm.bijective.comp (hi t ht).bijective
  have hpositive := det_mul_endpoints_pos hs.continuousOn hT
  have h0 := det_frame_eq_det_split_mul_det_coefficient j (G 0) (C 0) (L 0)
    (hi 0 (by simp))
  have h1 := det_frame_eq_det_split_mul_det_coefficient j (G 1) (C 1) (L 1)
    (hi 1 (by simp))
  rw [h0, h1]
  have heq :
      ((T 0).toLinearMap.det * ((complementQuotient (G 0) (C 0)).comp (L 0)).toLinearMap.det) *
        ((T 1).toLinearMap.det * ((complementQuotient (G 1) (C 1)).comp (L 1)).toLinearMap.det) =
      ((T 0).toLinearMap.det * (T 1).toLinearMap.det) *
        (((complementQuotient (G 0) (C 0)).comp (L 0)).toLinearMap.det *
          ((complementQuotient (G 1) (C 1)).comp (L 1)).toLinearMap.det) := by ring
  change (0 < ((T 0).toLinearMap.det * _) * ((T 1).toLinearMap.det * _)) ↔ _
  rw [heq]
  exact mul_pos_iff_of_pos_left hpositive

end Wikipedia.SmoothSixDPoincare.FrameField
