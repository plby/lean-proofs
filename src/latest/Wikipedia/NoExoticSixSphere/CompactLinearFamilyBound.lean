import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Group.Bounded

/-! # A uniform shrinking factor for a compact family of linear maps -/

open Set Metric

namespace NoExoticSixSphere

variable {M K F : Type*} [TopologicalSpace M] [CompactSpace M]
  [NormedAddCommGroup K] [NormedSpace ℝ K] [ProperSpace K]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_uniform_linear_family_bound (L : M → K →L[ℝ] F)
    (hc : Continuous (fun p : M × K ↦ L p.1 p.2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ m v, ‖L m v‖ ≤ C * ‖v‖ := by
  have hs := (isCompact_univ : IsCompact (univ : Set M)).prod
    (isCompact_closedBall (0 : K) 1)
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro m v
  by_cases hv : v = 0
  · simp only [hv, map_zero, norm_zero, mul_zero, le_refl]
  · have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hu : ‖‖v‖⁻¹ • v‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hvn.ne']
    have hb := hC (m, ‖v‖⁻¹ • v) ⟨mem_univ _, mem_closedBall_zero_iff.mpr hu⟩
    change ‖L m (‖v‖⁻¹ • v)‖ ≤ C at hb
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, ← div_eq_inv_mul] at hb
    exact ((div_le_iff₀ hvn).mp hb).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg v))

theorem exists_uniform_linear_family_shrink (L : M → K →L[ℝ] F)
    (hc : Continuous (fun p : M × K ↦ L p.1 p.2)) :
    ∃ s : ℝ, 0 < s ∧ ∀ m v, s * ‖L m v‖ ≤ ‖v‖ := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_linear_family_bound L hc
  refine ⟨C⁻¹, inv_pos.mpr hC, ?_⟩
  intro m v
  calc
    C⁻¹ * ‖L m v‖ ≤ C⁻¹ * (C * ‖v‖) :=
      mul_le_mul_of_nonneg_left (hb m v) (inv_nonneg.mpr hC.le)
    _ = ‖v‖ := by rw [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul]

end NoExoticSixSphere
