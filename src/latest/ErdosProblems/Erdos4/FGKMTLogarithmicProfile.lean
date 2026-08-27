import ErdosProblems.Erdos4.Base

/-!
# An explicit logarithmic-gain variational family

The earlier base development already contains the needed product-profile
integrals and Markov estimate. This file exposes their quantitative gain
in terms of the dimension, rather than just an arbitrary fixed constant.
-/

namespace Erdos4.FGKMT

open VariableMaynard

theorem parameter_log_dimension (j : ℕ) :
    Real.log (parameterK j : ℝ) = (j : ℝ) * Real.log 2 := by
  unfold parameterK
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

theorem parameter_logarithmic_gain {j : ℕ} (hj : 8 ≤ j) :
    Real.log (parameterK j : ℝ) / 72 <
      BoundedGaps.Maynard.maynardRatio (parameterK j) (candidate (parameterK j) (parameterA j)) := by
  have hlog2 : Real.log 2 ≤ 1 := Real.log_two_lt_d9.le.trans (by norm_num)
  have hlog : Real.log (parameterK j : ℝ) ≤ (j : ℝ) := by
    rw [parameter_log_dimension]
    exact mul_le_of_le_one_right (Nat.cast_nonneg j) hlog2
  exact (div_le_div_of_nonneg_right hlog (by norm_num)).trans_lt (parameter_ratio_gt hj)

/-- Every member has the required support and integrability, lies in `[0,1]`,
has positive normalization, and achieves a fixed positive multiple of log dimension. -/
theorem logarithmic_profile_family {j : ℕ} (hj : 8 ≤ j) :
    BoundedGaps.Maynard.MaynardAdmissible (parameterK j)
        (candidate (parameterK j) (parameterA j)) ∧
      (∀ t, 0 ≤ candidate (parameterK j) (parameterA j) t ∧
        candidate (parameterK j) (parameterA j) t ≤ 1) ∧
      0 < BoundedGaps.Maynard.maynardI (parameterK j) (candidate (parameterK j) (parameterA j)) ∧
      Real.log (parameterK j : ℝ) / 72 <
        BoundedGaps.Maynard.maynardRatio (parameterK j) (candidate (parameterK j) (parameterA j)) := by
  have hA := parameterA_pos (by omega : 0 < j)
  exact ⟨candidate_admissible hA, fun t => ⟨candidate_nonneg hA t, candidate_le_one hA t⟩,
    maynardI_candidate_pos (parameterK_pos j) hA, parameter_logarithmic_gain hj⟩

end Erdos4.FGKMT
