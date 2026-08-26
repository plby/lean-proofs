/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceDyadicGlobalCover
import ErdosProblems.Erdos4b.SourceUnboundedProfiles

/-!
# Unconditional survivor covers for every multiplier on one fixed ray

The source profiles are now constructed by the unbounded variational
theorem. No probability or variational hypotheses remain in the result.
-/

namespace Erdos4b.SmoothParameters

noncomputable section

open Filter

theorem exists_dyadicRay_covers :
    ∃ a : ℕ, ∀ D : ℕ, 0 < D →
      ∀ᶠ r in atTop, ∃ data : SurvivorCoverData (D * intervalLength a r)
          (smoothFrontier r) (residualPrimeFrontier a r),
        smoothFrontier r ≤ residualPrimeFrontier a r ∧
        residualPrimeFrontier a r ≤ primaryFrontier a r ∧
        (∀ p ∈ data.measurePrimes, p ≤ primaryFrontier a r) ∧
        (∀ p ∈ data.freshPrimes, p ≤ primaryFrontier a r) := by
  obtain ⟨a, C, hC, hcovers⟩ := exists_dyadicRay_profileCovers.{0}
  refine ⟨a, ?_⟩
  intro D hD
  have hρ := dyadicAllocationDensity_pos hD
  have hproduct : (0 : ℝ) < 128 * C * D := by positivity
  obtain ⟨K, I, S, F, hF, hratio⟩ := exists_sourceProfile_ratio_gt
    (16 * Real.log (128 * C * D) / dyadicAllocationDensity D)
  let t := dyadicProfileCoverLevel D S F sourceCompanionProfile
  have ht : Real.log (128 * C * D) < t := by
    unfold t dyadicProfileCoverLevel
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr
    calc
      _ = (16 * Real.log (128 * C * D) / dyadicAllocationDensity D) *
          dyadicAllocationDensity D := by field_simp
      _ < sourceProfileRatio S F sourceCompanionProfile * dyadicAllocationDensity D :=
        mul_lt_mul_of_pos_right hratio hρ
      _ = _ := mul_comm _ _
  have he : 128 * C * D < Real.exp t := by
    rw [← Real.exp_log hproduct]
    exact Real.exp_lt_exp.mpr ht
  have hmiss : Real.exp (-t) * C * D ≤ (1 / 128 : ℝ) := by
    rw [Real.exp_neg]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 128)).mpr
    have hh : (128 * C * D) / Real.exp t < 1 := (div_lt_one (Real.exp_pos t)).mpr he
    have heq : (Real.exp t)⁻¹ * C * D * 128 = (128 * C * D) / Real.exp t := by ring
    rw [heq]
    exact hh.le
  exact hcovers I K D S F sourceCompanionProfile hD hF hmiss

end

end Erdos4b.SmoothParameters
