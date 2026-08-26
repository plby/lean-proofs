/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceDyadicSmallCofactors
import ErdosProblems.Erdos4b.SourceDyadicBoundaryCount
import ErdosProblems.Erdos4b.SourceDyadicAllocatedCoverage

/-!
# The lower boundary consumes a vanishing fresh-prime budget

Only small cofactors are retained for the random cover. The sum of all
their discarded boundary primes is o(X / log X), for each fixed K,D.
-/

namespace Erdos4b.SmoothParameters

noncomputable section

open Filter
open scoped BigOperators Topology

theorem residualPrimeFrontier_le_dyadicPinnedBoundary {K : ℕ} (hK : 0 < K) (a r : ℕ) :
    residualPrimeFrontier a r ≤ dyadicPinnedBoundary K a r := by
  calc
    _ ≤ residualPrimeFrontier a r * 2 ^ r := Nat.le_mul_of_pos_right _ (by positivity)
    _ = primaryFrontier a r := residualPrimeFrontier_mul_twoPow a r
    _ ≤ (primorial (sourcePreSieveCutoff r) * K) * primaryFrontier a r :=
      Nat.le_mul_of_pos_left _ (Nat.mul_pos (primorial_pos _) hK)
    _ = _ := rfl

theorem dyadicBoundary_main_bound {C : ℝ} (hC : 0 ≤ C) {r : ℕ} (hr : 0 < r)
    (K a D : ℕ)
    (hlog : (smallResidualCofactorCutoff D r : ℝ) *
      (1 + Real.log (smallResidualCofactorCutoff D r)) ≤ 5 * (D : ℝ) * core r * r) :
    8 * C * dyadicPinnedBoundary K a r * smallResidualCofactorCutoff D r *
        (1 + Real.log (smallResidualCofactorCutoff D r)) /
        (dyadicAmbientScale a r * dyadicCompanionScale r) ≤
      (80 * C * D * K * ((primorial (sourcePreSieveCutoff r) : ℝ) / (2 : ℝ) ^ r)) *
        ((primaryFrontier a r : ℝ) / dyadicAmbientScale a r) := by
  have hV : 0 < dyadicAmbientScale a r := lt_of_lt_of_le (by norm_num)
    (one_le_dyadicAmbientScale a r)
  have hL : 0 < dyadicCompanionScale r := dyadicCompanionScale_pos hr
  have hrr : (0 : ℝ) < r := by exact_mod_cast hr
  have hcore : (0 : ℝ) < core r := by exact_mod_cast core_pos r
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let t : ℝ := (40 * C * D * K * ((primorial (sourcePreSieveCutoff r) : ℝ) / (2 : ℝ) ^ r)) *
    ((primaryFrontier a r : ℝ) / dyadicAmbientScale a r)
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  calc
    _ = (8 * C * dyadicPinnedBoundary K a r /
        (dyadicAmbientScale a r * dyadicCompanionScale r)) *
        ((smallResidualCofactorCutoff D r : ℝ) *
          (1 + Real.log (smallResidualCofactorCutoff D r))) := by ring
    _ ≤ (8 * C * dyadicPinnedBoundary K a r /
        (dyadicAmbientScale a r * dyadicCompanionScale r)) * (5 * (D : ℝ) * core r * r) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = t / Real.log 2 := by
      dsimp only [t]
      simp only [dyadicPinnedBoundary, dyadicCompanionScale_eq, smoothExponent,
        rankinDenominator, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      field_simp
      ring
    _ ≤ 2 * t := (div_le_iff₀ hlog2).mpr (by
      nlinarith [mul_le_mul_of_nonneg_left half_le_log_two ht])
    _ = _ := by dsimp only [t]; ring

theorem eventually_sum_dyadicBoundaryPrimeCount_le
    {K D : ℕ} (hK : 0 < K) (hD : 0 < D) (a : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r in atTop, ∀ E : Finset ℕ,
      (∀ m ∈ E, 0 < m ∧ Even m ∧ m ≤ smallResidualCofactorCutoff D r) →
      (∑ m ∈ E, ((residualPrimeFiberBelow (D * intervalLength a r) (smoothFrontier r)
        (residualPrimeFrontier a r) m (dyadicPinnedBoundary K a r)).card : ℝ)) ≤
        ε * ((primaryFrontier a r : ℝ) / dyadicAmbientScale a r) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_sum_dyadicBoundaryPrimeCount_bound
  have hlim : Tendsto
      (fun r ↦ 80 * C * D * K * ((primorial (sourcePreSieveCutoff r) : ℝ) / (2 : ℝ) ^ r))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      tendsto_sourcePreSieve_primorial_div_twoPow_zero.const_mul (80 * C * D * K)
  filter_upwards [hbound a, eventually_ge_atTop 2, eventually_smallCofactor_log_weight_le hD,
    hlim.eventually (gt_mem_nhds hε)] with r hr hrpos hlog hsmall
  intro E hE
  have hM : 1 ≤ smallResidualCofactorCutoff D r :=
    (by norm_num : 1 ≤ (2 : ℕ)).trans (two_le_smallResidualCofactorCutoff hD hrpos)
  have hcount := hr (D * intervalLength a r) (dyadicPinnedBoundary K a r)
    (smallResidualCofactorCutoff D r) E hM hE (residualPrimeFrontier_le_dyadicPinnedBoundary hK a r)
  have hmain := dyadicBoundary_main_bound hC.le (by omega : 0 < r) K a D hlog
  apply (hcount.trans hmain).trans
  exact mul_le_mul_of_nonneg_right hsmall.le (by
    apply div_nonneg (Nat.cast_nonneg _)
    exact zero_le_one.trans (one_le_dyadicAmbientScale a r))

end

end Erdos4b.SmoothParameters
