/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceDyadicSmallCofactors
import ErdosProblems.Erdos4b.SourceDyadicResidualTailBound

/-!
# Large cofactors consume a vanishing fresh-prime budget

The ratio of full to small cofactor cutoffs is at most 2*4^r.
The reciprocal-totient tail therefore costs only O((1+r)/2^r)
times X/log X, for every fixed interval multiplier.
-/

namespace Erdos4b.SmoothParameters

noncomputable section

open Filter
open scoped BigOperators Topology

theorem log_full_div_smallCofactorCutoff_le {D r : ℕ} (hD : 0 < D) (hr : 2 ≤ r) :
    Real.log ((D * fullResidualCofactorCutoff r : ℕ) / (smallResidualCofactorCutoff D r : ℝ)) ≤
      Real.log 2 + (r : ℝ) * Real.log 4 := by
  have hM : (0 : ℝ) < smallResidualCofactorCutoff D r := by
    exact_mod_cast (show 0 < smallResidualCofactorCutoff D r by
      have := two_le_smallResidualCofactorCutoff hD hr; omega)
  have hB : (0 : ℝ) < (D * fullResidualCofactorCutoff r : ℕ) :=
    by exact_mod_cast Nat.mul_pos hD (fullResidualCofactorCutoff_pos (by omega))
  have hh := Real.log_le_log (div_pos hB hM) (full_div_smallCofactorCutoff_le hD hr)
  simpa only [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (4 : ℝ) ^ r ≠ 0),
    Real.log_pow] using hh

theorem tendsto_dyadicCofactorTailEnvelope_zero :
    Tendsto (fun r : ℕ ↦ (1 + Real.log 2 + (r : ℝ) * Real.log 4) / (2 : ℝ) ^ r)
      atTop (𝓝 0) := by
  have hp : Tendsto (fun r : ℕ ↦ (2 : ℝ) ^ r) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hbase : Tendsto (fun r : ℕ ↦ 1 / (2 : ℝ) ^ r) atTop (𝓝 0) := by
    simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp hp
  have hr : Tendsto (fun r : ℕ ↦ (r : ℝ) / (2 : ℝ) ^ r) atTop (𝓝 0) := by
    simpa only [pow_one] using tendsto_pow_const_div_const_pow_of_one_lt 1
      (by norm_num : (1 : ℝ) < 2)
  have hsum := (hbase.const_mul (1 + Real.log 2)).add (hr.const_mul (Real.log 4))
  simp only [mul_zero, add_zero] at hsum
  apply hsum.congr
  intro r
  ring

theorem dyadicCofactorTail_main_bound {C : ℝ} (hC : 0 ≤ C) {D r : ℕ}
    (hD : 0 < D) (hr : 2 ≤ r) (a : ℕ) :
    8 * C * (D * intervalLength a r : ℕ) *
        (1 + Real.log ((D * fullResidualCofactorCutoff r : ℕ) /
          (smallResidualCofactorCutoff D r : ℝ))) /
        (dyadicAmbientScale a r * dyadicCompanionScale r) ≤
      (16 * C * D * ((1 + Real.log 2 + (r : ℝ) * Real.log 4) / (2 : ℝ) ^ r)) *
        ((primaryFrontier a r : ℝ) / dyadicAmbientScale a r) := by
  have hV : 0 < dyadicAmbientScale a r := lt_of_lt_of_le (by norm_num)
    (one_le_dyadicAmbientScale a r)
  have hL : 0 < dyadicCompanionScale r := dyadicCompanionScale_pos (by omega)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  have hlogs := log_full_div_smallCofactorCutoff_le hD hr
  let t : ℝ := (8 * C * D * ((1 + Real.log 2 + (r : ℝ) * Real.log 4) / (2 : ℝ) ^ r)) *
    ((primaryFrontier a r : ℝ) / dyadicAmbientScale a r)
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  calc
    _ ≤ 8 * C * (D * intervalLength a r : ℕ) *
        (1 + Real.log 2 + (r : ℝ) * Real.log 4) /
        (dyadicAmbientScale a r * dyadicCompanionScale r) := by
      apply div_le_div_of_nonneg_right _ (mul_pos hV hL).le
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = (8 * C * D / dyadicAmbientScale a r) *
        ((intervalLength a r : ℝ) / dyadicCompanionScale r) *
        (1 + Real.log 2 + (r : ℝ) * Real.log 4) := by push_cast; ring
    _ = t / Real.log 2 := by
      rw [dyadicInterval_div_companion (by omega)]
      dsimp only [t]
      ring
    _ ≤ 2 * t := (div_le_iff₀ hlog2).mpr (by
      nlinarith [mul_le_mul_of_nonneg_left half_le_log_two ht])
    _ = _ := by dsimp only [t]; ring

theorem eventually_sum_dyadicLargeCofactorPrimeCount_le
    {D : ℕ} (hD : 0 < D) (a : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r in atTop, ∀ E : Finset ℕ,
      E ⊆ Finset.Ioc (smallResidualCofactorCutoff D r) (D * fullResidualCofactorCutoff r) →
      (∀ m ∈ E, Even m) →
      (∑ m ∈ E, ((residualPrimeFiber (D * intervalLength a r) (smoothFrontier r)
        (residualPrimeFrontier a r) m).card : ℝ)) ≤
        ε * ((primaryFrontier a r : ℝ) / dyadicAmbientScale a r) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_sum_dyadicResidualPrimeFiber_interval_bound
  have hlim : Tendsto
      (fun r : ℕ ↦ 16 * C * D * ((1 + Real.log 2 + (r : ℝ) * Real.log 4) / (2 : ℝ) ^ r))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_dyadicCofactorTailEnvelope_zero.const_mul (16 * C * D)
  filter_upwards [hbound a D, eventually_ge_atTop 2, hlim.eventually (gt_mem_nhds hε)]
    with r hr hrpos hsmall
  intro E hE heven
  have hM : 0 < smallResidualCofactorCutoff D r := by
    have := two_le_smallResidualCofactorCutoff hD hrpos
    omega
  have hcount := hr (smallResidualCofactorCutoff D r) (D * fullResidualCofactorCutoff r) E
    hM (smallResidualCofactorCutoff_le_full D r) le_rfl hE heven
  have hmain := dyadicCofactorTail_main_bound hC.le hD hrpos a
  apply (hcount.trans hmain).trans
  exact mul_le_mul_of_nonneg_right hsmall.le (by
    apply div_nonneg (Nat.cast_nonneg _)
    exact zero_le_one.trans (one_le_dyadicAmbientScale a r))

end

end Erdos4b.SmoothParameters
