import ErdosProblems.Erdos69.LargePrimeErrorBounds
import ErdosProblems.Erdos69.TailTruncation

/-! # Vanishing truncation error for the full signed tails -/

open Filter
open scoped BigOperators Topology

namespace Erdos69.Elementary

noncomputable def fullCharacteristic (q : ℝ) (m : ℕ) : ℂ :=
  (constructionLaw m).complexMean (fun t ↦ fourierPhase
    (q * arithmeticTail m (dilationPrimeCutoff m) (constructionPoint m t.val)))

theorem construction_tail_point_error (q : ℝ) (m : ℕ) (t : Fin (progressionLength m)) :
    |q * arithmeticTail m (dilationPrimeCutoff m) (constructionPoint m t.val) -
      constructionRetainedValue q m t.val| ≤
      coefficientMassBound q m *
        (Real.log (constructionUpperBound m : ℝ) / Real.log 2 + (6 * m + retainedLength m) + 2) /
          2 ^ retainedLength m := by
  have h := arithmeticTail_truncation_error m (dilationPrimeCutoff m) (constructionPoint m t.val)
    (retainedLength m) q
  have hsum : constructionRetainedValue q m t.val =
      ∑ r ∈ retainedShifts m (dilationPrimeCutoff m) (retainedLength m),
        shiftCoefficient m (dilationPrimeCutoff m) (retainedLength m) q r *
          omegaCount (constructionPoint m t.val + r) := by
    exact Finset.sum_coe_sort (retainedShifts m (dilationPrimeCutoff m) (retainedLength m))
      (fun r ↦ shiftCoefficient m (dilationPrimeCutoff m) (retainedLength m) q r *
        omegaCount (constructionPoint m t.val + r))
  rw [hsum]
  apply h.trans
  have hlog (i : PatternLabel m) : Real.log (constructionPoint m t.val + constructionDilation m i : ℕ) ≤
      Real.log (constructionUpperBound m : ℝ) := by
    apply Real.log_le_log (by have hp := constructionPoint_pos m t.val; positivity)
    exact_mod_cast sampled_dilation_le_upper m t i
  calc
    _ ≤ |q| * ∑ _i : PatternLabel m,
        (Real.log (constructionUpperBound m : ℝ) / Real.log 2 + (6 * m + retainedLength m) + 2) /
          2 ^ (6 * m + retainedLength m) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg q)
      apply Finset.sum_le_sum
      intro i hi
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hd : Real.log (constructionPoint m t.val +
          patternDilation m (dilationPrimeCutoff m) i : ℕ) / Real.log 2 ≤
          Real.log (constructionUpperBound m : ℝ) / Real.log 2 :=
        div_le_div_of_nonneg_right (hlog i) (Real.log_pos (by norm_num)).le
      linarith only [hd]
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, card_patternLabel, nsmul_eq_mul, Nat.cast_pow,
        Nat.cast_ofNat, pow_add]
      rw [show |q| * ((36 : ℝ) ^ m *
          ((Real.log (constructionUpperBound m : ℝ) / Real.log 2 +
            (6 * m + retainedLength m) + 2) / (2 ^ (6 * m) * 2 ^ retainedLength m))) =
          (|q| * ((36 : ℝ) ^ m / 2 ^ (6 * m))) *
            (Real.log (constructionUpperBound m : ℝ) / Real.log 2 +
              (6 * m + retainedLength m) + 2) / 2 ^ retainedLength m by ring]
      rw [pattern_mass_ratio]
      rfl

noncomputable def truncationError (m : ℕ) : ℝ :=
  (46 + 2 / Real.log 2) * ((fluctuationScale m : ℝ) + 1) / 2 ^ fluctuationScale m

theorem tendsto_truncationError : Tendsto truncationError atTop (𝓝 0) := by
  change Tendsto (fun m ↦ (46 + 2 / Real.log 2) *
    ((fluctuationScale m : ℝ) + 1) / 2 ^ fluctuationScale m) atTop (𝓝 0)
  simpa only [mul_div_assoc, mul_zero] using tendsto_scale_tail.const_mul (46 + 2 / Real.log 2)

theorem construction_tail_factor_le {m : ℕ} (hm : 0 < m) :
    (Real.log (constructionUpperBound m : ℝ) / Real.log 2 + (6 * m + retainedLength m) + 2) /
      2 ^ retainedLength m ≤ truncationError m := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hX := log_constructionUpperBound_le hm
  rw [log_progressionLength] at hX
  have hE : (excludedPrimeCutoff m : ℝ) ≤ (2 : ℝ) ^ fluctuationScale m := by
    have h := twice_excluded_le_two_pow_scale hm
    exact_mod_cast (show excludedPrimeCutoff m ≤ 2 ^ fluctuationScale m by omega)
  have hK : (6 * m : ℕ) ≤ fluctuationScale m := by
    apply (initialLength_le_patternSize m).trans
    change patternSize m ≤ patternSize m ^ 4
    simpa using Nat.pow_le_pow_right (patternSize_pos m) (show 1 ≤ 4 by omega)
  have hKR : (6 : ℝ) * m ≤ fluctuationScale m := by exact_mod_cast hK
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ fluctuationScale m := one_le_pow₀ (by norm_num)
  have hpowpos : (0 : ℝ) < (2 : ℝ) ^ fluctuationScale m := by positivity
  have hB : (0 : ℝ) ≤ fluctuationScale m := by positivity
  have hX' : Real.log (constructionUpperBound m : ℝ) / Real.log 2 ≤
      (40 * fluctuationScale m + 2 / Real.log 2) * (2 : ℝ) ^ fluctuationScale m := by
    apply (div_le_iff₀ hlog2).mpr
    have he := mul_le_mul_of_nonneg_left hE (by norm_num : (0 : ℝ) ≤ 2)
    field_simp
    nlinarith
  unfold truncationError retainedLength
  push_cast
  rw [pow_mul, pow_right_comm (2 : ℝ) 2 (fluctuationScale m)]
  apply (div_le_div_iff₀ (sq_pos_of_pos hpowpos) hpowpos).mpr
  have hmul := mul_le_mul_of_nonneg_right hX' hpowpos.le
  have hrest := mul_le_mul_of_nonneg_right hpow (by positivity : (0 : ℝ) ≤ 3 * fluctuationScale m + 2)
  have hconst : 0 ≤ 2 / Real.log 2 := by positivity
  nlinarith [mul_nonneg hconst hB]

theorem tendsto_full_sub_retained_norm (q : ℝ) :
    Tendsto (fun m ↦ ‖fullCharacteristic q m - retainedCharacteristic q m‖) atTop (𝓝 0) := by
  have hlim := tendsto_truncationError.const_mul (2 * Real.pi)
  simp only [mul_zero] at hlim
  apply squeeze_zero' (Filter.Eventually.of_forall (fun m ↦ norm_nonneg _)) _ hlim
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    (tendsto_coefficientMassBound q).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with m hm hε
  have hpoint (t : Fin (progressionLength m)) :
      |q * arithmeticTail m (dilationPrimeCutoff m) (constructionPoint m t.val) -
        constructionRetainedValue q m t.val| ≤ truncationError m := by
    apply (construction_tail_point_error q m t).trans
    rw [mul_div_assoc]
    calc
      _ ≤ coefficientMassBound q m * truncationError m :=
        mul_le_mul_of_nonneg_left (construction_tail_factor_le (by omega)) (by
          unfold coefficientMassBound; positivity)
      _ ≤ truncationError m := by
        have hn : 0 ≤ truncationError m := by unfold truncationError; positivity
        nlinarith
  have h := FiniteLaw.norm_mean_fourierPhase_sub_le (constructionLaw m)
    (fun t ↦ q * arithmeticTail m (dilationPrimeCutoff m) (constructionPoint m t.val))
    (fun t ↦ constructionRetainedValue q m t.val)
  apply h.trans
  have hmean := (constructionLaw m).mean_mono hpoint
  rw [FiniteLaw.mean_const] at hmean
  exact mul_le_mul_of_nonneg_left hmean (by positivity)

theorem tendsto_fullCharacteristic_norm {q : ℝ} (hq : 0 < q) :
    Tendsto (fun m ↦ ‖fullCharacteristic q m‖) atTop (𝓝 0) := by
  have h := (tendsto_retainedCharacteristic_norm hq).add (tendsto_full_sub_retained_norm q)
  simp only [add_zero] at h
  apply squeeze_zero (fun m ↦ norm_nonneg _) _ h
  intro m
  have ht := norm_le_norm_add_norm_sub (retainedCharacteristic q m) (fullCharacteristic q m)
  simpa only [norm_sub_rev (retainedCharacteristic q m)] using ht

end Erdos69.Elementary
