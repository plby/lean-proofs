import ErdosProblems.Erdos69.TruncationErrorBounds

/-! # Rationality forces the full characteristic function to approach one -/

open Filter
open scoped BigOperators Topology

namespace Erdos69.Elementary

theorem dilationPrimeCutoff_ge_two (m : ℕ) : 2 ≤ dilationPrimeCutoff m := by
  unfold dilationPrimeCutoff
  exact Nat.one_lt_two_pow (Nat.pow_pos (patternSize_pos m)).ne'

theorem constructionDilation_log_le (m : ℕ) (i : PatternLabel m) :
    Real.log (constructionDilation m i : ℝ) ≤ 5 * dilationPrimeCutoff m := by
  apply le_trans _ (log_constructionMaxDilation_le m)
  exact Real.log_le_log (by exact_mod_cast constructionDilation_pos m i)
    (by exact_mod_cast constructionDilation_le_max m i)

theorem constructionDilation_omega_le (m : ℕ) (i : PatternLabel m) :
    (omegaCount (constructionDilation m i) : ℝ) ≤ 5 * dilationPrimeCutoff m / Real.log 2 := by
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  exact (omegaCount_mul_log_two_le (constructionDilation_pos m i)).trans
    (constructionDilation_log_le m i)

theorem constructionDilation_reciprocal_le (m : ℕ) (i : PatternLabel m) :
    (∑ p ∈ (constructionDilation m i).primeFactors, (1 : ℝ) / p) ≤
      5 / Real.log (dilationPrimeCutoff m : ℝ) :=
  roughDilation_reciprocal_mass_le (dilationPrimeCutoff_ge_two m)
    ((patternDigit_lt m i).le.trans (digitRange_le_dilationPrimeCutoff m))

theorem construction_correction_mean_le (m : ℕ) (i : PatternLabel m) :
    (constructionLaw m).mean (fun t ↦ compositeCorrection (constructionDilation m i)
      ((constructionPoint m t.val - constructionOffset m i) / constructionDilation m i)) ≤
        5 / Real.log (dilationPrimeCutoff m : ℝ) +
          5 * dilationPrimeCutoff m / (Real.log 2 * progressionLength m) := by
  simp_rw [construction_quotient_affine]
  have h := FiniteLaw.uniform_compositeCorrection_le (progressionLength m) (constructionDilation m i)
    (constructionModulus m / constructionDilation m i)
    ((constructionBase m - constructionOffset m i) / constructionDilation m i)
    (progressionLength_pos m) (fun p hp ↦
      (construction_quotient_coprime m i).of_dvd_right (Nat.mem_primeFactors.mp hp).2.1)
  apply h.trans
  have hw := div_le_div_of_nonneg_right (constructionDilation_omega_le m i)
    (by positivity : (0 : ℝ) ≤ progressionLength m)
  have hr := constructionDilation_reciprocal_le m i
  calc
    _ ≤ 5 / Real.log (dilationPrimeCutoff m : ℝ) +
        (5 * dilationPrimeCutoff m / Real.log 2) / progressionLength m := add_le_add hr hw
    _ = _ := by ring

theorem rational_fullCharacteristic_bound {q : ℕ} {z : ℤ}
    (h : (q : ℝ) * binaryOmegaSum = z) (m : ℕ) :
    ‖fullCharacteristic q m - 1‖ ≤ 2 * Real.pi * q * patternSize m *
      (5 / Real.log (dilationPrimeCutoff m : ℝ) +
        5 * dilationPrimeCutoff m / (Real.log 2 * progressionLength m)) := by
  have hphase := FiniteLaw.rational_signed_tail_phase_le h (constructionLaw m)
    (constructionDilation m) (fun i ↦ (constructionDilation_pos m i).ne')
    (patternSign m) (patternSign_abs_real m)
    (fun t i ↦ (constructionPoint m t.val - constructionOffset m i) / constructionDilation m i)
  have heq (t : Fin (progressionLength m)) :
      (∑ i : PatternLabel m, (patternSign m i : ℝ) * dilatedPositiveTail (constructionDilation m i)
        ((constructionPoint m t.val - constructionOffset m i) / constructionDilation m i)) =
        arithmeticTail m (dilationPrimeCutoff m) (constructionPoint m t.val) :=
    signed_dilatedTail_eq_arithmeticTail m _ _ (constructionPoint_modEq m t.val)
      (constructionOffset_le_point m t.val)
  simp_rw [heq] at hphase
  apply hphase.trans
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (PatternLabel m))) ↦
    construction_correction_mean_le m i)
  simp only [Finset.sum_const, Finset.card_univ, card_patternLabel, nsmul_eq_mul,
    Nat.cast_pow, Nat.cast_ofNat] at hsum
  have hmul := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 2 * Real.pi * (q : ℝ))
  simpa only [patternSize, Nat.cast_pow, Nat.cast_ofNat, mul_assoc] using hmul

theorem size_primeCutoff_ratio_le {m : ℕ} (hm : 0 < m) :
    (patternSize m : ℝ) * dilationPrimeCutoff m / progressionLength m ≤
      (1 : ℝ) / 2 ^ fluctuationScale m := by
  have hNpow : patternSize m ≤ patternSize m ^ 12 := by
    simpa using Nat.pow_le_pow_right (patternSize_pos m) (show 1 ≤ 12 by omega)
  have hNP : patternSize m * dilationPrimeCutoff m ≤ 2 ^ fluctuationScale m := by
    apply (Nat.mul_le_mul_right _ hNpow).trans
    apply (polynomial_primeCutoff_le_excluded hm).trans
    have h := twice_excluded_le_two_pow_scale hm
    omega
  have hT : 2 ^ (2 * fluctuationScale m) ≤ progressionLength m := by
    calc
      _ ≤ 2 ^ (40 * fluctuationScale m) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ _ := Nat.pow_le_pow_left (smallPrimeCutoff_ge_two m) _
  have hNPR : (patternSize m : ℝ) * dilationPrimeCutoff m ≤ (2 : ℝ) ^ fluctuationScale m := by
    exact_mod_cast hNP
  have hTR : ((2 : ℝ) ^ fluctuationScale m) ^ 2 ≤ progressionLength m := by
    have h := hT
    rw [Nat.mul_comm 2, pow_mul] at h
    exact_mod_cast h
  apply (div_le_div_iff₀ (by exact_mod_cast progressionLength_pos m : (0 : ℝ) < progressionLength m)
    (by positivity : (0 : ℝ) < 2 ^ fluctuationScale m)).mpr
  have hmul := mul_le_mul_of_nonneg_right hNPR (by positivity : (0 : ℝ) ≤ 2 ^ fluctuationScale m)
  nlinarith

noncomputable def correctionError (q : ℝ) (m : ℕ) : ℝ :=
  (5 * |q| / Real.log 2) * ((1 : ℝ) / patternSize m + 1 / 2 ^ fluctuationScale m)

theorem tendsto_correctionError (q : ℝ) : Tendsto (correctionError q) atTop (𝓝 0) := by
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).comp tendsto_fluctuationScale
  have hp' : Tendsto (fun m ↦ (1 : ℝ) / 2 ^ fluctuationScale m) atTop (𝓝 0) := by
    simpa only [div_pow, one_pow, Function.comp_def] using hp
  change Tendsto (fun m ↦ (5 * |q| / Real.log 2) *
    ((1 : ℝ) / patternSize m + 1 / 2 ^ fluctuationScale m)) atTop (𝓝 0)
  simpa only [add_zero, mul_zero] using
    (tendsto_inverse_patternSize.add hp').const_mul (5 * |q| / Real.log 2)

theorem construction_correction_error_le {m : ℕ} (hm : 0 < m) (q : ℝ) (hq : 0 ≤ q) :
    q * patternSize m * (5 / Real.log (dilationPrimeCutoff m : ℝ) +
      5 * dilationPrimeCutoff m / (Real.log 2 * progressionLength m)) ≤ correctionError q m := by
  have hN : (0 : ℝ) < patternSize m := by exact_mod_cast patternSize_pos m
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  rw [log_dilationPrimeCutoff]
  have heq : q * patternSize m * (5 / ((patternSize m : ℝ) ^ 2 * Real.log 2) +
      5 * dilationPrimeCutoff m / (Real.log 2 * progressionLength m)) =
      (5 * q / Real.log 2) * ((1 : ℝ) / patternSize m +
        (patternSize m : ℝ) * dilationPrimeCutoff m / progressionLength m) := by
    field_simp
  rw [heq, correctionError, abs_of_nonneg hq]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add le_rfl (size_primeCutoff_ratio_le hm)

theorem tendsto_full_sub_one_norm_of_rational {q : ℕ} {z : ℤ}
    (h : (q : ℝ) * binaryOmegaSum = z) :
    Tendsto (fun m ↦ ‖fullCharacteristic q m - 1‖) atTop (𝓝 0) := by
  have hlim := (tendsto_correctionError (q : ℝ)).const_mul (2 * Real.pi)
  simp only [mul_zero] at hlim
  apply squeeze_zero' (Filter.Eventually.of_forall (fun m ↦ norm_nonneg _)) _ hlim
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  apply (rational_fullCharacteristic_bound h m).trans
  have hb := mul_le_mul_of_nonneg_left (construction_correction_error_le (m := m) (by omega) (q : ℝ)
    (by positivity)) (by positivity : 0 ≤ 2 * Real.pi)
  simpa only [mul_assoc] using hb

end Erdos69.Elementary
