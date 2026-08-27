import ErdosProblems.Erdos4.FGKMTTranslatedCenterLaw
import ErdosProblems.Erdos4.FGKMTCombinedPrimeFamily
import ErdosProblems.Erdos4.FGKMTModulusLevel

/-! The growing parameters satisfy the concrete normalization and atom budgets. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Filter ProductCharacterEncoding BoundedGaps.Maynard

theorem rowCost_precut_bound {k : ℕ} (hk : 1 ≤ k) :
    (k : ℝ) * LocalIndicatorExpansion.rowCost k ≤ (16 * k ^ 4 : ℕ) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold LocalIndicatorExpansion.rowCost
  push_cast
  nlinarith [sq_nonneg ((k : ℝ) - 1), sq_nonneg ((k : ℝ) ^ 2 - 1)]

theorem sievePrime_normalization_tail {W R k : ℕ} (hk : 1 ≤ k)
    (hpre : ∀ p : ℕ, p.Prime → p ≤ 16 * k ^ 4 → p ∣ W) :
    (k : ℝ) * LocalIndicatorExpansion.rowCost k *
      ∑ p : SievePrime W R, 1 / (sievePrimeValue W R p : ℝ) ^ 2 ≤ 1 := by
  have hD : 0 < 16 * k ^ 4 := by positivity
  have hDR : (0 : ℝ) < (16 * k ^ 4 : ℕ) := by exact_mod_cast hD
  have ht := sievePrimeValue_square_tail (R := R) hD hpre
  have hc := rowCost_precut_bound hk
  simp only [one_div]
  calc
    _ ≤ ((k : ℝ) * LocalIndicatorExpansion.rowCost k) * ((16 * k ^ 4 : ℕ) : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left ht
        (mul_nonneg (Nat.cast_nonneg k) (LocalIndicatorExpansion.rowCost_nonneg k))
    _ ≤ 1 := by
      rw [← div_eq_mul_inv]
      exact (div_le_one hDR).mpr hc

theorem growing_sievePrime_size (x B R : ℕ)
    (p : SievePrime (harmonicModulus (growingPrecutoff x) B) R) :
    sieveDimension (growingIndex x) + 2 ≤
      sievePrimeValue (harmonicModulus (growingPrecutoff x) B) R p := by
  let k := sieveDimension (growingIndex x)
  have hk : 1 ≤ k := sieveDimension_pos (growingIndex x)
  have hk4 : k ≤ k ^ 4 := Nat.le_pow (by norm_num)
  have hD : k + 1 ≤ growingPrecutoff x := by
    change k + 1 ≤ 16 * k ^ 4
    omega
  have hp := sievePrimeValue_above_precut
    (fun q hq hqD => small_prime_dvd_harmonicModulus (growingPrecutoff x) B hq hqD) p
  change k + 2 ≤ _
  omega

theorem growing_sievePrime_normalization_tail (x B R : ℕ) :
    (sieveDimension (growingIndex x) : ℝ) *
      LocalIndicatorExpansion.rowCost (sieveDimension (growingIndex x)) *
        ∑ p : SievePrime (harmonicModulus (growingPrecutoff x) B) R,
          1 / (sievePrimeValue (harmonicModulus (growingPrecutoff x) B) R p : ℝ) ^ 2 ≤ 1 :=
  sievePrime_normalization_tail (sieveDimension_pos (growingIndex x))
    (fun p hp hpD => small_prime_dvd_harmonicModulus (growingPrecutoff x) B hp hpD)

theorem eventually_growing_weight_numerator :
    ∀ᶠ x : ℕ in atTop, ∀ a : ℝ, a ≤ 1 / 4 → ∀ B : ℕ,
      (B = 1 ∨ B.Prime) → B ≤ exponentialConductorCutoff a x →
      (smallPresieveModulus (growingPrecutoff x) B : ℝ) *
        (Real.exp 1 ^ 2 * (growingRadius x : ℝ) ^ 4) ≤ (x : ℝ) ^ (1 / 10 : ℝ) := by
  have hlogTop := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_harmonicModulus_log_small, eventually_growingRadius_bounds,
    hlogTop.eventually (eventually_ge_atTop 200), eventually_ge_atTop 1]
    with x hW hR hlog hx
  change 200 ≤ Real.log (x : ℝ) at hlog
  intro a ha B hB hBx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hRpos : (0 : ℝ) < growingRadius x := by exact_mod_cast (by omega : 0 < growingRadius x)
  have hMpos : (0 : ℝ) < smallPresieveModulus (growingPrecutoff x) B := by
    exact_mod_cast smallPresieveModulus_pos (growingPrecutoff x) B
  have hMdvd : smallPresieveModulus (growingPrecutoff x) B ∣
      harmonicModulus (growingPrecutoff x) B :=
    (smallPresieveModulus_dvd_primorial (growingPrecutoff x) B).trans
      (primorial_dvd_harmonicModulus (growingPrecutoff x) B)
  have hMle : (smallPresieveModulus (growingPrecutoff x) B : ℝ) ≤
      harmonicModulus (growingPrecutoff x) B := by
    exact_mod_cast Nat.le_of_dvd (harmonicModulus_pos (growingPrecutoff x) hB) hMdvd
  have hMlog := (Real.log_le_log hMpos hMle).trans (hW a ha B hB hBx)
  have hRlog : Real.log (growingRadius x : ℝ) ≤ (1 / 50 : ℝ) * Real.log (x : ℝ) := by
    have hh := Real.log_le_log hRpos (growingRadius_upper x)
    simpa only [Real.log_rpow hxpos] using hh
  let N : ℝ := (smallPresieveModulus (growingPrecutoff x) B : ℝ) *
    (Real.exp 1 ^ 2 * (growingRadius x : ℝ) ^ 4)
  have hNpos : 0 < N := by dsimp only [N]; positivity
  have hNlog : Real.log N ≤ Real.log (x : ℝ) * (1 / 10 : ℝ) := by
    dsimp only [N]
    rw [Real.log_mul hMpos.ne' (mul_pos (sq_pos_of_pos (Real.exp_pos 1)) (pow_pos hRpos 4)).ne',
      Real.log_mul (pow_ne_zero 2 (Real.exp_ne_zero 1)) (pow_ne_zero 4 hRpos.ne'),
      Real.log_pow, Real.log_pow, Real.log_exp]
    norm_num only [Nat.cast_ofNat]
    linarith
  change N ≤ _
  calc
    _ = Real.exp (Real.log N) := (Real.exp_log hNpos).symm
    _ ≤ Real.exp (Real.log (x : ℝ) * (1 / 10 : ℝ)) := Real.exp_le_exp.mpr hNlog
    _ = _ := (Real.rpow_def_of_pos hxpos (1 / 10 : ℝ)).symm

theorem eventually_growing_normalization_budget :
    ∀ᶠ x : ℕ in atTop, ∀ a : ℝ, a ≤ 1 / 4 → ∀ B : ℕ,
      (B = 1 ∨ B.Prime) → B ≤ exponentialConductorCutoff a x → ∀ Y : ℕ, x ≤ Y →
      (smallPresieveModulus (growingPrecutoff x) B : ℝ) *
        (Real.exp 1 ^ 2 * (growingRadius x : ℝ) ^ 4) ≤ Y := by
  filter_upwards [eventually_growing_weight_numerator, eventually_ge_atTop 1] with x hnum hx
  intro a ha B hB hBx Y hY
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hpow : (x : ℝ) ^ (1 / 10 : ℝ) ≤ x := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hxR (by norm_num : (1 / 10 : ℝ) ≤ 1)
  exact (hnum a ha B hB hBx).trans (hpow.trans (by exact_mod_cast hY))

end Erdos4.FGKMT
