import ErdosProblems.Erdos67b.PrimeGraphRestriction
import ErdosProblems.Erdos67b.PrimeGraphFourierBound
import ErdosProblems.Erdos67b.PrimeGraphConcentration

/-!
# Uniform bounds for prime graph frequencies

At fixed shift, the dyadic prime block is comparable to the block length.
The sharp fourth moment therefore bounds the number of exceptional
frequencies independently of that length.
-/

open scoped BigOperators
open Finset Filter

namespace Erdos67b

noncomputable section

theorem norm_primeGraphMultiplier_le_reciprocal_sum
    (T h : ℕ) (s : Finset ℕ) (t : ℤ) :
    ‖primeGraphMultiplier T h s t‖ ≤ ∑ p ∈ s, (p : ℝ)⁻¹ := by
  calc
    _ ≤ ∑ p ∈ s, ‖(p : ℂ)⁻¹ * Erdos438.Fourier.phase T t (p * h : ℕ)‖ := norm_sum_le _ _
    _ = _ := by
      simp only [norm_mul, norm_inv, Complex.norm_natCast, Erdos438.Fourier.norm_phase, mul_one]

theorem norm_dyadic_primeGraphMultiplier_le_primeCounting
    (T h : ℕ) {P : ℕ} (hP : 0 < P) (t : ℤ) :
    ‖primeGraphMultiplier T h (PrimeEstimates.dyadicPrimes P) t‖ ≤
      (Nat.primeCounting (2 * P) : ℝ) / P := by
  have hPr : (0 : ℝ) < P := Nat.cast_pos.mpr hP
  have hs : PrimeEstimates.dyadicPrimes P ⊆ Nat.primesLE (2 * P) := by
    intro p hp
    have hp' := PrimeEstimates.mem_primesInInterval.mp hp
    exact Nat.mem_primesLE.mpr ⟨hp'.2.1, hp'.2.2⟩
  have hcard : (PrimeEstimates.dyadicPrimes P).card ≤ Nat.primeCounting (2 * P) := by
    simpa only [Nat.primesLE_card_eq_primeCounting] using Finset.card_le_card hs
  calc
    _ ≤ ∑ p ∈ PrimeEstimates.dyadicPrimes P, (p : ℝ)⁻¹ :=
      norm_primeGraphMultiplier_le_reciprocal_sum _ _ _ _
    _ ≤ ∑ _p ∈ PrimeEstimates.dyadicPrimes P, (P : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      exact inv_anti₀ hPr (by exact_mod_cast (PrimeEstimates.mem_primesInInterval.mp hp).1.le)
    _ = (PrimeEstimates.dyadicPrimes P).card / (P : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
    _ ≤ (Nat.primeCounting (2 * P) : ℝ) / P := by gcongr

/-- Elementary comparisons for the quotient defining a fixed-relative
dyadic block, including the logarithm comparison. -/
theorem primeGraph_quotient_comparisons {H K P₀ : ℕ}
    (hK : 2 ≤ K) (hP₀ : 2 * K ≤ P₀) (hH : K * P₀ ≤ H) :
    P₀ ≤ H / K ∧ 2 * (H / K) ≤ H ∧
      (H : ℝ) ≤ 2 * K * (H / K : ℕ) ∧
      0 < Real.log (H / K : ℕ) ∧ 0 < Real.log (H : ℝ) ∧
      Real.log (H : ℝ) ≤ 2 * Real.log (H / K : ℕ) := by
  have hKpos : 0 < K := by omega
  have hP : P₀ ≤ H / K := (Nat.le_div_iff_mul_le hKpos).mpr (by simpa [mul_comm] using hH)
  have hdiv := Nat.div_mul_le_self H K
  have hlt := Nat.lt_mul_div_succ H hKpos
  have hP2 : 2 ≤ H / K := by omega
  have htwice : 2 * (H / K) ≤ H := by nlinarith
  have hratio : H ≤ 2 * K * (H / K) := by nlinarith
  have hsquare : H ≤ (H / K) ^ 2 := by nlinarith
  have hlogP : 0 < Real.log (H / K : ℕ) := Real.log_pos (by exact_mod_cast (by omega : 1 < H / K))
  have hlogH : 0 < Real.log (H : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < H))
  refine ⟨hP, htwice, by exact_mod_cast hratio, hlogP, hlogH, ?_⟩
  have hlog := Real.log_le_log (show (0 : ℝ) < H by exact_mod_cast (by omega : 0 < H))
    (show (H : ℝ) ≤ (H / K : ℕ) ^ 2 by exact_mod_cast hsquare)
  simpa only [Real.log_pow, Nat.cast_ofNat] using hlog

/-- Sharp fourth moment and a uniform supremum bound for the actual
multiplier used by the entropy-selected graph lower bound. -/
theorem exists_eventually_primeGraphMultiplier_bounds {h : ℕ} (hh : 0 < h) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₁ : ℕ, 2 ≤ H₁ ∧ ∀ H ≥ H₁,
      let P := H / (4 * h + 4)
      let T := 4 * h * H + 1
      (∑ t ∈ Finset.range T,
        ‖primeGraphMultiplier T h (PrimeEstimates.dyadicPrimes P) (t : ℤ)‖ ^ 4 ≤
          C / Real.log H ^ 4) ∧
        ∀ t : ℤ, ‖primeGraphMultiplier T h (PrimeEstimates.dyadicPrimes P) t‖ ≤
          16 / Real.log H := by
  obtain ⟨A, hA, P₀, hP₀, hfourth⟩ := exists_dyadic_primeGraphMultiplier_fourth_moment_bound
  obtain ⟨P₁, hprime⟩ := Filter.eventually_atTop.mp eventually_primeCounting_le_four_mul_div_log
  let K : ℕ := 4 * h + 4
  have hK : 2 ≤ K := by dsimp [K]; omega
  let P₂ : ℕ := max (max P₀ P₁) (2 * K)
  have hP₂ : 2 * K ≤ P₂ := le_max_right _ _
  let C : ℝ := 32 * A * K * (4 * h + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, max 2 (K * P₂), le_max_left _ _, ?_⟩
  intro H hHH
  let P := H / K
  let T := 4 * h * H + 1
  obtain ⟨hPP₂, hPH, hratio, hlogP, hlogH, hlogratio⟩ :=
    primeGraph_quotient_comparisons hK hP₂ ((le_max_right _ _).trans hHH)
  have hPP₀ : P₀ ≤ P := ((le_max_left _ _).trans (le_max_left _ _)).trans hPP₂
  have hPP₁ : P₁ ≤ P := ((le_max_right _ _).trans (le_max_left _ _)).trans hPP₂
  have hP2 : 2 ≤ P := hP₀.trans hPP₀
  have hPr : (0 : ℝ) < P := by positivity
  have hHr : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have hTr : (T : ℝ) ≤ (4 * h + 1) * H := by
    have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast (by omega : 1 ≤ H)
    dsimp [T]
    push_cast
    nlinarith
  have hTP : (T : ℝ) / P ≤ 2 * K * (4 * h + 1) := by
    apply (div_le_iff₀ hPr).mpr
    nlinarith
  have hlogInv : (1 : ℝ) / Real.log P ^ 4 ≤ 16 / Real.log H ^ 4 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hpow := pow_le_pow_left₀ hlogH.le hlogratio 4
    nlinarith [hpow]
  have hT : 4 * P * h < T := by
    have hPH' : P ≤ H := by dsimp [P]; omega
    have hmul := Nat.mul_le_mul_left (4 * h) hPH'
    dsimp [T]
    nlinarith
  have h4 := hfourth P hPP₀ T h hh hT
  constructor
  · change (∑ t ∈ Finset.range T,
      ‖primeGraphMultiplier T h (PrimeEstimates.dyadicPrimes P) (t : ℤ)‖ ^ 4) ≤ C / Real.log H ^ 4
    calc
      _ ≤ A * T / ((P : ℝ) * Real.log P ^ 4) := h4
      _ = A * ((T : ℝ) / P) * (1 / Real.log P ^ 4) := by ring
      _ ≤ A * (2 * K * (4 * h + 1)) * (16 / Real.log H ^ 4) := by gcongr
      _ = C / Real.log H ^ 4 := by dsimp [C]; ring
  · intro t
    change ‖primeGraphMultiplier T h (PrimeEstimates.dyadicPrimes P) t‖ ≤ 16 / Real.log H
    have hp := hprime (2 * P) (by omega)
    have hlog2P : 0 < Real.log (2 * P : ℕ) := Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * P))
    have hlogle : Real.log (P : ℝ) ≤ Real.log (2 * P : ℕ) :=
      Real.log_le_log hPr (by exact_mod_cast (by omega : P ≤ 2 * P))
    calc
      _ ≤ (Nat.primeCounting (2 * P) : ℝ) / P :=
        norm_dyadic_primeGraphMultiplier_le_primeCounting T h (by omega) t
      _ ≤ (4 * (2 * P : ℕ) / Real.log (2 * P : ℕ)) / P :=
        div_le_div_of_nonneg_right (by simpa only [mul_div_assoc] using hp) hPr.le
      _ = 8 / Real.log (2 * P : ℕ) := by push_cast; field_simp; ring
      _ ≤ 8 / Real.log P := div_le_div_of_nonneg_left (by norm_num) hlogP hlogle
      _ ≤ 16 / Real.log H := by
        apply (div_le_div_iff₀ hlogP hlogH).mpr
        linarith

/-- Markov's inequality for the finite frequency count. -/
theorem card_primeGraphLargeFrequencies_le {T h : ℕ} (s : Finset ℕ)
    {θ B : ℝ} (hθ : 0 < θ)
    (hmoment : ∑ t ∈ Finset.range T, ‖primeGraphMultiplier T h s (t : ℤ)‖ ^ 4 ≤ B) :
    (primeGraphLargeFrequencies T h s θ).card ≤ B / θ ^ 4 := by
  have hsmall : (primeGraphLargeFrequencies T h s θ).card * θ ^ 4 ≤
      ∑ t ∈ primeGraphLargeFrequencies T h s θ, ‖primeGraphMultiplier T h s (t : ℤ)‖ ^ 4 := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro t ht
    exact pow_le_pow_left₀ hθ.le (Finset.mem_filter.mp ht).2 4
  have hsub : primeGraphLargeFrequencies T h s θ ⊆ Finset.range T := Finset.filter_subset _ _
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ ↦ by positivity :
    ∀ t ∈ Finset.range T, t ∉ primeGraphLargeFrequencies T h s θ →
      0 ≤ ‖primeGraphMultiplier T h s (t : ℤ)‖ ^ 4)
  exact (le_div_iff₀ (by positivity : 0 < θ ^ 4)).mpr ((hsmall.trans hsum).trans hmoment)

end

end Erdos67b
