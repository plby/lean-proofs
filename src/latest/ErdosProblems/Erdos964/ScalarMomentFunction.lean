import ErdosProblems.Erdos964.SelbergDimension
import BoundedGaps.Maynard.ReciprocalTotientCorrection

/-!
# Arithmetic functions for the scalar sieve moments

The numerator is the dimension, while both moments have local denominator
`p-3`. The support is squarefree and coprime to the fixed bad modulus.
-/

namespace Erdos964

open BoundedGaps.Maynard

noncomputable def scalarMomentAF (M k : ℕ) : ArithmeticFunction ℝ where
  toFun n := if Squarefree n ∧ n.Coprime M then
    ∏ p ∈ n.primeFactors, (k : ℝ) / ((p : ℝ) - 3) else 0
  map_zero' := by simp

theorem scalarMomentAF_apply (M k n : ℕ) :
    scalarMomentAF M k n = if Squarefree n ∧ n.Coprime M then
      ∏ p ∈ n.primeFactors, (k : ℝ) / ((p : ℝ) - 3) else 0 := rfl

theorem scalarMomentAF_multiplicative (M k : ℕ) :
    (scalarMomentAF M k).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [scalarMomentAF], ?_⟩
  intro m n hm hn hcop
  have hprod := (ArithmeticFunction.IsMultiplicative.prodPrimeFactors
    (fun p : ℕ => (k : ℝ) / ((p : ℝ) - 3))).map_mul_of_coprime hcop
  simp only [ArithmeticFunction.prodPrimeFactors_apply hm,
    ArithmeticFunction.prodPrimeFactors_apply hn,
    ArithmeticFunction.prodPrimeFactors_apply (mul_ne_zero hm hn)] at hprod
  simp only [scalarMomentAF_apply, Nat.squarefree_mul hcop, Nat.coprime_mul_iff_left]
  have hcond : ((Squarefree m ∧ Squarefree n) ∧ (m.Coprime M ∧ n.Coprime M)) ↔
      ((Squarefree m ∧ m.Coprime M) ∧ (Squarefree n ∧ n.Coprime M)) := by tauto
  simp only [hcond, hprod]
  by_cases hmc : Squarefree m ∧ m.Coprime M
  · by_cases hnc : Squarefree n ∧ n.Coprime M
    · rw [if_pos ⟨hmc, hnc⟩, if_pos hmc, if_pos hnc]
    · rw [if_neg (fun h => hnc h.2), if_neg hnc, mul_zero]
  · rw [if_neg (fun h => hmc h.1), if_neg hmc, zero_mul]

theorem scalarMomentAF_prime (M k : ℕ) {p : ℕ} (hp : p.Prime) :
    scalarMomentAF M k p = if p ∣ M then 0 else (k : ℝ) / ((p : ℝ) - 3) := by
  simp only [scalarMomentAF_apply, hp.squarefree, true_and, hp.coprime_iff_not_dvd,
    hp.primeFactors, Finset.prod_singleton]
  by_cases h : p ∣ M <;> simp [h]

theorem scalarMomentAF_prime_pow_ge_two (M k : ℕ) {p j : ℕ} (hp : p.Prime) (hj : 2 ≤ j) :
    scalarMomentAF M k (p ^ j) = 0 := by
  have hns : ¬Squarefree (p ^ j) := by
    intro hsq
    have hdiv : p * p ∣ p ^ j := by
      rw [← pow_two]
      exact pow_dvd_pow p hj
    have hunit := hsq p hdiv
    exact hp.not_isUnit hunit
  simp only [scalarMomentAF_apply, hns, false_and, ↓reduceIte]

theorem scalarMomentAF_three (M n : ℕ) :
    scalarMomentAF M 3 n =
      if Squarefree n ∧ n.Coprime M then dimensionSelbergWeight 3 n else 0 := by
  by_cases h : Squarefree n ∧ n.Coprime M
  · rw [scalarMomentAF_apply, if_pos h, if_pos h,
      dimensionSelbergWeight_apply 3 n h.1.ne_zero]
    norm_num only [Nat.cast_ofNat]
  · simp only [scalarMomentAF_apply, if_neg h]

theorem scalarMomentAF_two (M n : ℕ) :
    scalarMomentAF M 2 n =
      if Squarefree n ∧ n.Coprime M then semiprimeSelbergWeight 3 n else 0 := by
  by_cases h : Squarefree n ∧ n.Coprime M
  · rw [scalarMomentAF_apply, if_pos h, if_pos h, semiprimeSelbergWeight,
      ArithmeticFunction.prodPrimeFactors_apply h.1.ne_zero]
    norm_num only [Nat.cast_ofNat, show (3 : ℝ) - 1 = 2 by norm_num]
  · simp only [scalarMomentAF_apply, if_neg h]

noncomputable def scalarMomentCorrectionAF (M k : ℕ) : ArithmeticFunction ℝ :=
  scalarMomentAF M k * coprimeMobiusInvAF M ^ k

theorem scalarMomentCorrectionAF_multiplicative (M k : ℕ) :
    (scalarMomentCorrectionAF M k).IsMultiplicative :=
  (scalarMomentAF_multiplicative M k).mul (coprimeMobiusInvAF_isMultiplicative M).pow

theorem scalarMomentCorrectionAF_mul_harmonic_pow (M k : ℕ) :
    scalarMomentCorrectionAF M k * coprimeHarmonicAF M ^ k = scalarMomentAF M k := by
  unfold scalarMomentCorrectionAF
  rw [mul_assoc, ← mul_pow, coprimeMobiusInvAF_mul_coprimeHarmonicAF, one_pow, mul_one]

end Erdos964
