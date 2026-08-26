import ErdosProblems.Erdos67b.MRGSA10TailoredNearMassScalar
import ErdosProblems.Erdos67b.PrimeEstimates

/-!
# Counting the two high-prime factors in the A.10 near term

After the alpha--beta exponential average, the prime--prime part of the
near mass is reduced to counting pairs of primes above the source cutoff.
This file records the elementary Chebyshev bound for that count.
-/

open scoped BigOperators
open Finset

namespace Erdos67b.MRHalaszBands

noncomputable section

open Erdos67b.PrimeEstimates

/-- Primes in the source window `(y,K]`. -/
def gsA10HighPrimes (y K : ℕ) : Finset ℕ :=
  (primesUpTo K).filter (fun p ↦ y < p)

@[simp] theorem mem_gsA10HighPrimes {y K p : ℕ} :
    p ∈ gsA10HighPrimes y K ↔ y < p ∧ p ≤ K ∧ p.Prime := by
  constructor
  · intro hp
    have hpdata := Finset.mem_filter.mp hp
    have hprime := mem_primesUpTo.mp hpdata.1
    exact ⟨hpdata.2, hprime.2, hprime.1⟩
  · rintro ⟨hpy, hpK, hpprime⟩
    exact Finset.mem_filter.mpr
      ⟨mem_primesUpTo.mpr ⟨hpprime, hpK⟩, hpy⟩

/-- Chebyshev gives the elementary `K / log y` upper bound for primes in
`(y,K]`. -/
theorem card_gsA10HighPrimes_le
    {y K : ℕ} (hy : 2 ≤ y) :
    ((gsA10HighPrimes y K).card : ℝ) ≤
      gsA10NearChebyshevConstant * K / Real.log (y : ℝ) := by
  have hyR : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos hyR
  have hweighted :
      ((gsA10HighPrimes y K).card : ℝ) * Real.log (y : ℝ) ≤
        ∑ p ∈ gsA10HighPrimes y K,
          ArithmeticFunction.vonMangoldt p := by
    calc
      ((gsA10HighPrimes y K).card : ℝ) * Real.log (y : ℝ) =
          ∑ p ∈ gsA10HighPrimes y K, Real.log (y : ℝ) := by
            simp
      _ ≤ ∑ p ∈ gsA10HighPrimes y K, Real.log (p : ℝ) := by
            apply Finset.sum_le_sum
            intro p hp
            have hpdata := mem_gsA10HighPrimes.mp hp
            exact Real.log_le_log (by positivity)
              (by exact_mod_cast (Nat.le_of_lt hpdata.1))
      _ = ∑ p ∈ gsA10HighPrimes y K,
          ArithmeticFunction.vonMangoldt p := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [ArithmeticFunction.vonMangoldt_apply_prime
              (mem_gsA10HighPrimes.mp hp).2.2]
  have hsubset : gsA10HighPrimes y K ⊆ Finset.Icc 1 K := by
    intro p hp
    have hpdata := mem_gsA10HighPrimes.mp hp
    exact Finset.mem_Icc.mpr ⟨hpdata.2.2.pos, hpdata.2.1⟩
  have hsum :
      (∑ p ∈ gsA10HighPrimes y K,
          ArithmeticFunction.vonMangoldt p) ≤
        gsA10NearChebyshevConstant * K := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun _ _ _ ↦ ArithmeticFunction.vonMangoldt_nonneg)).trans
        (sum_vonMangoldt_le_nearChebyshevConstant_mul K)
  apply (le_div_iff₀ hlogy).2
  simpa only [Nat.cast_ofNat] using hweighted.trans hsum

/-- The number of ordered high-prime pairs with product at most `2X` is
bounded by `X / log y` times the reciprocal-prime mass.  It is stated as a
sum of inner cardinalities, the form produced directly by the near-mass
hyperbola. -/
theorem sum_card_gsA10HighPrimes_div_le
    {y X : ℕ} (hy : 2 ≤ y) (hX : 0 < X) :
    (∑ b ∈ gsA10HighPrimes y (2 * X),
        ((gsA10HighPrimes y (2 * X / b)).card : ℝ)) ≤
      (gsA10NearChebyshevConstant * (2 * X : ℕ) /
          Real.log (y : ℝ)) * primeReciprocals (2 * X) := by
  have hyR : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos hyR
  have hfactor0 :
      0 ≤ gsA10NearChebyshevConstant * (2 * X : ℕ) /
        Real.log (y : ℝ) := by
    exact div_nonneg
      (mul_nonneg gsA10NearChebyshevConstant_nonneg (by positivity))
      hlogy.le
  calc
    (∑ b ∈ gsA10HighPrimes y (2 * X),
        ((gsA10HighPrimes y (2 * X / b)).card : ℝ)) ≤
      ∑ b ∈ gsA10HighPrimes y (2 * X),
        (gsA10NearChebyshevConstant * (2 * X : ℕ) /
          Real.log (y : ℝ)) * (b : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro b hb
        have hbpos : 0 < b := (mem_gsA10HighPrimes.mp hb).2.2.pos
        calc
          ((gsA10HighPrimes y (2 * X / b)).card : ℝ) ≤
              gsA10NearChebyshevConstant * (2 * X / b : ℕ) /
                Real.log (y : ℝ) := card_gsA10HighPrimes_le hy
          _ ≤ gsA10NearChebyshevConstant *
                ((2 * X : ℝ) / (b : ℝ)) / Real.log (y : ℝ) := by
              have hcast : (((2 * X / b : ℕ) : ℕ) : ℝ) ≤
                  (2 * X : ℝ) / (b : ℝ) := by
                simpa only [Nat.cast_mul, Nat.cast_ofNat] using
                  (Nat.cast_div_le (α := ℝ) (m := 2 * X) (n := b))
              exact div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left hcast
                  gsA10NearChebyshevConstant_nonneg) hlogy.le
          _ = (gsA10NearChebyshevConstant * (2 * X : ℕ) /
                Real.log (y : ℝ)) * (b : ℝ)⁻¹ := by
              rw [div_eq_mul_inv]
              push_cast
              ring
    _ = (gsA10NearChebyshevConstant * (2 * X : ℕ) /
          Real.log (y : ℝ)) *
        (∑ b ∈ gsA10HighPrimes y (2 * X), (b : ℝ)⁻¹) := by
          rw [Finset.mul_sum]
    _ ≤ (gsA10NearChebyshevConstant * (2 * X : ℕ) /
          Real.log (y : ℝ)) * primeReciprocals (2 * X) := by
      apply mul_le_mul_of_nonneg_left _ hfactor0
      rw [primeReciprocals_eq_primeHarmonic]
      unfold Erdos697.PrimeHarmonic.sum
      simp_rw [one_div]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have hpdata := mem_gsA10HighPrimes.mp hp
        exact Nat.mem_primesLE.mpr ⟨hpdata.2.1, hpdata.2.2⟩
      · intro p hp hnot
        exact inv_nonneg.mpr (by positivity)

end

end Erdos67b.MRHalaszBands

#print axioms Erdos67b.MRHalaszBands.sum_card_gsA10HighPrimes_div_le
