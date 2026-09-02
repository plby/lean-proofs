import ErdosProblems.Erdos327.Analytic.FactorCounts
import ErdosProblems.Erdos327.Analytic.ThreeFormBoxBounds

/-!
# Pointwise bridges to the three-form box weights

The analytic coordinate arguments naturally produce multiplicity weights.
The finite CRT sieve uses squarefree divisibility weights over odd primes.
This file proves the required pointwise comparisons, including the support
conditions below the roughness cutoff.
-/

namespace Erdos327.Analytic

open Finset
open scoped ArithmeticFunction.Omega BigOperators

noncomputable section

theorem oddPrimesUpTo_eq_primesBetween_three (z : ℕ) :
    oddPrimesUpTo z = primesBetween 3 z := by
  ext p
  simp only [mem_oddPrimesUpTo, mem_primesBetween]
  constructor
  · rintro ⟨hp, hpz, hp2⟩
    have hpTwoLe := hp.two_le
    exact ⟨by omega, hpz, hp⟩
  · rintro ⟨hp3, hpz, hp⟩
    exact ⟨hp, hpz, by omega⟩

/-- On odd-rough first and third forms, the source parameters below `L`
never meet a divisor.  The source squarefree weight is therefore the
constant `(1/2,1/2,1/4)` weight on all odd primes. -/
theorem sourceIntegerWeight_eq_const_of_oddRough
    {L z u v : ℕ}
    (hu : OddRough L u) (hsum : OddRough L (u + v)) :
    centeredIntegerWeight (oddPrimesUpTo z)
        (sourceQU L) (sourceQV L) (sourceQSum L) u v =
      centeredIntegerWeight (oddPrimesUpTo z)
        (fun _ ↦ (1 / 2 : ℝ)) (fun _ ↦ (1 / 2 : ℝ))
        (fun _ ↦ (1 / 4 : ℝ)) u v := by
  unfold centeredIntegerWeight
  apply prod_congr rfl
  intro p hp
  have hpData := mem_oddPrimesUpTo.mp hp
  have hp2 : 2 < p := by
    have hpTwoLe := hpData.1.two_le
    omega
  by_cases hpL : p < L
  · have hpu : ¬p ∣ u := hu p hpData.1 hp2 hpL
    have hpsum : ¬p ∣ u + v := hsum p hpData.1 hp2 hpL
    simp [sourceQV, hpu, hpsum]
  · simp [sourceQU, sourceQV, sourceQSum, hpL]

/-- Full source multiplicity weights are pointwise bounded by the finite
source squarefree weight. -/
theorem sourceMultiplicityWeight_le_integerWeight
    {L z u v : ℕ}
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hsum0 : u + v ≠ 0)
    (hu : OddRough L u) (hsum : OddRough L (u + v)) :
    (1 / 2 : ℝ) ^ ArithmeticFunction.cardFactors u *
        (1 / 2 : ℝ) ^ ArithmeticFunction.cardFactors v *
        (1 / 4 : ℝ) ^ ArithmeticFunction.cardFactors (u + v) ≤
      centeredIntegerWeight (oddPrimesUpTo z)
        (sourceQU L) (sourceQV L) (sourceQSum L) u v := by
  have hU :=
    pow_cardFactors_le_pow_primeFactorCountBetween
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) 3 z u
  have hV :=
    pow_cardFactors_le_pow_primeFactorCountBetween
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) 3 z v
  have hSum :=
    pow_cardFactors_le_pow_primeFactorCountBetween
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) ≤ 1) 3 z (u + v)
  have hlocalized :=
    centeredMultiplicityWeight_le_integerWeight
      (L := 3) (X := z) hu0 hv0 hsum0
      (qU := (1 / 2 : ℝ)) (qV := (1 / 2 : ℝ))
      (qSum := (1 / 4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  calc
    (1 / 2 : ℝ) ^ ArithmeticFunction.cardFactors u *
          (1 / 2 : ℝ) ^ ArithmeticFunction.cardFactors v *
          (1 / 4 : ℝ) ^ ArithmeticFunction.cardFactors (u + v)
        ≤ (1 / 2 : ℝ) ^ primeFactorCountBetween 3 z u *
          (1 / 2 : ℝ) ^ primeFactorCountBetween 3 z v *
          (1 / 4 : ℝ) ^ primeFactorCountBetween 3 z (u + v) := by
      exact mul_le_mul
        (mul_le_mul hU hV (by positivity) (by positivity))
        hSum (by positivity) (by positivity)
    _ ≤ centeredIntegerWeight (primesBetween 3 z)
          (fun _ ↦ (1 / 2 : ℝ)) (fun _ ↦ (1 / 2 : ℝ))
          (fun _ ↦ (1 / 4 : ℝ)) u v :=
      hlocalized
    _ = centeredIntegerWeight (oddPrimesUpTo z)
          (fun _ ↦ (1 / 2 : ℝ)) (fun _ ↦ (1 / 2 : ℝ))
          (fun _ ↦ (1 / 4 : ℝ)) u v := by
      rw [oddPrimesUpTo_eq_primesBetween_three]
    _ = centeredIntegerWeight (oddPrimesUpTo z)
          (sourceQU L) (sourceQV L) (sourceQSum L) u v :=
      (sourceIntegerWeight_eq_const_of_oddRough hu hsum).symm

/-- The interval prime set is contained in the odd-prime set as soon as
the lower cutoff is at least three. -/
theorem primesBetween_subset_oddPrimesUpTo
    {L z : ℕ} (hL : 3 ≤ L) :
    primesBetween L z ⊆ oddPrimesUpTo z := by
  intro p hp
  have hpData := mem_primesBetween.mp hp
  exact mem_oddPrimesUpTo.mpr
    ⟨hpData.2.2, hpData.2.1, by omega⟩

/-- On rough first and third forms, adjoining odd primes below `L` leaves
the mixed integer weight unchanged. -/
theorem mixedIntegerWeight_eq_primesBetween_of_rough
    {L z u w : ℕ} {alpha beta s : ℝ}
    (hL : 3 ≤ L)
    (hu : Rough L u) (hlin : Rough L (2 * u + w)) :
    crossIntegerWeight (oddPrimesUpTo z)
        (mixedQU L alpha) (mixedQW L beta)
        (mixedQLinear L s) u w =
      crossIntegerWeight (primesBetween L z)
        (fun _ ↦ alpha) (fun _ ↦ beta) (fun _ ↦ s) u w := by
  let f : ℕ → ℝ := fun p ↦
    (if p ∣ u then mixedQU L alpha p else 1) *
      (if p ∣ w then mixedQW L beta p else 1) *
      (if p ∣ 2 * u + w then mixedQLinear L s p else 1)
  let g : ℕ → ℝ := fun p ↦
    (if p ∣ u then alpha else 1) *
      (if p ∣ w then beta else 1) *
      (if p ∣ 2 * u + w then s else 1)
  have hsubset :
      primesBetween L z ⊆ oddPrimesUpTo z :=
    primesBetween_subset_oddPrimesUpTo hL
  have hextra :
      ∀ p ∈ oddPrimesUpTo z, p ∉ primesBetween L z → f p = 1 := by
    intro p hpOdd hpNot
    have hpData := mem_oddPrimesUpTo.mp hpOdd
    have hpL : p < L := by
      by_contra hnot
      exact hpNot (mem_primesBetween.mpr
        ⟨Nat.le_of_not_gt hnot, hpData.2.1, hpData.1⟩)
    have hpu : ¬p ∣ u := hu p hpData.1 hpL
    have hplin : ¬p ∣ 2 * u + w := hlin p hpData.1 hpL
    simp [f, mixedQU, mixedQW, mixedQLinear, hpL, hpu, hplin]
  have hon :
      ∀ p ∈ primesBetween L z, f p = g p := by
    intro p hp
    have hpL := (mem_primesBetween.mp hp).1
    simp [f, g, mixedQU, mixedQW, mixedQLinear,
      Nat.not_lt_of_ge hpL]
  unfold crossIntegerWeight
  change (∏ p ∈ oddPrimesUpTo z, f p) =
    ∏ p ∈ primesBetween L z, g p
  rw [← prod_subset hsubset hextra]
  exact prod_congr rfl hon

/-- The mixed multiplicity weight localized at `[L,z]` is pointwise
bounded by the finite mixed squarefree weight on all odd primes. -/
theorem mixedMultiplicityWeight_le_oddIntegerWeight
    {L z u w : ℕ} {alpha beta s : ℝ}
    (hL : 3 ≤ L)
    (hu0 : u ≠ 0) (hw0 : w ≠ 0) (hlin0 : 2 * u + w ≠ 0)
    (hu : Rough L u) (hlin : Rough L (2 * u + w))
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    alpha ^ primeFactorCountBetween L z u *
        beta ^ primeFactorCountBetween L z w *
        s ^ primeFactorCountBetween L z (2 * u + w) ≤
      crossIntegerWeight (oddPrimesUpTo z)
        (mixedQU L alpha) (mixedQW L beta)
        (mixedQLinear L s) u w := by
  have hbase :=
    crossMultiplicityWeight_le_integerWeight
      (L := L) (X := z) hu0 hw0 hlin0
      ha0 ha1 hb0 hb1 hs0 hs1
  calc
    alpha ^ primeFactorCountBetween L z u *
          beta ^ primeFactorCountBetween L z w *
          s ^ primeFactorCountBetween L z (2 * u + w) ≤
        crossIntegerWeight (primesBetween L z)
          (fun _ ↦ alpha) (fun _ ↦ beta) (fun _ ↦ s) u w :=
      hbase
    _ = crossIntegerWeight (oddPrimesUpTo z)
          (mixedQU L alpha) (mixedQW L beta)
          (mixedQLinear L s) u w :=
      (mixedIntegerWeight_eq_primesBetween_of_rough hL hu hlin).symm

end

end Erdos327.Analytic
