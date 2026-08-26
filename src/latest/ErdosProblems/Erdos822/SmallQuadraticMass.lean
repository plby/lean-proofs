/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.SharpBoundedMassProgressions
import ErdosProblems.Erdos822.RoughQuadraticPairClasses

/-! # Full prime-modulus savings in the small quadratic fibers -/

namespace Erdos822

open scoped BigOperators Classical
open Filter

theorem exists_eventually_small_primeResidueClasses_bound (C : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ N : ℕ in atTop, ∀ d a y : ℕ,
      0 < d → d ≤ N ^ 3 → primeDivisorReciprocalMass d ≤ C →
      (∑ r ∈ middlePrimeResidueClass N d a, (1 : ℝ) / r) ≤ B / d ∧
      (∑ q ∈ largePrimeResidueClass N d a y, (1 : ℝ) / q) ≤ B / d := by
  obtain ⟨B, hB, hbound⟩ := exists_eventually_boundedMass_prime_progression_mass C
  refine ⟨B, hB, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop 2] with N hbound hN
  intro d a y hd hdN hmass
  have hdN4 : d * N ≤ N ^ 4 := by
    calc
      _ ≤ N ^ 3 * N := Nat.mul_le_mul_right _ hdN
      _ = _ := by ring
  have hdN21 : d * N ≤ N ^ 21 := hdN4.trans
    (Nat.pow_le_pow_right (by omega : 1 ≤ N) (by omega : 4 ≤ 21))
  constructor
  · apply hbound _ (N ^ 4) d a hd hdN4 hmass
    intro r hr
    have hdata := mem_middlePrimeResidueClass_iff.mp hr
    have hrdata := mem_middlePrimes_iff.mp hdata.1
    have hrne : r ≠ N ^ 4 := by
      intro heq
      exact (Nat.Prime.not_prime_pow (by omega : 2 ≤ 4)) (heq ▸ hrdata.2.2)
    refine ⟨by omega, ?_, hrdata.2.2, hdata.2⟩
    simpa [show N * N ^ 4 = N ^ 5 by ring] using hrdata.2.1
  · apply hbound _ (N ^ 21) d a hd hdN21 hmass
    intro q hq
    have hdata := mem_largePrimeResidueClass_iff.mp hq
    have hqdata := mem_largePrimes_iff.mp hdata.1
    have hqne : q ≠ N ^ 21 := by
      intro heq
      exact (Nat.Prime.not_prime_pow (by omega : 2 ≤ 21)) (heq ▸ hqdata.2.2)
    refine ⟨by omega, ?_, hqdata.2.2, hdata.2.2⟩
    simpa [show N * N ^ 21 = N ^ 22 by ring] using hqdata.2.1

theorem exists_eventually_small_quadraticPairClasses_bound (C : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ N : ℕ in atTop, ∀ d u v y : ℕ,
      Squarefree d → d ≤ N ^ 3 → primeDivisorReciprocalMass d ≤ C →
      (∑ r ∈ quadraticMiddlePrimeClasses N d u v,
        ∑ q ∈ quadraticLargePrimeClasses N d u v y, (1 : ℝ) / (r * q : ℕ)) ≤
          B ^ 2 * (4 : ℝ) ^ d.primeFactors.card / (d : ℝ) ^ 2 := by
  obtain ⟨B, hB, hbound⟩ := exists_eventually_small_primeResidueClasses_bound C
  refine ⟨B, hB, ?_⟩
  filter_upwards [hbound] with N hbound
  intro d u v y hsq hdN hmass
  have hd : 0 < d := Nat.pos_of_ne_zero hsq.ne_zero
  have hcard : ((quadraticAssignmentResidues u v d).card : ℝ) ≤ (2 : ℝ) ^ d.primeFactors.card := by
    exact_mod_cast quadraticAssignmentResidues_card_le_two_pow hsq
  have hmiddle : (∑ r ∈ quadraticMiddlePrimeClasses N d u v, (1 : ℝ) / r) ≤
      (2 : ℝ) ^ d.primeFactors.card * (B / d) := by
    calc
      _ ≤ ∑ a ∈ quadraticAssignmentResidues u v d,
          ∑ r ∈ middlePrimeResidueClass N d a, (1 : ℝ) / r := by
        apply sum_biUnion_le_sum
        intro a ha r hr
        positivity
      _ ≤ ∑ _a ∈ quadraticAssignmentResidues u v d, B / d :=
        Finset.sum_le_sum fun a ha ↦ (hbound d a y hd hdN hmass).1
      _ = ((quadraticAssignmentResidues u v d).card : ℝ) * (B / d) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)
  have hlarge : (∑ q ∈ quadraticLargePrimeClasses N d u v y, (1 : ℝ) / q) ≤
      (2 : ℝ) ^ d.primeFactors.card * (B / d) := by
    calc
      _ ≤ ∑ a ∈ quadraticAssignmentResidues u v d,
          ∑ q ∈ largePrimeResidueClass N d a y, (1 : ℝ) / q := by
        apply sum_biUnion_le_sum
        intro a ha q hq
        positivity
      _ ≤ ∑ _a ∈ quadraticAssignmentResidues u v d, B / d :=
        Finset.sum_le_sum fun a ha ↦ (hbound d a y hd hdN hmass).2
      _ = ((quadraticAssignmentResidues u v d).card : ℝ) * (B / d) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)
  calc
    _ = (∑ r ∈ quadraticMiddlePrimeClasses N d u v, (1 : ℝ) / r) *
        (∑ q ∈ quadraticLargePrimeClasses N d u v y, (1 : ℝ) / q) := by
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro q hq
      push_cast
      ring
    _ ≤ ((2 : ℝ) ^ d.primeFactors.card * (B / d)) *
        ((2 : ℝ) ^ d.primeFactors.card * (B / d)) :=
      mul_le_mul hmiddle hlarge (by positivity) (by positivity)
    _ = B ^ 2 * ((2 : ℝ) ^ d.primeFactors.card) ^ 2 / (d : ℝ) ^ 2 := by ring
    _ = _ := by
      rw [← pow_mul, Nat.mul_comm d.primeFactors.card 2, pow_mul]
      norm_num

#print axioms exists_eventually_small_quadraticPairClasses_bound

end Erdos822
