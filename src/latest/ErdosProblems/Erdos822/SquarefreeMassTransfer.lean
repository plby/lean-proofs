/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.PrimeSquareAverage

/-!
# Retaining reciprocal mass after the squarefree correction

For any cofactor family satisfying the B4 implication that a repeated large
prime in the shifted coefficient is absent from the cofactor itself, failure
of the large-squarefree shifted condition lies in the global prime-square
union already estimated.  This finite transfer is the interface used after
the B4 family has been constructed.
-/

namespace Erdos822

open scoped BigOperators

/-- Keep from B only cofactors whose shifted coefficient has no repeated
prime factor above y. -/
noncomputable def largeSquarefreeFilter
    (B : Finset ℕ) (y : ℕ) : Finset ℕ := by
  classical
  exact B.filter fun m =>
    ∀ p : ℕ, p.Prime → y < p → ¬ p ^ 2 ∣ shiftedTotient m

@[simp]
theorem mem_largeSquarefreeFilter_iff
    {B : Finset ℕ} {y m : ℕ} :
    m ∈ largeSquarefreeFilter B y ↔
      m ∈ B ∧
        ∀ p : ℕ, p.Prime → y < p →
          ¬ p ^ 2 ∣ shiftedTotient m := by
  simp [largeSquarefreeFilter]

theorem largeSquarefreeFilter_subset
    (B : Finset ℕ) (y : ℕ) :
    largeSquarefreeFilter B y ⊆ B := by
  intro m hm
  exact (mem_largeSquarefreeFilter_iff.mp hm).1

/-- Complementary part removed by the large-squarefree filter. -/
noncomputable def badLargeSquarefreeFilter
    (B : Finset ℕ) (y : ℕ) : Finset ℕ := by
  classical
  exact B.filter fun m => ¬
    ∀ p : ℕ, p.Prime → y < p →
      ¬ p ^ 2 ∣ shiftedTotient m

@[simp]
theorem mem_badLargeSquarefreeFilter_iff
    {B : Finset ℕ} {y m : ℕ} :
    m ∈ badLargeSquarefreeFilter B y ↔
      m ∈ B ∧ ¬
        ∀ p : ℕ, p.Prime → y < p →
          ¬ p ^ 2 ∣ shiftedTotient m := by
  simp [badLargeSquarefreeFilter]

/-- The complement of the squarefree filter inside a p-free family is
contained in the globally estimated prime-square bad union. -/
theorem bad_largeSquarefreeFilter_subset_largeSquareBad
    {N y : ℕ} {B : Finset ℕ}
    (hN : 1 ≤ N) (hB : B ⊆ oddRawCofactors N)
    (hfree : ∀ m ∈ B, ∀ p : ℕ, p.Prime → y < p →
      p ^ 2 ∣ shiftedTotient m → ¬ p ∣ m) :
    badLargeSquarefreeFilter B y ⊆
      largeSquareBadCoprimeOddCofactors N y := by
  classical
  intro m hm
  have hmData := mem_badLargeSquarefreeFilter_iff.mp hm
  push_neg at hmData
  obtain ⟨p, hp, hyp, hpsq⟩ := hmData.2
  rw [mem_largeSquareBadCoprimeOddCofactors_iff]
  refine ⟨p, ?_, ?_⟩
  · exact mem_largeSquarePrimes_of_sq_dvd_shifted hN
      (hB hmData.1) hp hyp hpsq
  · rw [mem_squareDivisibleCoprimeOddCofactors_iff]
    exact ⟨hB hmData.1, hpsq, hfree m hmData.1 p hp hyp hpsq⟩

/-- The reciprocal mass removed by the large-squarefree filter is bounded
by the global square-prime estimate. -/
theorem sum_inv_bad_largeSquarefreeFilter_le
    {N y : ℕ} {B : Finset ℕ}
    (hN : 2 ≤ N) (hy1 : 1 ≤ y) (hyN : y < N ^ 21)
    (hB : B ⊆ oddRawCofactors N)
    (hfree : ∀ m ∈ B, ∀ p : ℕ, p.Prime → y < p →
      p ^ 2 ∣ shiftedTotient m → ¬ p ∣ m) :
    (∑ m ∈ badLargeSquarefreeFilter B y,
        (1 : ℝ) / m) ≤
      (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
        (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
          ((((1 : ℝ) / y) +
              ((2 * N ^ 14 : ℕ) : ℝ) / (N ^ 21 : ℕ)) *
            (harmonic N : ℝ)) := by
  calc
    (∑ m ∈ badLargeSquarefreeFilter B y,
        (1 : ℝ) / m) ≤
        ∑ m ∈ largeSquareBadCoprimeOddCofactors N y,
          (1 : ℝ) / m := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (bad_largeSquarefreeFilter_subset_largeSquareBad
          (by omega) hB hfree)
      intro m hm hnot
      positivity
    _ ≤ (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
        (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
          ((((1 : ℝ) / y) +
              ((2 * N ^ 14 : ℕ) : ℝ) / (N ^ 21 : ℕ)) *
            (harmonic N : ℝ)) :=
      sum_inv_largeSquareBadCoprimeOddCofactors_le hN hy1 hyN

/-- Subtracting the square-prime bad mass gives a retained reciprocal-mass
lower bound for the corrected family. -/
theorem sum_inv_largeSquarefreeFilter_ge
    {N y : ℕ} {B : Finset ℕ} {R D : ℝ}
    (hN : 2 ≤ N) (hy1 : 1 ≤ y) (hyN : y < N ^ 21)
    (hB : B ⊆ oddRawCofactors N)
    (hfree : ∀ m ∈ B, ∀ p : ℕ, p.Prime → y < p →
      p ^ 2 ∣ shiftedTotient m → ¬ p ∣ m)
    (hraw : R ≤ ∑ m ∈ B, (1 : ℝ) / m)
    (hD :
      (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
        (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
          ((((1 : ℝ) / y) +
              ((2 * N ^ 14 : ℕ) : ℝ) / (N ^ 21 : ℕ)) *
            (harmonic N : ℝ)) ≤ D) :
    R - D ≤
      ∑ m ∈ largeSquarefreeFilter B y, (1 : ℝ) / m := by
  let good := largeSquarefreeFilter B y
  let bad := badLargeSquarefreeFilter B y
  have hpartition : B = good ∪ bad := by
    ext m
    simp only [good, bad, largeSquarefreeFilter,
      badLargeSquarefreeFilter, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hm
      by_cases hsq : ∀ p : ℕ, p.Prime → y < p →
          ¬ p ^ 2 ∣ shiftedTotient m
      · exact Or.inl ⟨hm, hsq⟩
      · exact Or.inr ⟨hm, hsq⟩
    · rintro (⟨hm, _⟩ | ⟨hm, _⟩) <;> exact hm
  have hdisj : Disjoint good bad := by
    rw [Finset.disjoint_left]
    intro m hmg hmb
    have hg := (mem_largeSquarefreeFilter_iff.mp hmg).2
    have hb := (mem_badLargeSquarefreeFilter_iff.mp hmb).2
    exact hb hg
  have hbad : ∑ m ∈ bad, (1 : ℝ) / m ≤ D := by
    calc
      ∑ m ∈ bad, (1 : ℝ) / m ≤
          (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
            (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
              ((((1 : ℝ) / y) +
                  ((2 * N ^ 14 : ℕ) : ℝ) / (N ^ 21 : ℕ)) *
                (harmonic N : ℝ)) := by
        dsimp [bad]
        exact sum_inv_bad_largeSquarefreeFilter_le
          hN hy1 hyN hB hfree
      _ ≤ D := hD
  have htotal :
      ∑ m ∈ B, (1 : ℝ) / m =
        ∑ m ∈ good, (1 : ℝ) / m +
          ∑ m ∈ bad, (1 : ℝ) / m := by
    rw [hpartition, Finset.sum_union hdisj]
  dsimp [good] at htotal ⊢
  linarith

end Erdos822
