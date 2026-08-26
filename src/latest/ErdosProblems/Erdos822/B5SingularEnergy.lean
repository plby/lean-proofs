/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.B5SingularWeight

/-!
# Energy assembly from a B5 singular-weight average

This is the exact finite shell around the remaining global arithmetic
average.  Empty fibers cost zero; nonempty fibers use the sharper B5
singular majorant, and the beta-sieve remainder is summed by the already
checked root-cutoff estimate.
-/

namespace Erdos822

open scoped BigOperators

/-- A linear B5 singular-weight sum gives linear collision energy on the
corresponding filtered odd outer-input family. -/
theorem exists_filteredOdd_collisionEnergy_le_of_b5SingularSum :
    ∃ A C : ℝ, 1 ≤ A ∧ 0 < C ∧
      ∀ C₀ : ℝ, ∀ N S K : ℕ, ∀ B : Finset ℕ,
        0 ≤ C₀ →
        B ⊆ massGoodOddCofactors N 2 (Nat.nthRoot (4 * S) N) C₀ →
        2 ≤ N → 0 < S → 101 ≤ S →
        let y := Nat.nthRoot (4 * S) N
        2 ≤ y →
        Real.log A ≤ 4 * (S - 100 : ℕ) / 99 →
        (∑ m ∈ B,
            ∑ m' ∈ B.erase m,
              b5SingularMainWeight A C C₀
                (N ^ 60) m m' 2 y S) ≤
          K * ((N ^ 60 : ℕ) : ℝ) →
        (collisionEnergy
          (outerInputs (fun _ => B) (N ^ 60))
          shiftedTotient : ℝ) ≤
          (K + 6) * ((N ^ 60 : ℕ) : ℝ) := by
  obtain ⟨A, C, hA, hC, hpoint⟩ :=
    exists_outerCollisionPairs_le_b5SingularWeight_of_massGood
  refine ⟨A, C, hA, hC, ?_⟩
  intro C₀ N S K B hC₀ hB hN hS hS101
  dsimp only
  intro hyTwo hlog hmain
  let y := Nat.nthRoot (4 * S) N
  have hy2 : 2 ≤ y := by simpa [y] using hyTwo
  have hBraw : B ⊆ oddRawCofactors N := by
    intro m hm
    exact (mem_massGoodOddCofactors_iff.mp (hB hm)).1
  have hpos : ∀ m ∈ B, 0 < m := by
    intro m hm
    exact oddRawCofactors_pos (hBraw hm)
  have hlarge : ∀ m ∈ B,
      ∀ p ∈ outerPrimes (N ^ 60) m, m < p := by
    intro m hm p hp
    exact oddOuterPrime_large_of_mem hN (hBraw hm) hp
  have hylarge : ∀ m ∈ B,
      ∀ p ∈ outerPrimes (N ^ 60) m, y < p := by
    intro m hm p hp
    dsimp [y]
    exact oddOuterPrime_gt_slowSieveCutoff hN hS (hBraw hm) hp
  let G : ℕ → ℕ → ℝ := fun m m' =>
    b5SingularMainWeight A C C₀ (N ^ 60) m m' 2 y S +
      (((y ^ S : ℕ) : ℝ) ^ 2)
  have hG : ∀ m ∈ B,
      ∀ m' ∈ B.erase m,
      ((outerCollisionPairs (N ^ 60) m m').card : ℝ) ≤ G m m' := by
    intro m hm m' hm'
    have hm'B := (Finset.mem_erase.mp hm').2
    by_cases hne : (outerCollisionPairs (N ^ 60) m m').Nonempty
    · dsimp [G]
      exact hpoint C₀ (N ^ 60) m m' 2 y S hC₀
        (hpos m hm) (hpos m' hm'B)
        (hlarge m hm) (hlarge m' hm'B)
        (hylarge m hm) (hylarge m' hm'B)
        (by norm_num) (by omega) (by omega) hS101 hlog
        (mem_massGoodOddCofactors_iff.mp (hB hm)).2
        (mem_massGoodOddCofactors_iff.mp (hB hm'B)).2 hne
    · have hempty : outerCollisionPairs (N ^ 60) m m' = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hne
      rw [hempty]
      simp only [Finset.card_empty, Nat.cast_zero]
      dsimp [G]
      exact add_nonneg
        (b5SingularMainWeight_nonneg A C C₀ (N ^ 60) m m' 2 y S
          (le_trans (by norm_num) hA))
        (sq_nonneg _)
  have herrRaw :
      (∑ m ∈ oddRawCofactors N,
          ∑ m' ∈ (oddRawCofactors N).erase m,
            (((y ^ S : ℕ) : ℝ) ^ 2)) ≤
        4 * ((N ^ 60 : ℕ) : ℝ) := by
    simpa [y] using sum_oddRaw_slowSieveCutoff_error_sq_le N S
      (by omega) hS
  have herr :
      (∑ m ∈ B,
          ∑ m' ∈ B.erase m,
            (((y ^ S : ℕ) : ℝ) ^ 2)) ≤
        4 * ((N ^ 60 : ℕ) : ℝ) := by
    calc
      (∑ m ∈ B,
          ∑ m' ∈ B.erase m,
            (((y ^ S : ℕ) : ℝ) ^ 2)) ≤
          ∑ m ∈ B,
            ∑ m' ∈ (oddRawCofactors N).erase m,
              (((y ^ S : ℕ) : ℝ) ^ 2) := by
        apply Finset.sum_le_sum
        intro m hm
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.erase_subset_erase m hBraw)
        intro m' hm' hnot
        positivity
      _ ≤ ∑ m ∈ oddRawCofactors N,
            ∑ m' ∈ (oddRawCofactors N).erase m,
              (((y ^ S : ℕ) : ℝ) ^ 2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hBraw
        intro m hm hnot
        positivity
      _ ≤ 4 * ((N ^ 60 : ℕ) : ℝ) := herrRaw
  have hsum :
      (∑ m ∈ B,
          ∑ m' ∈ B.erase m, G m m') ≤
        (K + 4) * ((N ^ 60 : ℕ) : ℝ) := by
    dsimp [G]
    simp_rw [Finset.sum_add_distrib]
    calc
      (∑ m ∈ B,
          ∑ m' ∈ B.erase m,
              b5SingularMainWeight A C C₀
                (N ^ 60) m m' 2 y S) +
          ∑ m ∈ B,
            ∑ m' ∈ B.erase m,
              (((y ^ S : ℕ) : ℝ) ^ 2) ≤
          K * ((N ^ 60 : ℕ) : ℝ) +
            4 * ((N ^ 60 : ℕ) : ℝ) :=
        add_le_add hmain herr
      _ = (K + 4) * ((N ^ 60 : ℕ) : ℝ) := by
        push_cast
        ring
  have henergy :=
    collisionEnergy_outerInputs_cast_le_of_sum_majorant
      (fun _ => B) (N ^ 60) G (K + 4)
      (by
        have : 1 ≤ N ^ 60 := one_le_pow₀ (by omega)
        exact this)
      hpos hlarge hG hsum
  convert henergy using 1 <;> push_cast <;> ring

end Erdos822
