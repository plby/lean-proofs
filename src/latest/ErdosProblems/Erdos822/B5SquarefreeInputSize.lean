/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.B5SquarefreeMass
import ErdosProblems.Erdos822.B5InputSize

/-!
# Linear input size after the corrected B4 and B5 filters

The family used in the collision argument must satisfy the corrected B4
coprimality and squarefreeness conditions, not merely B5.  The preceding
mass theorem shows that their intersection still has logarithmic reciprocal
mass.  The uniform outer-prime lower bound therefore gives a linear family
of actual inputs at the perfect-power scales.
-/

namespace Erdos822

open scoped BigOperators

/-- The squarefree-B4/B5 filtered odd outer-input family has linear size. -/
theorem exists_eventually_squarefreeB5OuterInputs_card_linear :
    ∃ S : ℕ, ∃ C₀ : ℝ, 101 ≤ S ∧ 0 < C₀ ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        let y := Nat.nthRoot (4 * S) N
        (1 / 19200000 : ℝ) * ((N ^ 60 : ℕ) : ℝ) ≤
          ((outerInputs
            (fun _ => squarefreeB5GoodCofactors N y C₀)
            (N ^ 60)).card : ℝ) := by
  obtain ⟨S, C₀, hS, hC₀, hmass⟩ :=
    exists_eventually_squarefreeB5Good_log_mass
  refine ⟨S, C₀, hS, hC₀, ?_⟩
  filter_upwards [hmass, eventually_outerPrimes_card_lower_raw,
      Filter.eventually_ge_atTop 2] with N hmassN houter hN
  dsimp only at hmassN ⊢
  let y := Nat.nthRoot (4 * S) N
  let B := squarefreeB5GoodCofactors N y C₀
  have hsubset : B ⊆ oddRawCofactors N := by
    intro m hm
    exact squarefreeLargeGcdFreeOddCofactors_subset_oddRaw N (N ^ 4)
      ((mem_squarefreeB5GoodCofactors_iff.mp hm).1)
  have hpos : ∀ m ∈ B, 0 < m := by
    intro m hm
    exact oddRawCofactors_pos (hsubset hm)
  have hlarge : ∀ m ∈ B,
      ∀ p ∈ outerPrimes (N ^ 60) m, m < p := by
    intro m hm p hp
    exact oddOuterPrime_large_of_mem hN (hsubset hm) hp
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hfactor0 :
      0 ≤ ((N ^ 60 : ℕ) : ℝ) / (1200 * Real.log N) := by
    positivity
  have hmassmul :
      ((N ^ 60 : ℕ) : ℝ) / (1200 * Real.log N) *
          ((1 / 16000 : ℝ) * Real.log N) ≤
        ((N ^ 60 : ℕ) : ℝ) / (1200 * Real.log N) *
          ∑ m ∈ B, (1 : ℝ) / m := by
    apply mul_le_mul_of_nonneg_left
    · simpa [B, y] using hmassN
    · exact hfactor0
  have hsum :
      ∑ m ∈ B,
          ((N ^ 60 : ℕ) : ℝ) /
            (1200 * (m : ℝ) * Real.log N) ≤
        ∑ m ∈ B, ((outerPrimes (N ^ 60) m).card : ℝ) := by
    apply Finset.sum_le_sum
    intro m hm
    exact houter m
      (oddRawCofactors_subset_raw N (hsubset hm))
  have hleft :
      ∑ m ∈ B,
          ((N ^ 60 : ℕ) : ℝ) /
            (1200 * (m : ℝ) * Real.log N) =
        ((N ^ 60 : ℕ) : ℝ) / (1200 * Real.log N) *
          ∑ m ∈ B, (1 : ℝ) / m := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  have hcard :
      ((outerInputs (fun _ => B) (N ^ 60)).card : ℝ) =
        ∑ m ∈ B, ((outerPrimes (N ^ 60) m).card : ℝ) := by
    rw [outerInputs_card_eq_sum_outerPrimes_card
      (fun _ => B) (N ^ 60) hpos hlarge]
    norm_cast
  calc
    (1 / 19200000 : ℝ) * ((N ^ 60 : ℕ) : ℝ) =
        ((N ^ 60 : ℕ) : ℝ) / (1200 * Real.log N) *
          ((1 / 16000 : ℝ) * Real.log N) := by
      field_simp
      ring
    _ ≤ ((N ^ 60 : ℕ) : ℝ) / (1200 * Real.log N) *
          ∑ m ∈ B, (1 : ℝ) / m := hmassmul
    _ = ∑ m ∈ B,
          ((N ^ 60 : ℕ) : ℝ) /
            (1200 * (m : ℝ) * Real.log N) := hleft.symm
    _ ≤ ∑ m ∈ B, ((outerPrimes (N ^ 60) m).card : ℝ) := hsum
    _ = ((outerInputs (fun _ => B) (N ^ 60)).card : ℝ) := hcard.symm

end Erdos822
