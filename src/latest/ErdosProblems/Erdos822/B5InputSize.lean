/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.B5GoodMass

/-!
# Linear input size after B5

The uniform outer-prime lower bound applies to every filtered cofactor
because the B5-good layer is a subset of the odd raw layer.  Multiplying
that bound by the retained reciprocal mass gives a linear number of outer
inputs at scale N^60.
-/

namespace Erdos822

open scoped BigOperators

/-- The B5-filtered odd outer-input family still has linear size. -/
theorem exists_eventually_massGoodOuterInputs_card_linear :
    ∃ S : ℕ, ∃ C₀ : ℝ, 101 ≤ S ∧ 0 < C₀ ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        let y := Nat.nthRoot (4 * S) N
        (1 / 4800000 : ℝ) * ((N ^ 60 : ℕ) : ℝ) ≤
          ((outerInputs
            (fun _ => massGoodOddCofactors N 2 y C₀)
            (N ^ 60)).card : ℝ) := by
  obtain ⟨S, C₀, hS, hC₀, hmass⟩ :=
    exists_eventually_massGoodOddCofactors_log_mass
  refine ⟨S, C₀, hS, hC₀, ?_⟩
  filter_upwards [hmass, eventually_outerPrimes_card_lower_raw,
      Filter.eventually_ge_atTop 2] with N hmassN houter hN
  dsimp only at hmassN ⊢
  let y := Nat.nthRoot (4 * S) N
  let B := massGoodOddCofactors N 2 y C₀
  have hsubset : B ⊆ oddRawCofactors N := by
    intro m hm
    exact (mem_massGoodOddCofactors_iff.mp hm).1
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
          ((1 / 4000 : ℝ) * Real.log N) ≤
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
    (1 / 4800000 : ℝ) * ((N ^ 60 : ℕ) : ℝ) =
        ((N ^ 60 : ℕ) : ℝ) / (1200 * Real.log N) *
          ((1 / 4000 : ℝ) * Real.log N) := by
      field_simp
      ring
    _ ≤ ((N ^ 60 : ℕ) : ℝ) / (1200 * Real.log N) *
          ∑ m ∈ B, (1 : ℝ) / m := hmassmul
    _ = ∑ m ∈ B,
          ((N ^ 60 : ℕ) : ℝ) /
            (1200 * (m : ℝ) * Real.log N) := hleft.symm
    _ ≤ ∑ m ∈ B, ((outerPrimes (N ^ 60) m).card : ℝ) := hsum
    _ = ((outerInputs (fun _ => B) (N ^ 60)).card : ℝ) :=
      hcard.symm

end Erdos822
