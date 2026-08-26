/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.B5SquarefreeMass

/-!
# Input size from reciprocal cofactor mass

The outer-prime lower bound is uniform on every subfamily of the odd raw
layer.  This file records the generic multiplication by reciprocal mass and
then applies it to the corrected B4/B5 family.
-/

namespace Erdos822

open scoped BigOperators

/-- Any odd-raw subfamily with c*log N reciprocal mass yields
(c/1200)*N^60 outer inputs. -/
theorem eventually_outerInputs_card_linear_of_log_mass
    {B : ℕ → Finset ℕ} {c : ℝ}
    (hc : 0 < c)
    (hB : ∀ N, B N ⊆ oddRawCofactors N)
    (hmass : ∀ᶠ N : ℕ in Filter.atTop,
      c * Real.log (N : ℝ) ≤
        ∑ m ∈ B N, (1 : ℝ) / m) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (c / 1200) * ((N ^ 60 : ℕ) : ℝ) ≤
        ((outerInputs (fun _ => B N) (N ^ 60)).card : ℝ) := by
  filter_upwards [hmass, eventually_outerPrimes_card_lower_raw,
      Filter.eventually_ge_atTop 2] with N hmassN houter hN
  have hsubset : B N ⊆ oddRawCofactors N := hB N
  have hpos : ∀ m ∈ B N, 0 < m := by
    intro m hm
    exact oddRawCofactors_pos (hsubset hm)
  have hlarge : ∀ m ∈ B N,
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
          (c * Real.log N) ≤
        ((N ^ 60 : ℕ) : ℝ) / (1200 * Real.log N) *
          ∑ m ∈ B N, (1 : ℝ) / m := by
    exact mul_le_mul_of_nonneg_left hmassN hfactor0
  have hsum :
      ∑ m ∈ B N,
          ((N ^ 60 : ℕ) : ℝ) /
            (1200 * (m : ℝ) * Real.log N) ≤
        ∑ m ∈ B N, ((outerPrimes (N ^ 60) m).card : ℝ) := by
    apply Finset.sum_le_sum
    intro m hm
    exact houter m
      (oddRawCofactors_subset_raw N (hsubset hm))
  have hleft :
      ∑ m ∈ B N,
          ((N ^ 60 : ℕ) : ℝ) /
            (1200 * (m : ℝ) * Real.log N) =
        ((N ^ 60 : ℕ) : ℝ) / (1200 * Real.log N) *
          ∑ m ∈ B N, (1 : ℝ) / m := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  have hcard :
      ((outerInputs (fun _ => B N) (N ^ 60)).card : ℝ) =
        ∑ m ∈ B N, ((outerPrimes (N ^ 60) m).card : ℝ) := by
    rw [outerInputs_card_eq_sum_outerPrimes_card
      (fun _ => B N) (N ^ 60) hpos hlarge]
    norm_cast
  calc
    (c / 1200) * ((N ^ 60 : ℕ) : ℝ) =
        ((N ^ 60 : ℕ) : ℝ) / (1200 * Real.log N) *
          (c * Real.log N) := by
      field_simp
    _ ≤ ((N ^ 60 : ℕ) : ℝ) / (1200 * Real.log N) *
          ∑ m ∈ B N, (1 : ℝ) / m := hmassmul
    _ = ∑ m ∈ B N,
          ((N ^ 60 : ℕ) : ℝ) /
            (1200 * (m : ℝ) * Real.log N) := hleft.symm
    _ ≤ ∑ m ∈ B N, ((outerPrimes (N ^ 60) m).card : ℝ) := hsum
    _ = ((outerInputs (fun _ => B N) (N ^ 60)).card : ℝ) :=
      hcard.symm

/-- The corrected squarefree B4/B5 family has linearly many outer inputs
at the perfect-power scale. -/
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
  let B : ℕ → Finset ℕ := fun N =>
    squarefreeB5GoodCofactors N (Nat.nthRoot (4 * S) N) C₀
  have hsubset : ∀ N, B N ⊆ oddRawCofactors N := by
    intro N m hm
    exact squarefreeLargeGcdFreeOddCofactors_subset_oddRaw N (N ^ 4)
      (squarefreeB5GoodCofactors_subset_squarefree N
        (Nat.nthRoot (4 * S) N) C₀ hm)
  have hmass' :
      ∀ᶠ N : ℕ in Filter.atTop,
        (1 / 16000 : ℝ) * Real.log (N : ℝ) ≤
          ∑ m ∈ B N, (1 : ℝ) / m := by
    simpa [B] using hmass
  have hsize := eventually_outerInputs_card_linear_of_log_mass
    (B := B) (c := (1 / 16000 : ℝ)) (by norm_num)
    hsubset hmass'
  norm_num at hsize ⊢
  simpa [B] using hsize

end Erdos822
