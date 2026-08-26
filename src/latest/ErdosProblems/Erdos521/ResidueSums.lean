/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Partitioning centered finite sums by residue classes.
Formal proof: Codex.
-/
import Mathlib

namespace Erdos521

open MeasureTheory
open scoped BigOperators

theorem sum_residue_parts (m k : ℕ) (hm : 0 < m) (x : ℝ) :
    (∑ c ∈ Finset.range m, if k % m = c then x else 0) = x := by
  simp [Nat.mod_lt k hm]

theorem centered_residue_sum {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (m : ℕ) (hm : 0 < m) (S : Finset ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) :
    (∑ c ∈ Finset.range m, ∑ k ∈ S,
      ((if k % m = c then X k ω else 0) - ∫ z, (if k % m = c then X k z else 0) ∂μ)) =
      ∑ k ∈ S, (X k ω - ∫ z, X k z ∂μ) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  have hterm (c : ℕ) :
      (if k % m = c then X k ω else 0) - (∫ z, (if k % m = c then X k z else 0) ∂μ) =
        if k % m = c then X k ω - ∫ z, X k z ∂μ else 0 := by
    by_cases h : k % m = c <;> simp [h]
  simp_rw [hterm]
  exact sum_residue_parts m k hm _

end Erdos521
