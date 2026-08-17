/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib
import UnitFractions.Definitions

/-!
# Erdős Problem 297: finite counting infrastructure

This file defines the exact finite counting function in the problem.  All
reciprocal sums are taken in `ℚ`; consequently the predicate being counted is
literal equality of rational numbers, with no analytic tolerance.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos297

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The available denominators `1, …, N`. -/
def denominators (N : ℕ) : Finset ℕ := Icc 1 N

/-- The family of subsets of `1, …, N` whose reciprocal sum is exactly one. -/
def representations (N : ℕ) : Finset (Finset ℕ) :=
  (denominators N).powerset.filter fun A ↦ UnitFractions.rec_sum A = 1

/-- The exact counting function in Erdős Problem 297. -/
def count (N : ℕ) : ℕ := (representations N).card

@[simp] theorem mem_denominators {N n : ℕ} :
    n ∈ denominators N ↔ 1 ≤ n ∧ n ≤ N := by
  simp [denominators]

@[simp] theorem mem_representations {N : ℕ} {A : Finset ℕ} :
    A ∈ representations N ↔
      A ⊆ denominators N ∧ UnitFractions.rec_sum A = 1 := by
  simp [representations]

theorem count_eq_card_filter (N : ℕ) :
    count N =
      ((Icc 1 N : Finset ℕ).powerset.filter fun A : Finset ℕ ↦
        (∑ n ∈ A, (1 : ℚ) / (n : ℚ)) = 1).card := by
  simp [count, representations, denominators, UnitFractions.rec_sum]

/-- There is always at least one representation: `{1}`. -/
theorem singleton_one_mem_representations {N : ℕ} (hN : 1 ≤ N) :
    {1} ∈ representations N := by
  rw [mem_representations]
  constructor
  · intro n hn
    simp only [Finset.mem_singleton] at hn
    subst n
    exact mem_denominators.mpr ⟨by omega, hN⟩
  · simp [UnitFractions.rec_sum]

theorem count_pos {N : ℕ} (hN : 1 ≤ N) : 0 < count N := by
  rw [count, Finset.card_pos]
  exact ⟨{1}, singleton_one_mem_representations hN⟩

theorem count_le_two_pow (N : ℕ) : count N ≤ 2 ^ N := by
  calc
    count N ≤ ((denominators N).powerset).card := by
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = 2 ^ (denominators N).card := Finset.card_powerset _
    _ = 2 ^ N := by simp [denominators]

/-- The normalized logarithm whose limit is the sharp exponent. -/
def logGrowth (N : ℕ) : ℝ := Real.log (count N : ℝ) / N

end

end Erdos297

#print axioms Erdos297.count_pos
#print axioms Erdos297.count_le_two_pow
