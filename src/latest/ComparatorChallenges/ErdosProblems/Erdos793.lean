/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

open Filter
open scoped Topology

namespace Erdos793

/-- A finite set `A ⊆ ℕ` is *strongly 2-primitive* if, for every `a, b, c ∈ A`
with `a ≠ b` and `a ≠ c`, we have `a ∤ b * c`. -/
def Strongly2Primitive (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → a ≠ c → ¬ a ∣ b * c

/-- The extremal function: the maximal cardinality of a strongly 2-primitive
subset of `[n] = {1, …, n}`. -/
noncomputable def F (n : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 n).powerset.filter Strongly2Primitive).sup Finset.card

theorem erdos_793 :
    Tendsto
      (fun n : ℕ =>
        ((F n : ℝ) - Nat.primeCounting n) /
          ((n : ℝ) ^ ((2 : ℝ) / 3) / (Real.log n) ^ 2))
      atTop (𝓝 (27 / 2)) := by
  sorry

end Erdos793
