/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Nat Filter Topology

/-!
# Erdős Problem 1064

The density-one inequality `φ (n - φ n) + f n < φ n` holds for every
natural-valued `o(n)` error term `f`.
-/

namespace Set

@[inline]
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

end Set

namespace Erdos1064

theorem erdos_1064.variants.erdos_1064 (f : ℕ → ℕ)
    (hf : (fun n ↦ (f n : ℝ)) =o[atTop] (fun n ↦ (n : ℝ))) :
    {n : ℕ | φ (n - φ n) + f n < φ n}.HasDensity 1 := by
  sorry
