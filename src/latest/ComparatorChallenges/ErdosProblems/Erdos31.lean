/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped Pointwise Topology

namespace Erdos31

section

variable {β : Type*} [Preorder β]

variable (S : Set β) (a b : β)

abbrev Set.interIio (S : Set β) (b : β) : Set β :=
  S ∩ Set.Iio b
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  (Set.interIio (S ∩ A) b).ncard / (Set.interIio A b).ncard

def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Filter.Tendsto (fun (b : β) => partialDensity S A b) Filter.atTop (𝓝 α)
end

theorem erdos_31 (A : Set ℕ) (hA : A.Infinite) :
    ∃ B : Set ℕ, HasDensity B 0 ∧
      ∃ n0 : ℕ, ∀ n ≥ n0, n ∈ A + B := by
  sorry

end Erdos31
