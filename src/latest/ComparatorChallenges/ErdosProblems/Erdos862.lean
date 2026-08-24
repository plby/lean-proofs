/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos862

def Sidon {α : Type} [AddCommMonoid α] (S : Set α) : Prop :=
  ∀ a b c d, a ∈ S → b ∈ S → c ∈ S → d ∈ S → a + b = c + d → ({a, b} : Set α) = {c, d}

def MaximalSidonSubset (U : Finset ℕ) (S : Finset ℕ) : Prop :=
  S ⊆ U ∧ Sidon (S : Set ℕ) ∧ ∀ S' : Finset ℕ, S' ⊆ U → Sidon (S' : Set ℕ) → S ⊆ S' → S = S'

open scoped Classical in
noncomputable def A1 (N : ℕ) : ℕ :=
  ((Finset.range N).powerset.filter (fun S => MaximalSidonSubset (Finset.range N) S)).card
noncomputable def eta : ℝ := 1 / 2 * Real.log (5 / 4)

theorem erdos_862 :
    ∀ c < eta, ∀ᶠ N : ℕ in Filter.atTop, Real.log (A1 N : ℝ) / Real.sqrt N ≥ c := by
  sorry

end Erdos862
