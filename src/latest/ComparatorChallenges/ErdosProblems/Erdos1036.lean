/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Harmonic.GeneralizeProofs

end GeneralizeProofs

end Harmonic

namespace Erdos1036

noncomputable def hom_num {V : Type*} (G : SimpleGraph V) : ℕ := max G.cliqueNum G.indepNum
def induced_iso_rel {V : Type*} (G : SimpleGraph V) (s t : Set V) : Prop :=
  Nonempty (G.induce s ≃g G.induce t)
open scoped Classical in
noncomputable def I_num {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : ℕ :=
  Fintype.card (Quotient (Setoid.mk (induced_iso_rel G) (by
  constructor;
  · intro x
    use Equiv.refl x
    simp
  · rintro x y ⟨ f, hf ⟩;
    refine ⟨ f.symm, ?_ ⟩;
    grind;
  · rintro x y z ⟨ f, hf ⟩ ⟨ g, hg ⟩;
    exact ⟨ f.trans g, by aesop ⟩)))

theorem erdos_1036 (c : ℝ) (hc : c > 0) :
  ∃ (ε : ℝ), ε > 0 ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj],
  Fintype.card V = n →
  (hom_num G : ℝ) ≤ c * Real.logb 2 n →
  (I_num G : ℝ) ≥ (2 : ℝ) ^ (ε * n) := by
  sorry

end Erdos1036
