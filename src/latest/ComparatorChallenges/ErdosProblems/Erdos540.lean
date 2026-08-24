/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos540

def hasZeroSum {G : Type*} [DecidableEq G] [AddCommMonoid G] (A : Finset G) : Prop :=
  ∃ S : Finset G, S ⊆ A ∧ S.Nonempty ∧ S.sum id = 0

theorem erdos_540 : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (_ : 0 < N) (A : Finset (ZMod N)),
    C * Real.sqrt N ≤ ↑A.card →
    hasZeroSum A := by
  sorry

end Erdos540
