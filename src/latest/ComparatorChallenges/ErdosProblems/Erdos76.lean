/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Finset

namespace Erdos76

/-- Distinct selected triangles share at most one vertex. -/
def EdgeDisjoint {α : Type*} [DecidableEq α]
    (P : Finset (Finset α)) : Prop :=
  ∀ ⦃s⦄, s ∈ P → ∀ ⦃t⦄, t ∈ P → s ≠ t → #(s ∩ t) ≤ 1

/-- Asymptotically sharp integral monochromatic triangle packing. -/
theorem erdos_76 :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ G : SimpleGraph (Fin n), ∃ P : Finset (Finset (Fin n)),
        (∀ t ∈ P, G.IsNClique 3 t ∨ Gᶜ.IsNClique 3 t) ∧
        EdgeDisjoint P ∧ (1 - ε) * (n : ℝ) ^ 2 / 12 ≤ (P.card : ℝ) := by
  sorry

end Erdos76
