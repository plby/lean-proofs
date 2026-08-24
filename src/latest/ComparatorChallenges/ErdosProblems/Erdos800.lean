/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos800

universe u v

/-- The host graph contains an ordinary (not necessarily induced) copy of the target. -/
abbrev HasCopy {α : Type u} {β : Type v}
    (H : SimpleGraph α) (G : SimpleGraph β) : Prop := SimpleGraph.IsContained H G

/-- Every red/blue colouring of `K_N` has a monochromatic copy of `H`. -/
def RamseyFor {α : Type u} (H : SimpleGraph α) (N : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N), HasCopy H G ∨ HasCopy H Gᶜ

/-- The hypothesis in Problem 800: no edge has two endpoints of degree at least three. -/
def NoAdjacentHighDegree {α : Type u} [Fintype α]
    (H : SimpleGraph α) : Prop := by
  classical
  exact ∀ ⦃x y : α⦄, H.Adj x y → H.degree x < 3 ∨ H.degree y < 3

/-- A clique containing at least as many vertices as the target contains a copy
of the target. -/

theorem erdos_800 (n : ℕ) (H : SimpleGraph (Fin n))
    (hH : NoAdjacentHighDegree H) : RamseyFor H (12 * n) := by
  sorry

end Erdos800
