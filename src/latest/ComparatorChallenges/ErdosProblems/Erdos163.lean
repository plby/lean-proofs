import Mathlib

open Finset

namespace Erdos163

universe u v

/-- Every nonempty induced vertex set contains a vertex of degree at most `d`. -/
def IsDegenerateAtMost {α : Type u} [Fintype α]
    (H : SimpleGraph α) (d : ℕ) : Prop := by
  classical
  exact ∀ S : Finset α, S.Nonempty →
    ∃ x ∈ S, (S.filter fun y => H.Adj x y).card ≤ d

/-- An injective graph homomorphism; nonedges need not be preserved. -/
structure CopyEmbedding {α : Type u} {β : Type v}
    (H : SimpleGraph α) (G : SimpleGraph β) where
  toFun : α → β
  injective' : Function.Injective toFun
  map_adj' : ∀ ⦃x y : α⦄, H.Adj x y → G.Adj (toFun x) (toFun y)

/-- The host contains an ordinary copy of the target. -/
def HasCopy {α : Type u} {β : Type v}
    (H : SimpleGraph α) (G : SimpleGraph β) : Prop :=
  Nonempty (CopyEmbedding H G)

/-- Every red/blue coloring contains a monochromatic copy of `H`. -/
def RamseyFor {α : Type u} (H : SimpleGraph α) (N : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N), HasCopy H G ∨ HasCopy H Gᶜ

/-- The Burr--Erdős conjecture: bounded-degeneracy graphs have linear Ramsey number. -/
theorem erdos_163 :
    ∀ d : ℕ, 1 ≤ d →
      ∃ C : ℕ, 1 ≤ C ∧
        ∀ n : ℕ, ∀ H : SimpleGraph (Fin n),
          IsDegenerateAtMost H d → RamseyFor H (C * n) := by
  sorry

end Erdos163
