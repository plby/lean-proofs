/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open EuclideanGeometry

scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

namespace Set

variable {α : Type*} {r : α → α → α → Prop} {s t : Set α} {x y z : α}

protected def Triplewise (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s →
    x ≠ y → y ≠ z → x ≠ z → r x y z
end Set

def NonTrilinear (A : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  A.Triplewise (fun x y z ↦ ¬ Collinear ℝ {x, y, z})

namespace Erdos846

section Prelims

def NonTrilinearFor (A : Set ℝ²) (ε : ℝ) : Prop :=
  ∀ (B : Finset ℝ²), (B : Set ℝ²) ⊆ A → ∃ C ⊆ B,
    ε * B.card ≤ C.card ∧ NonTrilinear (C : Set ℝ²)

def WeaklyNonTrilinear (A : Set ℝ²) : Prop :=
  ∃ B : Finset (Set ℝ²), A = sSup B ∧ ∀ b ∈ B, NonTrilinear b
end Prelims

theorem not_erdos_846 :
    ¬ (∀ᵉ (A : Set ℝ²) (ε > 0),
        A.Infinite → NonTrilinearFor A ε → WeaklyNonTrilinear A) := by
  sorry

end Erdos846
