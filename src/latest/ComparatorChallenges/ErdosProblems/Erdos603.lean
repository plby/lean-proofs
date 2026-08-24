/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos603

def IsErdos603Family {I X : Type u} (A : I → Set X) : Prop :=
  (∀ i, (A i).Countable ∧ (A i).Infinite) ∧
    ∀ i j, i ≠ j → (A i ∩ A j).encard ≠ 2

def UnionHasMonochromaticMember {I X : Type u} (A : I → Set X) (Color : Type u) : Prop :=
  ∀ coloring : (⋃ i, A i) → Color,
    ∃ (i : I) (k : Color), ∀ x (hx : x ∈ A i),
      coloring ⟨x, Set.mem_iUnion.2 ⟨i, hx⟩⟩ = k

theorem erdos_603 (C : Cardinal.{u}) :
    ∃ (I X : Type u) (A : I → Set X),
      IsErdos603Family A ∧ UnionHasMonochromaticMember A C.out := by
  sorry

end Erdos603
