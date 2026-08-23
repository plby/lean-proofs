/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Set Function Cardinal Ordinal

noncomputable section


namespace Erdos603

open scoped Classical in
def IsErdos603Family {I X : Type u} (A : I → Set X) : Prop :=
  (∀ i, (A i).Countable ∧ (A i).Infinite) ∧
    ∀ i j, i ≠ j → (A i ∩ A j).encard ≠ 2

end Erdos603

namespace Erdos603

open scoped Classical in
def UnionHasMonochromaticMember {I X : Type u} (A : I → Set X) (Color : Type u) : Prop :=
  ∀ coloring : (⋃ i, A i) → Color,
    ∃ (i : I) (k : Color), ∀ x (hx : x ∈ A i),
      coloring ⟨x, Set.mem_iUnion.2 ⟨i, hx⟩⟩ = k

end Erdos603

namespace Erdos603

open scoped Classical in
theorem erdos_603 (C : Cardinal.{u}) :
    ∃ (I X : Type u) (A : I → Set X),
      IsErdos603Family A ∧ UnionHasMonochromaticMember A C.out := by
  sorry

end Erdos603

end
