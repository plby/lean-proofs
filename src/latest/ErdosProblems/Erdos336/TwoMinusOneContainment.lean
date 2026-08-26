import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- If `x` is not in `2B-B`, then the translate `x+B` and `2B` are
disjoint subsets of `2A`. -/
theorem card_add_card_double_le_of_not_mem_two_sub
    {A B : Finset G} (hBA : B ⊆ A) {x : G} (hxA : x ∈ A)
    (hx : x ∉ (B + B) - B) :
    B.card + (B + B).card ≤ (A + A).card := by
  have hdis : Disjoint (x +ᵥ B) (B + B) := by
    rw [Finset.disjoint_left]
    intro y hyx hyBB
    obtain ⟨b, hb, hby⟩ := Finset.mem_vadd_finset.mp hyx
    obtain ⟨b₁, hb₁, b₂, hb₂, hb12⟩ := Finset.mem_add.mp hyBB
    apply hx
    apply Finset.mem_sub.mpr
    refine ⟨b₁ + b₂, Finset.mem_add.mpr ⟨b₁, hb₁, b₂, hb₂, rfl⟩,
      b, hb, ?_⟩
    simp only [vadd_eq_add] at hby
    rw [hb12, ← hby]
    abel
  have htrans : x +ᵥ B ⊆ A + A := by
    intro y hy
    obtain ⟨b, hb, hby⟩ := Finset.mem_vadd_finset.mp hy
    apply Finset.mem_add.mpr
    refine ⟨x, hxA, b, hBA hb, ?_⟩
    simpa [vadd_eq_add] using hby
  have hdouble : B + B ⊆ A + A := Finset.add_subset_add hBA hBA
  have hunion : (x +ᵥ B) ∪ (B + B) ⊆ A + A :=
    Finset.union_subset htrans hdouble
  have hcard := Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint hdis, Finset.card_vadd_finset] at hcard
  exact hcard

end Erdos336
