import Mathlib
import ErdosProblems.Erdos336.FiniteReflectionPigeonhole

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Dense finite pieces extracted from syndetic sets
-/

namespace Erdos336

/-- A finite shift-cover of a finite set has one shift whose pullback into `S`
has at least the floor-average cardinality.  The output points themselves lie
in `S`; adding the selected shift puts them back in `J`. -/
theorem exists_large_shift_piece
    {S : Set ℤ} {J F : Finset ℤ}
    (hFne : F.Nonempty)
    (hcover : ∀ n ∈ J, ∃ f ∈ F, n - f ∈ S) :
    ∃ f ∈ F, ∃ C : Finset ℤ,
      (∀ x ∈ C, x ∈ S ∧ x + f ∈ J) ∧
      J.card / F.card ≤ C.card := by
  classical
  let fdefault : ℤ := hFne.choose
  have hfdefault : fdefault ∈ F := hFne.choose_spec
  let pick : ℤ → ℤ := fun n =>
    if hn : n ∈ J then Classical.choose (hcover n hn) else fdefault
  have hpick_mem : ∀ n ∈ J, pick n ∈ F := by
    intro n hn
    simp only [pick, dif_pos hn]
    exact (Classical.choose_spec (hcover n hn)).1
  have hpick_S : ∀ n ∈ J, n - pick n ∈ S := by
    intro n hn
    simp only [pick, dif_pos hn]
    exact (Classical.choose_spec (hcover n hn)).2
  have hmul : F.card * (J.card / F.card) ≤ J.card :=
    Nat.mul_div_le J.card F.card
  obtain ⟨f, hfF, hfcard⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      hpick_mem hFne hmul
  let X : Finset ℤ := {n ∈ J | pick n = f}
  let C : Finset ℤ := X.image fun n => n - f
  refine ⟨f, hfF, C, ?_, ?_⟩
  · intro x hxC
    obtain ⟨n, hnX, rfl⟩ := Finset.mem_image.mp hxC
    have hnJ : n ∈ J := (Finset.mem_filter.mp hnX).1
    have hpick : pick n = f := (Finset.mem_filter.mp hnX).2
    constructor
    · simpa [hpick] using hpick_S n hnJ
    · simpa using hnJ
  · have hcardC : C.card = X.card := by
      apply Finset.card_image_iff.mpr
      intro a ha b hb hab
      exact sub_left_injective hab
    rw [hcardC]
    simpa [X] using hfcard

/-- Two applications of finite pigeonhole: first obtain a large piece of `S`
from a shift-cover of `J`, then obtain a large subpiece whose reflection also
lies in `S`. -/
theorem exists_large_doubly_reflected_piece
    {S : Set ℤ} {J F : Finset ℤ} {u : ℤ}
    (hFne : F.Nonempty)
    (hcoverJ : ∀ n ∈ J, ∃ f ∈ F, n - f ∈ S)
    (hcoverReflect : ∀ x ∈ S, (∃ f ∈ F, u - x - f ∈ S)) :
    ∃ f₀ ∈ F, ∃ f₁ ∈ F, ∃ C : Finset ℤ,
      (∀ x ∈ C, x ∈ S ∧ x + f₀ ∈ J ∧ (u - f₁) - x ∈ S) ∧
      (J.card / F.card) / F.card ≤ C.card := by
  obtain ⟨f₀, hf₀, X, hX, hcardX⟩ :=
    exists_large_shift_piece hFne hcoverJ
  have hXS : ∀ x ∈ X, x ∈ S := fun x hx => (hX x hx).1
  have href : ∀ x ∈ X, ∃ f ∈ F, u - x - f ∈ S := by
    intro x hx
    exact hcoverReflect x (hXS x hx)
  obtain ⟨f₁, hf₁, C, hC, hcardC⟩ :=
    exists_large_reflected_piece hFne hXS href
  refine ⟨f₀, hf₀, f₁, hf₁, C, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxX, hxS, hxrefl⟩ := hC x hx
    exact ⟨hxS, (hX x hxX).2, hxrefl⟩
  · exact le_trans (Nat.div_le_div_right hcardX) hcardC

end Erdos336
