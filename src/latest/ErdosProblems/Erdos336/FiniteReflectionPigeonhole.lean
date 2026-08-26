import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A finite pigeonhole reflection lemma
-/

namespace Erdos336

/-- If every reflected point `u-x`, for `x` in a finite piece `X⊂S`, can be
moved into `S` by one of finitely many shifts `F`, then one shift works on at
least the floor-average number of points.  The resulting `C` lies in `S` and
its reflection about `u-f` also lies in `S`. -/
theorem exists_large_reflected_piece
    {S : Set ℤ} {X F : Finset ℤ} {u : ℤ}
    (hFne : F.Nonempty)
    (hXS : ∀ x ∈ X, x ∈ S)
    (hcover : ∀ x ∈ X, ∃ f ∈ F, u - x - f ∈ S) :
    ∃ f ∈ F, ∃ C : Finset ℤ,
      (∀ x ∈ C, x ∈ X ∧ x ∈ S ∧ (u - f) - x ∈ S) ∧
      X.card / F.card ≤ C.card := by
  classical
  let fdefault : ℤ := hFne.choose
  have hfdefault : fdefault ∈ F := hFne.choose_spec
  let pick : ℤ → ℤ := fun x =>
    if hx : x ∈ X then Classical.choose (hcover x hx) else fdefault
  have hpick_mem : ∀ x ∈ X, pick x ∈ F := by
    intro x hx
    simp only [pick, dif_pos hx]
    exact (Classical.choose_spec (hcover x hx)).1
  have hpick_reflect : ∀ x ∈ X, u - x - pick x ∈ S := by
    intro x hx
    simp only [pick, dif_pos hx]
    exact (Classical.choose_spec (hcover x hx)).2
  have hmul : F.card * (X.card / F.card) ≤ X.card :=
    Nat.mul_div_le X.card F.card
  obtain ⟨f, hfF, hfcard⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      hpick_mem hFne hmul
  let C : Finset ℤ := {x ∈ X | pick x = f}
  refine ⟨f, hfF, C, ?_, ?_⟩
  · intro x hxC
    have hx : x ∈ X := (Finset.mem_filter.mp hxC).1
    have hpick : pick x = f := (Finset.mem_filter.mp hxC).2
    refine ⟨hx, hXS x hx, ?_⟩
    have href := hpick_reflect x hx
    rw [hpick] at href
    convert href using 1 <;> ring
  · simpa [C] using hfcard

end Erdos336
