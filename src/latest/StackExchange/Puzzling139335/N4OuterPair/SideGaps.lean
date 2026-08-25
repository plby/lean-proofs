import StackExchange.Puzzling139335.N4OuterPair.SideIntervals
import StackExchange.Puzzling139335.N4OuterPair.Remainder

/-!
# Actual vertical gaps are covered by the middle pair

Reflection determines the upper outer contacts from the lower ones.  On a
strict gap the cover must therefore come from a middle piece.  Closedness
then includes both endpoints of every nondegenerate gap.
-/

open Set

namespace Puzzling139335.N4OuterPair.Configuration

variable {d : SquareDissection}

private theorem horizontal_side_point (x y : ℝ) :
    ReflectionSeparation.horizontal (Schoenflies.Plane.mk x y) =
      Schoenflies.Plane.mk x (1 - y) := by
  ext i
  fin_cases i <;> simp

theorem reflected_side_mem_iff (h : Configuration d) (x y : ℝ) :
    Schoenflies.Plane.mk x y ∈ d.piece 1 ↔
      Schoenflies.Plane.mk x (1 - y) ∈ d.piece 0 := by
  constructor
  · intro hy
    have hm : ReflectionSeparation.horizontal (Schoenflies.Plane.mk x y) ∈ d.piece 0 :=
      h.reflection_back ▸ mem_image_of_mem ReflectionSeparation.horizontal hy
    simpa only [horizontal_side_point] using hm
  · intro hy
    have hm : ReflectionSeparation.horizontal (Schoenflies.Plane.mk x (1 - y)) ∈
        d.piece 1 := h.reflected ▸ mem_image_of_mem ReflectionSeparation.horizontal hy
    simpa only [horizontal_side_point, sub_sub_cancel] using hm

theorem upper_side_contact_iff (h : Configuration d) {x c : ℝ}
    (hcontact : ∀ y : ℝ, Schoenflies.Plane.mk x y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) c)
    (y : ℝ) :
    Schoenflies.Plane.mk x y ∈ d.piece 1 ↔ y ∈ Icc (1 - c) (1 : ℝ) := by
  rw [h.reflected_side_mem_iff, hcontact]
  constructor
  · rintro ⟨h₀, h₁⟩
    exact ⟨by linarith only [h₁], by linarith only [h₀]⟩
  · rintro ⟨h₀, h₁⟩
    exact ⟨by linarith only [h₁], by linarith only [h₀]⟩

theorem open_side_gap_covered (h : Configuration d) {x c : ℝ}
    (hx : x = 0 ∨ x = 1) (hc0 : 0 ≤ c)
    (hcontact : ∀ y : ℝ, Schoenflies.Plane.mk x y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) c)
    {y : ℝ} (hy : y ∈ Ioo c (1 - c)) :
    Schoenflies.Plane.mk x y ∈ d.piece 2 ∪ d.piece 3 := by
  have hyS : Schoenflies.Plane.mk x y ∈ unitSquare := by
    change x ∈ Icc (0 : ℝ) 1 ∧ y ∈ Icc (0 : ℝ) 1
    refine ⟨?_, ?_⟩
    · rcases hx with rfl | rfl <;> norm_num
    · exact ⟨by linarith only [hc0, hy.1], by linarith only [hc0, hy.2]⟩
  obtain ⟨i, hi⟩ := d.exists_piece_mem hyS
  fin_cases i
  · exact (not_le_of_gt hy.1 ((hcontact y).mp hi).2).elim
  · exact (not_le_of_gt hy.2 ((h.upper_side_contact_iff hcontact y).mp hi).1).elim
  · exact Or.inl hi
  · exact Or.inr hi

theorem closed_side_gap_covered (h : Configuration d) {x c : ℝ}
    (hx : x = 0 ∨ x = 1) (hc0 : 0 ≤ c) (hcHalf : c < 1 / 2)
    (hcontact : ∀ y : ℝ, Schoenflies.Plane.mk x y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) c) :
    ∀ y ∈ Icc c (1 - c), Schoenflies.Plane.mk x y ∈ d.piece 2 ∪ d.piece 3 := by
  let K : Set ℝ := {y | Schoenflies.Plane.mk x y ∈ d.piece 2 ∪ d.piece 3}
  have hKclosed : IsClosed K := by
    apply ((d.jordan 2).isClosed.union (d.jordan 3).isClosed).preimage
    fun_prop
  have hsub : Ioo c (1 - c) ⊆ K :=
    fun _ hy => h.open_side_gap_covered hx hc0 hcontact hy
  have hclosure := closure_minimal hsub hKclosed
  rw [closure_Ioo (by linarith only [hcHalf] : c ≠ 1 - c)] at hclosure
  exact hclosure

end Puzzling139335.N4OuterPair.Configuration
