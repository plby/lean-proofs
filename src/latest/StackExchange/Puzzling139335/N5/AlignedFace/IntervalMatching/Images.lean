import StackExchange.Puzzling139335.Definitions

/-!
# Coordinate formulas and images of aligned copies

These set identities use only the two coordinate formulas on the source
set. They do not require an isometry or any topological assumptions.
-/

open Set

namespace Puzzling139335.N5.AlignedFace

noncomputable section

/-- Horizontal translation by `δ`. -/
def horizontalTranslate (δ : ℝ) (z : Plane) : Plane :=
  Schoenflies.Plane.mk (z 0 + δ) (z 1)

/-- Reflection across the vertical line with first coordinate `κ / 2`. -/
def verticalReflect (κ : ℝ) (z : Plane) : Plane :=
  Schoenflies.Plane.mk (κ - z 0) (z 1)

@[simp] theorem horizontalTranslate_apply_zero (δ : ℝ) (z : Plane) :
    horizontalTranslate δ z 0 = z 0 + δ := rfl

@[simp] theorem horizontalTranslate_apply_one (δ : ℝ) (z : Plane) :
    horizontalTranslate δ z 1 = z 1 := rfl

@[simp] theorem verticalReflect_apply_zero (κ : ℝ) (z : Plane) :
    verticalReflect κ z 0 = κ - z 0 := rfl

@[simp] theorem verticalReflect_apply_one (κ : ℝ) (z : Plane) :
    verticalReflect κ z 1 = z 1 := rfl

theorem image_eq_horizontalTranslate {X : Type*} {P : Set X} {R D : X → Plane} {δ : ℝ}
    (hx : ∀ p ∈ P, D p 0 = R p 0 + δ) (hy : ∀ p ∈ P, D p 1 = R p 1) :
    D '' P = horizontalTranslate δ '' (R '' P) := by
  have hpoint : ∀ p ∈ P, D p = horizontalTranslate δ (R p) := by
    intro p hp
    ext i
    fin_cases i
    · exact hx p hp
    · exact hy p hp
  apply Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨R p, ⟨p, hp, rfl⟩, (hpoint p hp).symm⟩
  · rintro _ ⟨q, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, hpoint p hp⟩

theorem image_eq_verticalReflect {X : Type*} {P : Set X} {R D : X → Plane} {κ : ℝ}
    (hx : ∀ p ∈ P, D p 0 = κ - R p 0) (hy : ∀ p ∈ P, D p 1 = R p 1) :
    D '' P = verticalReflect κ '' (R '' P) := by
  have hpoint : ∀ p ∈ P, D p = verticalReflect κ (R p) := by
    intro p hp
    ext i
    fin_cases i
    · exact hx p hp
    · exact hy p hp
  apply Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨R p, ⟨p, hp, rfl⟩, (hpoint p hp).symm⟩
  · rintro _ ⟨q, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, hpoint p hp⟩

theorem verticalReflect_involutive (κ : ℝ) : Function.Involutive (verticalReflect κ) := by
  intro z
  ext i
  fin_cases i <;> simp

@[simp] theorem verticalReflect_twice (κ : ℝ) (z : Plane) :
    verticalReflect κ (verticalReflect κ z) = z :=
  verticalReflect_involutive κ z

@[simp] theorem verticalReflect_image_image (κ : ℝ) (A : Set Plane) :
    verticalReflect κ '' (verticalReflect κ '' A) = A := by
  ext p
  constructor
  · rintro ⟨q, ⟨r, hr, rfl⟩, rfl⟩
    simpa only [verticalReflect_twice] using hr
  · intro hp
    exact ⟨verticalReflect κ p, ⟨p, hp, rfl⟩, verticalReflect_twice κ p⟩

/-- Reflection exchanges two reflected sets, so it preserves their union. -/
theorem verticalReflect_image_union {A B : Set Plane} {κ : ℝ}
    (hB : B = verticalReflect κ '' A) :
    verticalReflect κ '' (A ∪ B) = A ∪ B := by
  rw [hB, image_union, verticalReflect_image_image]
  exact union_comm _ _

/-- The reflected union identity derived directly from the coordinate
relations on the source set. -/
theorem verticalReflect_image_union_of_coords {X : Type*} {P : Set X}
    {R D : X → Plane} {κ : ℝ}
    (hx : ∀ p ∈ P, D p 0 = κ - R p 0) (hy : ∀ p ∈ P, D p 1 = R p 1) :
    verticalReflect κ '' (R '' P ∪ D '' P) = R '' P ∪ D '' P :=
  verticalReflect_image_union (image_eq_verticalReflect hx hy)

end

end Puzzling139335.N5.AlignedFace
