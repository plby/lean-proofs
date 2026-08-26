import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {G Q : Type*} [AddCommGroup G] [DecidableEq G]
  [AddCommGroup Q] [DecidableEq Q]

/-- Translating one fibre of `B` by representatives of all image fibres of
`A` gives disjoint subsets of `A+B`. -/
theorem card_image_mul_card_fiber_le_card_add
    (f : G →+ Q) (A B : Finset G) (z : Q) :
    (A.image f).card * (B.filter fun b => f b = z).card ≤ (A + B).card := by
  let T : Finset Q := A.image f
  let U : Finset G := B.filter fun b => f b = z
  let rep : (y : ↥T) → G := fun y => (Finset.mem_image.mp y.property).choose
  have hrep_mem (y : ↥T) : rep y ∈ A :=
    (Finset.mem_image.mp y.property).choose_spec.1
  have hrep_map (y : ↥T) : f (rep y) = y.1 :=
    (Finset.mem_image.mp y.property).choose_spec.2
  have hUmem (b : ↥U) : b.1 ∈ B :=
    (Finset.mem_filter.mp b.property).1
  have hUmap (b : ↥U) : f b.1 = z :=
    (Finset.mem_filter.mp b.property).2
  let e : (↥T × ↥U) → ↥(A + B) := fun p =>
    ⟨rep p.1 + p.2.1,
      Finset.mem_add.mpr ⟨rep p.1, hrep_mem p.1,
        p.2.1, hUmem p.2, rfl⟩⟩
  have heinj : Function.Injective e := by
    rintro ⟨y₁, b₁⟩ ⟨y₂, b₂⟩ he
    have hsum : rep y₁ + b₁.1 = rep y₂ + b₂.1 :=
      congrArg Subtype.val he
    have hmaps := congrArg f hsum
    rw [map_add, map_add, hrep_map, hrep_map, hUmap, hUmap] at hmaps
    have hyval : y₁.1 = y₂.1 := add_right_cancel hmaps
    have hy : y₁ = y₂ := Subtype.ext hyval
    subst y₂
    have hbval : b₁.1 = b₂.1 := add_left_cancel hsum
    have hb : b₁ = b₂ := Subtype.ext hbval
    subst b₂
    rfl
  have hcard := Fintype.card_le_of_injective e heinj
  simpa [T, U] using hcard

/-- One image fibre has at least the average size, in division-free form. -/
theorem exists_card_le_image_mul_card_fiber
    (f : G →+ Q) (B : Finset G) (hB : B.Nonempty) :
    ∃ z ∈ B.image f,
      B.card ≤ (B.image f).card * (B.filter fun b => f b = z).card := by
  have hT : (B.image f).Nonempty := hB.image f
  obtain ⟨z, hz, hzmax⟩ := Finset.exists_max_image (B.image f)
    (fun y => (B.filter fun b => f b = y).card) hT
  refine ⟨z, hz, ?_⟩
  have hmaps : (B : Set G).MapsTo f (B.image f) := by
    intro b hb
    exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc
    ∑ y ∈ B.image f, (B.filter fun b => f b = y).card
        ≤ ∑ _y ∈ B.image f, (B.filter fun b => f b = z).card := by
          exact Finset.sum_le_sum fun y hy => hzmax y hy
    _ = (B.image f).card * (B.filter fun b => f b = z).card := by
      simp

/-- Image cardinalities obey an elementary quotient product bound. -/
theorem card_image_mul_card_le_card_image_mul_card_add
    (f : G →+ Q) (A B : Finset G) (hB : B.Nonempty) :
    (A.image f).card * B.card ≤ (B.image f).card * (A + B).card := by
  obtain ⟨z, _hz, hBavg⟩ := exists_card_le_image_mul_card_fiber f B hB
  calc
    (A.image f).card * B.card
        ≤ (A.image f).card * ((B.image f).card *
            (B.filter fun b => f b = z).card) :=
          Nat.mul_le_mul_left _ hBavg
    _ = (B.image f).card * ((A.image f).card *
            (B.filter fun b => f b = z).card) := by ring
    _ ≤ (B.image f).card * (A + B).card :=
      Nat.mul_le_mul_left _ (card_image_mul_card_fiber_le_card_add f A B z)

end Erdos336
