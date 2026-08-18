/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.HighCoefficientThickness

/-!
# Pulling a functional slab back to the source core

The high-coefficient side is selected after translating by its distinguished
point.  A dense slab inside that translated side must be pulled back before
Definition 9 can be applied.  These elementary identities keep that change
of coordinates explicit.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

@[simp]
theorem pzTranslate_neg_pzTranslate {d : ℕ}
    (a : LatticePoint d) (X : Finset (LatticePoint d)) :
    PZ.translate (-a) (PZ.translate a X) = X := by
  classical
  ext x
  simp only [PZ.translate, Finset.mem_image]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa using hz
  · intro hx
    refine ⟨x + a, ⟨x, hx, rfl⟩, ?_⟩
    simp

@[simp]
theorem pzTranslate_identifiedTranslate {d : ℕ}
    (a : LatticePoint d) (X : Finset (LatticePoint d)) :
    PZ.translate a (Reduction.identifiedTranslate X a) = X := by
  simpa [Reduction.identifiedTranslate, add_comm] using
    pzTranslate_neg_pzTranslate (-a) X

@[simp]
theorem identifiedTranslate_pzTranslate {d : ℕ}
    (a : LatticePoint d) (X : Finset (LatticePoint d)) :
    Reduction.identifiedTranslate (PZ.translate a X) a = X := by
  simpa [Reduction.identifiedTranslate] using
    pzTranslate_neg_pzTranslate a X

/-- Pulling a subset of a translated side back by the inverse translation
puts it in the original side. -/
theorem pzTranslate_subset_of_subset_identifiedTranslate {d : ℕ}
    {a : LatticePoint d} {X Z : Finset (LatticePoint d)}
    (hZ : Z ⊆ Reduction.identifiedTranslate X a) :
    PZ.translate a Z ⊆ X := by
  rw [← pzTranslate_identifiedTranslate a X]
  exact Finset.image_mono _ hZ

/-- Cardinality and nonemptiness are unchanged by the pullback. -/
theorem pzTranslate_pullback_nonempty {d : ℕ}
    (a : LatticePoint d) (Z : Finset (LatticePoint d)) :
    (PZ.translate a Z).Nonempty ↔ Z.Nonempty := by
  rw [← Finset.card_pos, PZ.card_translate, Finset.card_pos]

end

end Erdos186.PZ.Intersection
