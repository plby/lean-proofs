/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

/-! # A finite image loses at most its number of ordered collisions -/

namespace Erdos207

open Finset

noncomputable section

def imageCollisions {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) : Finset (α × α) :=
  (s ×ˢ s).filter fun p ↦ p.1 ≠ p.2 ∧ f p.1 = f p.2

theorem card_le_card_image_add_collisions
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) :
    s.card ≤ (s.image f).card + (imageCollisions s f).card := by
  classical
  have hfibre (y : s.image f) : ∃ x ∈ s, f x = y.1 := mem_image.mp y.2
  let r : s.image f → α := fun y ↦ (hfibre y).choose
  have hr (y : s.image f) : r y ∈ s ∧ f (r y) = y.1 := (hfibre y).choose_spec
  have hinj : Function.Injective r := by
    intro y z h
    apply Subtype.ext
    exact (hr y).2.symm.trans ((congrArg f h).trans (hr z).2)
  let reps : Finset α := univ.image r
  have hsub : reps ⊆ s := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := mem_image.mp hx
    exact (hr y).1
  have hcard : reps.card = (s.image f).card := by
    dsimp only [reps]
    rw [card_image_of_injective _ hinj, card_univ, Fintype.card_coe]
  let code : ↥(s \ reps) → imageCollisions s f := fun x ↦
    let y : s.image f := ⟨f x.1, mem_image_of_mem f (mem_sdiff.mp x.2).1⟩
    ⟨(x.1, r y), mem_filter.mpr ⟨mem_product.mpr ⟨(mem_sdiff.mp x.2).1, (hr y).1⟩,
      (by
        intro h
        change x.1 = r y at h
        apply (mem_sdiff.mp x.2).2
        change x.1 ∈ univ.image r
        rw [h]
        exact mem_image_of_mem r (mem_univ y)),
      (hr y).2.symm⟩⟩
  have hcode : Function.Injective code := by
    intro x y h
    exact Subtype.ext (congrArg (fun p : imageCollisions s f ↦ p.1.1) h)
  have hsmall : (s \ reps).card ≤ (imageCollisions s f).card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective code hcode
  have hsum := card_sdiff_add_card_eq_card hsub
  omega

end

end Erdos207
