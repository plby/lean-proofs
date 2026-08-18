/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Set.Card

/-!
# Finite collision energy for Erdős Problem 822

Generic fiber counting and the finite Cauchy--Schwarz inequality used by the
GIL range argument.
-/

namespace Erdos822

open scoped BigOperators Finset

section FiniteEnergy

variable {α β : Type*} [DecidableEq β]

/-- The number of elements of `A` in a specified fiber of `f`. -/
def fiberCount (A : Finset α) (f : α → β) (b : β) : ℕ :=
  #{a ∈ A | f a = b}

/-- Collision energy in its standard fiber-square form.  Equivalently, this is
the number of ordered pairs in `A` on which `f` takes the same value. -/
def collisionEnergy (A : Finset α) (f : α → β) : ℕ :=
  ∑ b ∈ A.image f, fiberCount A f b ^ 2

/-- The ordered collision pairs themselves. -/
def collisionPairs (A : Finset α) (f : α → β) : Finset (α × α) :=
  (A ×ˢ A).filter fun aa ↦ f aa.1 = f aa.2

/-- A finite set is partitioned by the fibers of any map on it. -/
theorem card_eq_sum_fiberCount (A : Finset α) (f : α → β) :
    A.card = ∑ b ∈ A.image f, fiberCount A f b := by
  simpa only [fiberCount] using Finset.card_eq_sum_card_image f A

/-- Collision energy is the sum of the squares of the fiber sizes. -/
theorem collisionEnergy_eq_sum_sq (A : Finset α) (f : α → β) :
    collisionEnergy A f = ∑ b ∈ A.image f, fiberCount A f b ^ 2 := by
  rfl

/-- The fiber-square energy really counts ordered pairs with equal image. -/
theorem collisionPairs_card_eq_collisionEnergy (A : Finset α) (f : α → β) :
    (collisionPairs A f).card = collisionEnergy A f := by
  have hdisjoint : (↑(A.image f) : Set β).PairwiseDisjoint
      (fun b ↦ (A.filter fun a ↦ f a = b) ×ˢ (A.filter fun a ↦ f a = b)) := by
    intro b _ c _ hbc
    change Disjoint
      ((A.filter fun a ↦ f a = b) ×ˢ (A.filter fun a ↦ f a = b))
      ((A.filter fun a ↦ f a = c) ×ˢ (A.filter fun a ↦ f a = c))
    rw [Finset.disjoint_left]
    intro aa haa hbbaa
    simp only [Finset.mem_product, Finset.mem_filter] at haa hbbaa
    exact hbc (haa.1.2.symm.trans hbbaa.1.2)
  simp_rw [collisionEnergy, fiberCount, sq, ← Finset.card_product]
  rw [← Finset.card_disjiUnion (A.image f)
    (fun b ↦ (A.filter fun a ↦ f a = b) ×ˢ (A.filter fun a ↦ f a = b)) hdisjoint]
  congr 1
  apply Finset.ext
  intro aa
  rw [Finset.mem_disjiUnion]
  simp only [collisionPairs, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨ha₁, ha₂⟩, haa⟩
    refine ⟨f aa.1, Finset.mem_image_of_mem f ha₁, ?_⟩
    exact ⟨⟨ha₁, rfl⟩, ha₂, haa.symm⟩
  · rintro ⟨b, _, hab⟩
    exact ⟨⟨hab.1.1, hab.2.1⟩, hab.1.2.trans hab.2.2.symm⟩

/-- The finite Cauchy--Schwarz step at the heart of the GIL argument:
the square of the number of inputs is at most the image size times the
collision energy. -/
theorem card_sq_le_image_card_mul_collisionEnergy (A : Finset α) (f : α → β) :
    A.card ^ 2 ≤ (A.image f).card * collisionEnergy A f := by
  rw [card_eq_sum_fiberCount A f, collisionEnergy_eq_sum_sq A f]
  exact sq_sum_le_card_mul_sum_sq

/-- Reindexing a finite family through an injective map does not change its
collision energy. -/
theorem collisionEnergy_image_eq_of_injOn
    {γ : Type*} [DecidableEq α] (A : Finset γ) (g : γ → α) (f : α → β)
    (hg : Set.InjOn g A) :
    collisionEnergy (A.image g) f = collisionEnergy A (fun a ↦ f (g a)) := by
  rw [← collisionPairs_card_eq_collisionEnergy,
    ← collisionPairs_card_eq_collisionEnergy]
  symm
  apply Finset.card_bij
    (fun z _ ↦ (g z.1, g z.2))
  · intro z hz
    rw [collisionPairs, Finset.mem_filter, Finset.mem_product] at hz ⊢
    exact ⟨⟨Finset.mem_image_of_mem g hz.1.1,
      Finset.mem_image_of_mem g hz.1.2⟩, hz.2⟩
  · intro z hz w hw hzw
    rw [collisionPairs, Finset.mem_filter, Finset.mem_product] at hz hw
    have hleft : z.1 = w.1 := hg hz.1.1 hw.1.1
      (Prod.ext_iff.mp hzw).1
    have hright : z.2 = w.2 := hg hz.1.2 hw.1.2
      (Prod.ext_iff.mp hzw).2
    exact Prod.ext hleft hright
  · intro z hz
    rw [collisionPairs, Finset.mem_filter, Finset.mem_product] at hz
    obtain ⟨u, hu, huEq⟩ := Finset.mem_image.mp hz.1.1
    obtain ⟨v, hv, hvEq⟩ := Finset.mem_image.mp hz.1.2
    refine ⟨(u, v), ?_, ?_⟩
    rw [collisionPairs, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨hu, hv⟩, ?_⟩
    simpa [huEq, hvEq] using hz.2
    exact Prod.ext huEq hvEq

end FiniteEnergy

end Erdos822
