/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.Data.Finset.Card

/-!
# Finite choice of injective representatives

For a map on a finite set, choosing one point from each nonempty fiber
produces a subset on which the map is injective and whose image is unchanged.
This elementary fact identifies the cardinality of a finite image with the
largest cardinality of a family distinguished by the map.
-/

open Classical

namespace Erdos636

/-- A map on a finite set has a subset containing exactly one representative
of every fiber.  In particular, its restriction to that subset is injective
and has exactly the same image as the original finite set. -/
theorem exists_subset_injOn_image_eq {α β : Type*} (s : Finset α)
    (f : α → β) :
    ∃ t : Finset α, t ⊆ s ∧ Set.InjOn f (t : Set α) ∧ t.image f = s.image f := by
  classical
  let representative : ↥(s.image f) → α := fun y ↦
    Classical.choose (Finset.mem_image.mp y.property)
  have representative_spec (y : ↥(s.image f)) :
      representative y ∈ s ∧ f (representative y) = y :=
    Classical.choose_spec (Finset.mem_image.mp y.property)
  let t : Finset α := (s.image f).attach.image representative
  have ht_subset : t ⊆ s := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, _hy, rfl⟩
    exact (representative_spec y).1
  have ht_injOn : Set.InjOn f (t : Set α) := by
    intro x hx z hz hxz
    rcases Finset.mem_image.mp hx with ⟨y, _hy, rfl⟩
    rcases Finset.mem_image.mp hz with ⟨w, _hw, rfl⟩
    have hyw : y = w := by
      apply Subtype.ext
      exact (representative_spec y).2.symm.trans
        (hxz.trans (representative_spec w).2)
    rw [hyw]
  have ht_image : t.image f = s.image f := by
    apply Finset.Subset.antisymm
    · intro y hy
      rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
      exact Finset.mem_image.mpr ⟨x, ht_subset hx, rfl⟩
    · intro y hy
      let y' : ↥(s.image f) := ⟨y, hy⟩
      have hrep : representative y' ∈ t :=
        Finset.mem_image.mpr ⟨y', Finset.mem_attach _ _, rfl⟩
      exact Finset.mem_image.mpr
        ⟨representative y', hrep, (representative_spec y').2⟩
  exact ⟨t, ht_subset, ht_injOn, ht_image⟩

/-- The cardinality of a finite image is attained by a subset on which the
map is injective. -/
theorem exists_subset_injOn_card_eq_card_image {α β : Type*} (s : Finset α)
    (f : α → β) :
    ∃ t : Finset α,
      t ⊆ s ∧ Set.InjOn f (t : Set α) ∧ t.card = (s.image f).card := by
  classical
  obtain ⟨t, hts, hinj, himage⟩ := exists_subset_injOn_image_eq s f
  refine ⟨t, hts, hinj, ?_⟩
  calc
    t.card = (t.image f).card := (Finset.card_image_iff.mpr hinj).symm
    _ = (s.image f).card := congrArg Finset.card himage

end Erdos636
