/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceTwoFamilyWeights

/-! # Literal two-family partitions and their ordered exposure geometry -/

namespace Erdos207

open Finset

noncomputable section

/-- The omitted parts are the complements of the root and selected part.
The two cross conditions say that a selected triangle cannot belong to the
other partition's root or omitted part. -/
structure SourceTwoFamilyWitness
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F F' : ForbiddenFamilyOn V)
    (Q Q' : TripleSystemOn V) (j' v' f : ℕ) where
  first : TripleSystemOn V
  second : TripleSystemOn V
  left : TripleSystemOn V
  right : TripleSystemOn V
  first_mem : first ∈ F
  second_mem : second ∈ F'
  first_root : Q ⊆ first
  second_root : Q' ⊆ second
  left_subset : left ⊆ first \ Q
  right_subset : right ⊆ second \ Q'
  cross_first : right ∩ first ⊆ left
  cross_second : left ∩ second ⊆ right
  first_terminal : ∀ T ∈ (first \ Q) \ left, W.level T = Fin.last ell
  second_terminal : ∀ T ∈ (second \ Q') \ right, W.level T = Fin.last ell
  exposed_nonempty : (second ∩ (first ∪ Q')).Nonempty
  exposed_exponent : vortexRootExponent j' (second ∩ (first ∪ Q')).card = v'
  selected_card : (left ∪ right).card = f

instance {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F F' : ForbiddenFamilyOn V)
    (Q Q' : TripleSystemOn V) (j' v' f : ℕ) :
    Finite (SourceTwoFamilyWitness W F F' Q Q' j' v' f) :=
  Finite.of_injective (fun x : SourceTwoFamilyWitness W F F' Q Q' j' v' f ↦
    (x.first, x.second, x.left, x.right))
    (by intro x y h; cases x; cases y; simp_all)

noncomputable instance {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F F' : ForbiddenFamilyOn V)
    (Q Q' : TripleSystemOn V) (j' v' f : ℕ) :
    Fintype (SourceTwoFamilyWitness W F F' Q Q' j' v' f) := Fintype.ofFinite _

namespace SourceTwoFamilyWitness

variable {V : Type*} [Fintype V] [DecidableEq V] {ell j' v' f : ℕ}
  {W : Vortex V ell} {F F' : ForbiddenFamilyOn V} {Q Q' : TripleSystemOn V}

theorem left_subset_first (x : SourceTwoFamilyWitness W F F' Q Q' j' v' f) :
    x.left ⊆ x.first := x.left_subset.trans sdiff_subset

theorem right_subset_second (x : SourceTwoFamilyWitness W F F' Q Q' j' v' f) :
    x.right ⊆ x.second := x.right_subset.trans sdiff_subset

theorem selected_split (x : SourceTwoFamilyWitness W F F' Q Q' j' v' f) :
    x.left ∪ (x.right \ x.first) = x.left ∪ x.right := by
  ext T
  simp only [mem_union, mem_sdiff]
  constructor
  · tauto
  · rintro (h | h)
    · exact Or.inl h
    · by_cases hfirst : T ∈ x.first
      · exact Or.inl (x.cross_first (mem_inter.mpr ⟨h, hfirst⟩))
      · exact Or.inr ⟨h, hfirst⟩

theorem selected_split_disjoint (x : SourceTwoFamilyWitness W F F' Q Q' j' v' f) :
    Disjoint x.left (x.right \ x.first) := by
  apply disjoint_left.mpr
  intro T hleft hright
  exact (mem_sdiff.mp hright).2 (x.left_subset_first hleft)

theorem selected_split_card (x : SourceTwoFamilyWitness W F F' Q Q' j' v' f) :
    x.left.card + (x.right \ x.first).card = f := by
  rw [← card_union_of_disjoint x.selected_split_disjoint, x.selected_split, x.selected_card]

theorem right_reconstruct (x : SourceTwoFamilyWitness W F F' Q Q' j' v' f) :
    (x.left ∩ x.second) ∪ (x.right \ x.first) = x.right := by
  ext T
  simp only [mem_union, mem_inter, mem_sdiff]
  constructor
  · rintro (h | h)
    · exact x.cross_second (mem_inter.mpr h)
    · exact h.1
  · intro hright
    by_cases hfirst : T ∈ x.first
    · exact Or.inl ⟨x.cross_first (mem_inter.mpr ⟨hright, hfirst⟩),
        x.right_subset_second hright⟩
    · exact Or.inr ⟨hright, hfirst⟩

theorem right_new_subset (x : SourceTwoFamilyWitness W F F' Q Q' j' v' f) :
    x.right \ x.first ⊆ x.second \ (x.second ∩ (x.first ∪ Q')) := by
  intro T hT
  obtain ⟨hR, hnF⟩ := mem_sdiff.mp hT
  obtain ⟨hS, hnQ⟩ := mem_sdiff.mp (x.right_subset hR)
  refine mem_sdiff.mpr ⟨hS, ?_⟩
  intro hbad
  exact (mem_union.mp (mem_inter.mp hbad).2).elim hnF hnQ

theorem right_new_terminal (x : SourceTwoFamilyWitness W F F' Q Q' j' v' f) :
    ∀ T ∈ (x.second \ (x.second ∩ (x.first ∪ Q'))) \ (x.right \ x.first),
      W.level T = Fin.last ell := by
  intro T hT
  obtain ⟨hT, hnNew⟩ := mem_sdiff.mp hT
  obtain ⟨hS, hnB⟩ := mem_sdiff.mp hT
  have hnF : T ∉ x.first := fun h ↦ hnB (mem_inter.mpr ⟨hS, mem_union_left _ h⟩)
  have hnQ : T ∉ Q' := fun h ↦ hnB (mem_inter.mpr ⟨hS, mem_union_right _ h⟩)
  have hnR : T ∉ x.right := fun h ↦ hnNew (mem_sdiff.mpr ⟨h, hnF⟩)
  exact x.second_terminal T (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hS, hnQ⟩, hnR⟩)

end SourceTwoFamilyWitness

end

end Erdos207
