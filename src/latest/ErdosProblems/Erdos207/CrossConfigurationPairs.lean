/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceTerminalAugmentation

/-! # Mixed configuration-pair candidates and their zero-profile count -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def crossDistinctConfigurationPairs
    {W : Type*} [DecidableEq W] (F G : Finset (Finset W)) (T T' : W) :
    Finset (Finset W × Finset W) :=
  (F ×ˢ G).filter fun C ↦ C.1 ≠ C.2 ∧ T ∈ C.1 ∧ T' ∈ C.2 ∧ C.1.erase T = C.2.erase T'

@[simp] theorem mem_crossDistinctConfigurationPairs_iff
    {W : Type*} [DecidableEq W] {F G : Finset (Finset W)} {T T' : W} {C : Finset W × Finset W} :
    C ∈ crossDistinctConfigurationPairs F G T T' ↔
      C.1 ∈ F ∧ C.2 ∈ G ∧ C.1 ≠ C.2 ∧ T ∈ C.1 ∧ T' ∈ C.2 ∧ C.1.erase T = C.2.erase T' := by
  simp only [crossDistinctConfigurationPairs, mem_filter, mem_product, and_assoc]

theorem crossDistinctConfigurationPairs_subset_union
    {W : Type*} [DecidableEq W] (F G : Finset (Finset W)) (T T' : W) :
    crossDistinctConfigurationPairs F G T T' ⊆ distinctEqualRemainderPairs (F ∪ G) T T' := by
  intro C hC
  obtain ⟨hF, hG, hrest⟩ := mem_crossDistinctConfigurationPairs_iff.mp hC
  exact mem_distinctEqualRemainderPairs_iff.mpr ⟨mem_union_left _ hF, mem_union_right _ hG, hrest⟩

theorem crossDistinctConfigurationPairs_sample_left
    {W : Type*} [DecidableEq W] (F G : Finset (Finset W)) (T T' : W) (ω : Finset W → Bool) :
    crossDistinctConfigurationPairs (F.filter fun C ↦ ω C = true) G T T' =
      (crossDistinctConfigurationPairs F G T T').filter fun C ↦ ω C.1 = true := by
  ext C
  simp only [mem_crossDistinctConfigurationPairs_iff, mem_filter]
  tauto

theorem crossDistinctConfigurationPairs_sample_right
    {W : Type*} [DecidableEq W] (F G : Finset (Finset W)) (T T' : W) (ω : Finset W → Bool) :
    crossDistinctConfigurationPairs F (G.filter fun C ↦ ω C = true) T T' =
      (crossDistinctConfigurationPairs F G T T').filter fun C ↦ ω C.2 = true := by
  ext C
  simp only [mem_crossDistinctConfigurationPairs_iff, mem_filter]
  tauto

theorem card_crossDistinctPairs_le_first_zero_profile
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F G : ForbiddenFamilyOn V) (T T' : TripleOn V)
    (hG : IsTerminalConfigurationFamily W G) :
    (crossDistinctConfigurationPairs F G T T').card ≤ (W.profiledExtensions F {T} 0).card := by
  apply card_le_card_of_injOn (fun C ↦ C.1)
  · intro C hC
    obtain ⟨hCF, hCG, _, hT, _, hrem⟩ := mem_crossDistinctConfigurationPairs_iff.mp hC
    apply (W.mem_profiledExtensions_iff _ _ _ _).mpr
    refine ⟨hCF, singleton_subset_iff.mpr hT, ?_⟩
    rw [sdiff_singleton_eq_erase, hrem]
    exact hG.outerProfile_subfamily hCG (erase_subset _ _)
  · intro C hC D hD heq
    exact distinctEqualRemainderPairs_fst_injOn (F ∪ G) T T'
      (crossDistinctConfigurationPairs_subset_union F G T T' hC)
      (crossDistinctConfigurationPairs_subset_union F G T T' hD) heq

theorem card_crossDistinctPairs_le_second_zero_profile
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F G : ForbiddenFamilyOn V) (T T' : TripleOn V)
    (hF : IsTerminalConfigurationFamily W F) :
    (crossDistinctConfigurationPairs F G T T').card ≤ (W.profiledExtensions G {T'} 0).card := by
  apply card_le_card_of_injOn (fun C ↦ C.2)
  · intro C hC
    obtain ⟨hCF, hCG, _, _, hT', hrem⟩ := mem_crossDistinctConfigurationPairs_iff.mp hC
    apply (W.mem_profiledExtensions_iff _ _ _ _).mpr
    refine ⟨hCG, singleton_subset_iff.mpr hT', ?_⟩
    rw [sdiff_singleton_eq_erase, ← hrem]
    exact hF.outerProfile_subfamily hCF (erase_subset _ _)
  · intro C hC D hD heq
    exact distinctEqualRemainderPairs_snd_injOn (F ∪ G) T T'
      (crossDistinctConfigurationPairs_subset_union F G T T' hC)
      (crossDistinctConfigurationPairs_subset_union F G T T' hD) heq

theorem card_profiledDistinctPairs_union_le_four
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F G : ForbiddenFamilyOn V) (T T' : TripleOn V) :
    (W.profiledDistinctEqualRemainderPairs (F ∪ G) T T' 0).card ≤
      (W.profiledDistinctEqualRemainderPairs F T T' 0).card + (distinctEqualRemainderPairs G T T').card +
        (crossDistinctConfigurationPairs F G T T').card + (crossDistinctConfigurationPairs G F T T').card := by
  let A := W.profiledDistinctEqualRemainderPairs F T T' 0
  let B := distinctEqualRemainderPairs G T T'
  let C := crossDistinctConfigurationPairs F G T T'
  let D := crossDistinctConfigurationPairs G F T T'
  have hsub : W.profiledDistinctEqualRemainderPairs (F ∪ G) T T' 0 ⊆ A ∪ B ∪ C ∪ D := by
    intro p hp
    obtain ⟨hp1, hp2, hne, hT, hT', hrem, hprof⟩ := (W.mem_profiledDistinctEqualRemainderPairs_iff _ _ _ _ _).mp hp
    rcases mem_union.mp hp1 with hF1 | hG1 <;> rcases mem_union.mp hp2 with hF2 | hG2
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _
        ((W.mem_profiledDistinctEqualRemainderPairs_iff _ _ _ _ _).mpr ⟨hF1, hF2, hne, hT, hT', hrem, hprof⟩)))
    · exact mem_union_left _ (mem_union_right _
        (mem_crossDistinctConfigurationPairs_iff.mpr ⟨hF1, hG2, hne, hT, hT', hrem⟩))
    · exact mem_union_right _
        (mem_crossDistinctConfigurationPairs_iff.mpr ⟨hG1, hF2, hne, hT, hT', hrem⟩)
    · exact mem_union_left _ (mem_union_left _ (mem_union_right _
        (mem_distinctEqualRemainderPairs_iff.mpr ⟨hG1, hG2, hne, hT, hT', hrem⟩)))
  calc
    _ ≤ (A ∪ B ∪ C ∪ D).card := card_le_card hsub
    _ ≤ (A ∪ B ∪ C).card + D.card := card_union_le _ _
    _ ≤ ((A ∪ B).card + C.card) + D.card := Nat.add_le_add_right (card_union_le _ _) _
    _ ≤ ((A.card + B.card) + C.card) + D.card :=
      Nat.add_le_add_right (Nat.add_le_add_right (card_union_le _ _) _) _

end

end Erdos207
