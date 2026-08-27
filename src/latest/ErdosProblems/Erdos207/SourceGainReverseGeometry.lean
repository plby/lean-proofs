/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceGainForwardGeometry
import ErdosProblems.Erdos207.GainDefectReverseExposure

/-! # Reversed source exposure in the exceptional forward gain branch -/

namespace Erdos207.GainDefectWitness

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {F G : ForbiddenFamilyOn V} {T : TripleOn V} {a : ℕ}

theorem reverse_first_omitted (u : GainDefectWitness F G T a) (H : TripleSystemOn V)
    (hH : H ⊆ u.remainder) :
    (u.second \ u.reverseSecondRoot H) \ (u.rightRemainder \ H) = u.second ∩ u.omitted := by
  ext R
  constructor
  · intro hR
    obtain ⟨hR, hnright⟩ := mem_sdiff.mp hR
    obtain ⟨hsecond, hnroot⟩ := mem_sdiff.mp hR
    have hnH : R ∉ H := fun hh ↦ hnroot (mem_union_left _ hh)
    have hnT : R ≠ T := by
      intro heq
      exact hnroot (mem_union_right _ (mem_inter.mpr ⟨hsecond, mem_singleton.mpr heq⟩))
    refine mem_inter.mpr ⟨hsecond, ?_⟩
    by_contra hnO
    have hnotRoot : R ∉ u.omittedRoot := fun hr ↦ (mem_insert.mp hr).elim hnT hnO
    exact hnright (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hsecond, hnotRoot⟩, hnH⟩)
  · intro hR
    obtain ⟨hsecond, hO⟩ := mem_inter.mp hR
    have hnT := (mem_erase.mp (u.omitted_subset hO)).1
    have hnH : R ∉ H := fun hh ↦ disjoint_left.mp (u.omittedRoot_disjoint_extension H hH)
      (mem_insert_of_mem hO) hh
    refine mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hsecond, ?_⟩, ?_⟩
    · intro hr
      exact (mem_union.mp hr).elim hnH (fun hi ↦ hnT (mem_singleton.mp (mem_inter.mp hi).2))
    · intro hr
      exact (mem_sdiff.mp (mem_sdiff.mp hr).1).2 (mem_insert_of_mem hO)

theorem reverse_second_omitted (u : GainDefectWitness F G T a) (H : TripleSystemOn V)
    (hH : H ⊆ u.remainder) (he : u.ForwardExceptional H) :
    (u.first \ {T}) \ (u.leftRemainder \ H) = u.omitted := by
  have ho := u.forward_first_omitted H hH
  have hroot : u.firstExposureRoot H = {T} := by
    rw [firstExposureRoot, disjoint_iff_inter_eq_empty.mp he.1]
    rfl
  rw [hroot] at ho
  exact ho

theorem reverseFirstRoot_eq_source_inter (u : GainDefectWitness F G T a) :
    u.reverseFirstRoot = u.first ∩ (u.second ∪ {T}) := by
  ext R
  by_cases hRT : R = T
  · subst R
    simp only [reverseFirstRoot, mem_insert, mem_inter, mem_union, mem_singleton,
      u.root_mem, true_or, or_true, and_true]
  · simp only [reverseFirstRoot, mem_insert, mem_inter, mem_union, mem_singleton, hRT, false_or, or_false]
    tauto

def sourceReverseExposure {ell : ℕ} (W : Vortex V ell) (u : GainDefectWitness F G T a)
    (H : TripleSystemOn V) (hH : H ⊆ u.remainder) (he : u.ForwardExceptional H)
    (hterm : ∀ U ∈ u.omittedRoot, W.level U = Fin.last ell) (r : ℕ) :
    SourceTwoFamilyWitness W G F (u.reverseSecondRoot H) {T} r
      (vortexRootExponent r u.reverseFirstRoot.card) u.leftRemainder.card where
  first := u.second
  second := u.first
  left := u.rightRemainder \ H
  right := u.leftRemainder \ H
  first_mem := u.second_mem
  second_mem := u.first_mem
  first_root := u.reverseSecondRoot_subset H hH he
  second_root := singleton_subset_iff.mpr u.root_mem
  left_subset := by
    intro R hR
    obtain ⟨hleft, hnH⟩ := mem_sdiff.mp hR
    obtain ⟨hsecond, hnroot⟩ := mem_sdiff.mp hleft
    refine mem_sdiff.mpr ⟨hsecond, ?_⟩
    intro hr
    rcases mem_union.mp hr with hh | hin
    · exact hnH hh
    · exact hnroot (mem_insert.mpr (Or.inl (mem_singleton.mp (mem_inter.mp hin).2)))
  right_subset := by
    intro R hR
    have hm := mem_sdiff.mp (mem_sdiff.mp hR).1
    exact mem_sdiff.mpr ⟨hm.1, fun hr ↦ hm.2 (mem_insert.mpr (Or.inl (mem_singleton.mp hr)))⟩
  cross_first := by
    intro R hR
    obtain ⟨hr, hs⟩ := mem_inter.mp hR
    obtain ⟨hr, hnH⟩ := mem_sdiff.mp hr
    exact mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hs, (mem_sdiff.mp hr).2⟩, hnH⟩
  cross_second := by
    intro R hR
    obtain ⟨hl, hf⟩ := mem_inter.mp hR
    obtain ⟨hl, hnH⟩ := mem_sdiff.mp hl
    exact mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hf, (mem_sdiff.mp hl).2⟩, hnH⟩
  first_terminal := by
    intro R hR
    rw [u.reverse_first_omitted H hH] at hR
    exact hterm R (mem_insert_of_mem (mem_inter.mp hR).2)
  second_terminal := by
    intro R hR
    rw [u.reverse_second_omitted H hH he] at hR
    exact hterm R (mem_insert_of_mem hR)
  exposed_nonempty := ⟨T, mem_inter.mpr ⟨u.root_mem, mem_union_right _ (mem_singleton_self T)⟩⟩
  exposed_exponent := by rw [← u.reverseFirstRoot_eq_source_inter]
  selected_card := by
    rw [union_comm, ← union_sdiff_distrib]
    exact congrArg Finset.card (u.remainder_sdiff_eq_left_of_forwardExceptional H he)

end

end Erdos207.GainDefectWitness
