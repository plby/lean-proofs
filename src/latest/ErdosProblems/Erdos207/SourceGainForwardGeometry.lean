/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceTwoFamilyEncoding
import ErdosProblems.Erdos207.GainDefectExposure

/-! # The forward gain-defect exposure is a literal two-family source witness -/

namespace Erdos207.GainDefectWitness

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {F G : ForbiddenFamilyOn V} {T : TripleOn V} {a : ℕ}

theorem omittedRoot_disjoint_extension (u : GainDefectWitness F G T a) (H : TripleSystemOn V)
    (hH : H ⊆ u.remainder) : Disjoint u.omittedRoot H :=
  u.disjoint_omittedRoot_remainder.mono_right hH

theorem forward_first_omitted (u : GainDefectWitness F G T a) (H : TripleSystemOn V)
    (hH : H ⊆ u.remainder) :
    (u.first \ u.firstExposureRoot H) \ (u.leftRemainder \ H) = u.omitted := by
  ext R
  constructor
  · intro hR
    obtain ⟨hR, hnleft⟩ := mem_sdiff.mp hR
    obtain ⟨hfirst, hnroot⟩ := mem_sdiff.mp hR
    have hnT : R ≠ T := by
      intro heq
      exact hnroot (heq ▸ mem_insert_self T (u.first ∩ H))
    have hnH : R ∉ H := fun hh ↦ hnroot (mem_insert_of_mem (mem_inter.mpr ⟨hfirst, hh⟩))
    by_contra hnO
    have hnotRoot : R ∉ u.omittedRoot := by
      intro hr
      exact (mem_insert.mp hr).elim hnT hnO
    exact hnleft (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hfirst, hnotRoot⟩, hnH⟩)
  · intro hR
    have hm := mem_erase.mp (u.omitted_subset hR)
    have hnH : R ∉ H := fun hh ↦ disjoint_left.mp (u.omittedRoot_disjoint_extension H hH)
      (mem_insert_of_mem hR) hh
    refine mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hm.2, ?_⟩, ?_⟩
    · intro hr
      exact (mem_insert.mp hr).elim hm.1 (fun hi ↦ hnH (mem_inter.mp hi).2)
    · intro hl
      exact (mem_sdiff.mp (mem_sdiff.mp hl).1).2 (mem_insert_of_mem hR)

theorem forward_second_omitted (u : GainDefectWitness F G T a) (H : TripleSystemOn V)
    (hH : H ⊆ u.remainder) :
    (u.second \ (u.second ∩ H)) \ (u.rightRemainder \ H) = u.second ∩ u.omittedRoot := by
  ext R
  constructor
  · intro hR
    obtain ⟨hR, hnright⟩ := mem_sdiff.mp hR
    obtain ⟨hsecond, hnroot⟩ := mem_sdiff.mp hR
    have hnH : R ∉ H := fun hh ↦ hnroot (mem_inter.mpr ⟨hsecond, hh⟩)
    refine mem_inter.mpr ⟨hsecond, ?_⟩
    by_contra hnO
    exact hnright (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hsecond, hnO⟩, hnH⟩)
  · intro hR
    obtain ⟨hsecond, hroot⟩ := mem_inter.mp hR
    have hnH : R ∉ H := fun hh ↦ disjoint_left.mp (u.omittedRoot_disjoint_extension H hH) hroot hh
    exact mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hsecond, fun hi ↦ hnH (mem_inter.mp hi).2⟩,
      fun hr ↦ (mem_sdiff.mp (mem_sdiff.mp hr).1).2 hroot⟩

theorem secondExposureRoot_eq_source_inter (u : GainDefectWitness F G T a) (H : TripleSystemOn V) :
    u.secondExposureRoot H = u.second ∩ (u.first ∪ (u.second ∩ H)) := by
  ext R
  simp only [secondExposureRoot, mem_inter, mem_union]
  tauto

def sourceForwardExposure {ell : ℕ} (W : Vortex V ell) (u : GainDefectWitness F G T a)
    (H : TripleSystemOn V) (hH : H ⊆ u.remainder)
    (hterm : ∀ U ∈ u.omittedRoot, W.level U = Fin.last ell) (s : ℕ) :
    SourceTwoFamilyWitness W F G (u.firstExposureRoot H) (u.second ∩ H) s
      (vortexRootExponent s (u.secondExposureRoot H).card) (u.remainder \ H).card where
  first := u.first
  second := u.second
  left := u.leftRemainder \ H
  right := u.rightRemainder \ H
  first_mem := u.first_mem
  second_mem := u.second_mem
  first_root := u.firstExposureRoot_subset H
  second_root := inter_subset_left
  left_subset := by
    intro R hR
    obtain ⟨hleft, hnH⟩ := mem_sdiff.mp hR
    obtain ⟨hfirst, hnroot⟩ := mem_sdiff.mp hleft
    refine mem_sdiff.mpr ⟨hfirst, ?_⟩
    intro hr
    rcases mem_insert.mp hr with heq | hin
    · exact hnroot (heq ▸ mem_insert_self T u.omitted)
    · exact hnH (mem_inter.mp hin).2
  right_subset := by
    intro R hR
    obtain ⟨hright, hnH⟩ := mem_sdiff.mp hR
    exact mem_sdiff.mpr ⟨(mem_sdiff.mp hright).1, fun hi ↦ hnH (mem_inter.mp hi).2⟩
  cross_first := by
    intro R hR
    obtain ⟨hr, hf⟩ := mem_inter.mp hR
    obtain ⟨hr, hnH⟩ := mem_sdiff.mp hr
    exact mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hf, (mem_sdiff.mp hr).2⟩, hnH⟩
  cross_second := by
    intro R hR
    obtain ⟨hl, hs⟩ := mem_inter.mp hR
    obtain ⟨hl, hnH⟩ := mem_sdiff.mp hl
    exact mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hs, (mem_sdiff.mp hl).2⟩, hnH⟩
  first_terminal := by
    intro R hR
    rw [u.forward_first_omitted H hH] at hR
    exact hterm R (mem_insert_of_mem hR)
  second_terminal := by
    intro R hR
    rw [u.forward_second_omitted H hH] at hR
    exact hterm R (mem_inter.mp hR).2
  exposed_nonempty := by
    have hn : (u.second ∩ insert T u.omitted).Nonempty := by
      rw [← card_pos, u.second_root_card]
      omega
    obtain ⟨U, hU⟩ := hn
    exact ⟨U, mem_inter.mpr ⟨(mem_inter.mp hU).1,
      mem_union_left _ (u.omittedRoot_subset_first (mem_inter.mp hU).2)⟩⟩
  exposed_exponent := by rw [← u.secondExposureRoot_eq_source_inter H]
  selected_card := by rw [← union_sdiff_distrib]; rfl

end

end Erdos207.GainDefectWitness
