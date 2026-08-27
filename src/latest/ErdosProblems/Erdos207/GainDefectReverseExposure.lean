/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GainDefectExposure

/-! # Reverse exposure of a gain defect and the off-diagonal exception -/

namespace Erdos207.GainDefectWitness

open Finset

noncomputable section

variable {W : Type*} [DecidableEq W] {F G : Finset (Finset W)} {T : W} {z : ℕ}

def reverseFirstRoot (w : GainDefectWitness F G T z) : Finset W :=
  insert T (w.second ∩ w.first)

def reverseSecondRoot (w : GainDefectWitness F G T z) (H : Finset W) : Finset W :=
  H ∪ (w.second ∩ {T})

theorem extension_subset_second_of_forwardExceptional
    (w : GainDefectWitness F G T z) (H : Finset W)
    (hH : H ⊆ w.remainder) (he : w.ForwardExceptional H) : H ⊆ w.second := by
  intro x hx
  have hu := (mem_sdiff.mp (w.remainder_eq_sdiff ▸ hH hx)).1
  rcases mem_union.mp hu with hf | hs
  · exact (disjoint_left.mp he.1 hf hx).elim
  · exact hs

theorem second_eq_inter_union_extension
    (w : GainDefectWitness F G T z) (H : Finset W)
    (hH : H ⊆ w.remainder) (he : w.ForwardExceptional H) :
    w.second = (w.second ∩ w.first) ∪ H := by
  apply Subset.antisymm
  · intro x hx
    rcases mem_union.mp (he.2.1 hx) with hf | hh
    · exact mem_union_left _ (mem_inter.mpr ⟨hx, hf⟩)
    · exact mem_union_right _ hh
  · exact union_subset inter_subset_left (w.extension_subset_second_of_forwardExceptional H hH he)

theorem reverseFirstRoot_subset (w : GainDefectWitness F G T z) :
    w.reverseFirstRoot ⊆ w.first := insert_subset w.root_mem inter_subset_right

theorem reverseSecondRoot_subset (w : GainDefectWitness F G T z) (H : Finset W)
    (hH : H ⊆ w.remainder) (he : w.ForwardExceptional H) :
    w.reverseSecondRoot H ⊆ w.second :=
  union_subset (w.extension_subset_second_of_forwardExceptional H hH he) inter_subset_left

theorem reverseFirstRoot_card_ge_two (w : GainDefectWitness F G T z) :
    2 ≤ w.reverseFirstRoot.card := by
  rw [← w.second_root_card]
  apply card_le_card
  intro x hx
  exact mem_insert_of_mem (mem_inter.mpr
    ⟨(mem_inter.mp hx).1, w.omittedRoot_subset_first (mem_inter.mp hx).2⟩)

theorem reverseSecondRoot_card_lt (w : GainDefectWitness F G T z) (H : Finset W)
    (hH : H ⊆ w.remainder) (he : w.ForwardExceptional H) :
    (w.reverseSecondRoot H).card < w.second.card := by
  have hnot : ¬ w.second ∩ w.omittedRoot ⊆ {T} := by
    intro h
    have hc := card_le_card h
    rw [omittedRoot, w.second_root_card, card_singleton] at hc
    omega
  obtain ⟨U, hU, hUT⟩ := Finset.not_subset.mp hnot
  have hnotRoot : U ∉ w.reverseSecondRoot H := by
    intro hx
    rcases mem_union.mp hx with hxH | hxT
    · exact disjoint_left.mp w.disjoint_omittedRoot_remainder (mem_inter.mp hU).2 (hH hxH)
    · exact hUT (mem_inter.mp hxT).2
  apply card_lt_card
  apply ssubset_iff_subset_ne.mpr
  refine ⟨w.reverseSecondRoot_subset H hH he, ?_⟩
  intro heq
  exact hnotRoot (heq ▸ (mem_inter.mp hU).1)

theorem reverseRoot_card_add (w : GainDefectWitness F G T z) (H : Finset W)
    (hH : H ⊆ w.remainder) (he : w.ForwardExceptional H) :
    w.reverseFirstRoot.card + (w.reverseSecondRoot H).card = w.second.card + 1 := by
  have hc := card_union_of_disjoint (he.1.mono_left (inter_subset_right :
    w.second ∩ w.first ⊆ w.first))
  rw [← w.second_eq_inter_union_extension H hH he] at hc
  by_cases hT : T ∈ w.second
  · have hI : T ∈ w.second ∩ w.first := mem_inter.mpr ⟨hT, w.root_mem⟩
    rw [reverseFirstRoot, insert_eq_of_mem hI, reverseSecondRoot,
      inter_singleton_of_mem hT, union_singleton,
      card_insert_of_notMem (w.root_not_mem_extension H hH)]
    omega
  · have hI : T ∉ w.second ∩ w.first := fun h ↦ hT (mem_inter.mp h).1
    rw [reverseFirstRoot, card_insert_of_notMem hI, reverseSecondRoot,
      inter_singleton_of_notMem hT, union_empty]
    omega

theorem remainder_sdiff_eq_left_of_forwardExceptional
    (w : GainDefectWitness F G T z) (H : Finset W)
    (he : w.ForwardExceptional H) : w.remainder \ H = w.leftRemainder := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxR, hxH⟩ := mem_sdiff.mp hx
    rcases mem_union.mp hxR with hl | hr
    · exact hl
    · have hs := mem_sdiff.mp hr
      have hf : x ∈ w.first := (mem_union.mp (he.2.1 hs.1)).resolve_right hxH
      exact mem_sdiff.mpr ⟨hf, hs.2⟩
  · intro hx
    refine mem_sdiff.mpr ⟨mem_union_left _ hx, ?_⟩
    exact fun hh ↦ disjoint_left.mp he.1 (mem_sdiff.mp hx).1 hh

theorem reverse_exception_has_equal_remainders
    (w : GainDefectWitness F G T z) (H : Finset W)
    (hH : H ⊆ w.remainder) (he : w.ForwardExceptional H)
    (ha : w.reverseFirstRoot.card = w.first.card)
    (hb : (w.reverseSecondRoot H).card = 1) :
    H.card = 1 ∧ T ∉ w.second ∧ w.second \ H = w.first.erase T := by
  have hcard : H.card ≤ 1 := by
    rw [← hb]
    exact card_le_card subset_union_left
  have hpos := card_pos.mpr he.2.2
  have hHcard : H.card = 1 := by omega
  have hnotT : T ∉ w.second := by
    intro hT
    rw [reverseSecondRoot, inter_singleton_of_mem hT, union_singleton,
      card_insert_of_notMem (w.root_not_mem_extension H hH), hHcard] at hb
    omega
  have hfull : w.reverseFirstRoot = w.first :=
    eq_of_subset_of_card_le w.reverseFirstRoot_subset ha.ge
  refine ⟨hHcard, hnotT, ?_⟩
  have hI : T ∉ w.second ∩ w.first := fun h ↦ hnotT (mem_inter.mp h).1
  have herase : w.first.erase T = w.second ∩ w.first := by
    conv_lhs => rw [← hfull]
    exact erase_insert hI
  rw [herase]
  ext x
  constructor
  · intro hx
    have hd := mem_sdiff.mp hx
    exact mem_inter.mpr ⟨hd.1, (mem_union.mp (he.2.1 hd.1)).resolve_right hd.2⟩
  · intro hx
    exact mem_sdiff.mpr ⟨(mem_inter.mp hx).1,
      fun hh ↦ disjoint_left.mp he.1 (mem_inter.mp hx).2 hh⟩

theorem reverse_exponent_or_equal_remainders
    (w : GainDefectWitness F G T z) (H : Finset W)
    (hH : H ⊆ w.remainder) (he : w.ForwardExceptional H)
    (r s : ℕ) (hfirst : w.first.card = r - 2) (hsecond : w.second.card = s - 2) :
    s + 4 ≤ vortexRootExponent r w.reverseFirstRoot.card +
        vortexRootExponent s (w.reverseSecondRoot H).card ∨
      (H.card = 1 ∧ T ∉ w.second ∧ w.second \ H = w.first.erase T) := by
  have hlt : (w.reverseSecondRoot H).card < s - 2 := by
    rw [← hsecond]
    exact w.reverseSecondRoot_card_lt H hH he
  have hc := w.reverseRoot_card_add H hH he
  have hspos : 0 < w.second.card := by
    have h2 : 2 ≤ w.second.card := w.second_root_card ▸
      (card_le_card (inter_subset_left : w.second ∩ insert T w.omitted ⊆ w.second))
    omega
  rcases vortexRootExponent_reverse_nibble_split w.reverseFirstRoot_card_ge_two hlt
    (by omega : w.reverseFirstRoot.card + (w.reverseSecondRoot H).card + 1 = s) with h | h
  · exact Or.inl h
  · exact Or.inr (w.reverse_exception_has_equal_remainders H hH he
      (h.1.trans hfirst.symm) h.2)

end

end Erdos207.GainDefectWitness
