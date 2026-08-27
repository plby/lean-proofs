/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GainDefectWitness
import ErdosProblems.Erdos207.VortexNibbleExponentSplit

/-! # Forward exposure and the exceptional reverse-order branch -/

namespace Erdos207.GainDefectWitness

open Finset

noncomputable section

variable {W : Type*} [DecidableEq W] {F G : Finset (Finset W)} {T : W} {z : ℕ}

def firstExposureRoot (w : GainDefectWitness F G T z) (H : Finset W) : Finset W :=
  insert T (w.first ∩ H)

def secondExposureRoot (w : GainDefectWitness F G T z) (H : Finset W) : Finset W :=
  w.second ∩ (w.first ∪ H)

theorem firstExposureRoot_subset (w : GainDefectWitness F G T z) (H : Finset W) :
    w.firstExposureRoot H ⊆ w.first := insert_subset w.root_mem inter_subset_left

theorem root_not_mem_extension (w : GainDefectWitness F G T z) (H : Finset W)
    (hH : H ⊆ w.remainder) : T ∉ H := fun h ↦ w.root_not_mem_remainder (hH h)

theorem firstExposureRoot_card (w : GainDefectWitness F G T z) (H : Finset W)
    (hH : H ⊆ w.remainder) :
    (w.firstExposureRoot H).card = (w.first ∩ H).card + 1 := by
  rw [firstExposureRoot, card_insert_of_notMem]
  exact fun h ↦ w.root_not_mem_extension H hH (mem_inter.mp h).2

theorem firstExposureRoot_card_lt (w : GainDefectWitness F G T z) (H : Finset W)
    (hH : H ⊆ w.remainder) (hz : 1 ≤ z) :
    (w.firstExposureRoot H).card < w.first.card := by
  have hnonempty : w.omitted.Nonempty := by rw [← card_pos, w.omitted_card]; omega
  obtain ⟨U, hU⟩ := hnonempty
  have hUF := mem_erase.mp (w.omitted_subset hU)
  have hUH : U ∉ H := fun h ↦ disjoint_left.mp w.disjoint_omittedRoot_remainder
    (mem_insert_of_mem hU) (hH h)
  apply card_lt_card
  apply ssubset_iff_subset_ne.mpr
  refine ⟨w.firstExposureRoot_subset H, ?_⟩
  intro heq
  have hm : U ∈ w.firstExposureRoot H := heq ▸ hUF.2
  rcases mem_insert.mp hm with h | h
  · exact hUF.1 h
  · exact hUH (mem_inter.mp h).2

theorem secondExposureRoot_card_ge_two (w : GainDefectWitness F G T z) (H : Finset W) :
    2 ≤ (w.secondExposureRoot H).card := by
  rw [← w.second_root_card]
  apply card_le_card
  intro x hx
  exact mem_inter.mpr ⟨(mem_inter.mp hx).1,
    mem_union_left _ (w.omittedRoot_subset_first (mem_inter.mp hx).2)⟩

theorem exposureRoot_card_add (w : GainDefectWitness F G T z) (H : Finset W)
    (hH : H ⊆ w.remainder) :
    (w.firstExposureRoot H).card + (w.secondExposureRoot H).card =
      H.card + (w.leftRemainder ∩ w.rightRemainder).card + 3 := by
  have hsub : H ⊆ w.first ∪ w.second := by
    rw [w.remainder_eq_sdiff] at hH
    exact hH.trans sdiff_subset
  have h := card_inter_add_card_inter_union_of_subset w.first w.second H hsub
  rw [w.inter_card] at h
  rw [w.firstExposureRoot_card H hH]
  change (w.first ∩ H).card + 1 + (w.second ∩ (w.first ∪ H)).card = _
  omega

def ForwardExceptional (w : GainDefectWitness F G T z) (H : Finset W) : Prop :=
  Disjoint w.first H ∧ w.second ⊆ w.first ∪ H ∧ H.Nonempty

theorem forwardExceptional_of_root_card
    (w : GainDefectWitness F G T z) (H : Finset W) (hH : H ⊆ w.remainder)
    (ha : (w.firstExposureRoot H).card = 1)
    (hb : (w.secondExposureRoot H).card = w.second.card) : w.ForwardExceptional H := by
  have hzero : (w.first ∩ H).card = 0 := by
    rw [w.firstExposureRoot_card H hH] at ha
    omega
  have hdis : Disjoint w.first H := disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp hzero)
  have hfull : w.secondExposureRoot H = w.second :=
    eq_of_subset_of_card_le inter_subset_left (by omega)
  have hsub : w.second ⊆ w.first ∪ H := by
    intro x hx
    have hh : x ∈ w.secondExposureRoot H := hfull ▸ hx
    exact (mem_inter.mp hh).2
  refine ⟨hdis, hsub, ?_⟩
  by_contra he
  have hEmpty := not_nonempty_iff_eq_empty.mp he
  exact w.not_subset (by simpa [hEmpty] using hsub)

theorem exposure_exponent_or_forwardExceptional
    (w : GainDefectWitness F G T z) (H : Finset W) (hH : H ⊆ w.remainder)
    (hz : 1 ≤ z) (r s : ℕ) (hfirst : w.first.card = r - 2) (hsecond : w.second.card = s - 2) :
    H.card + (w.leftRemainder ∩ w.rightRemainder).card + 8 ≤
        vortexRootExponent r (w.firstExposureRoot H).card +
          vortexRootExponent s (w.secondExposureRoot H).card ∨ w.ForwardExceptional H := by
  have ha : (w.firstExposureRoot H).card < r - 2 := by
    rw [← hfirst]
    exact w.firstExposureRoot_card_lt H hH hz
  rcases vortexRootExponent_pair_nibble_split ha (w.secondExposureRoot_card_ge_two H)
    (w.exposureRoot_card_add H hH) with h | h
  · exact Or.inl h
  · exact Or.inr (w.forwardExceptional_of_root_card H hH h.1 (h.2.trans hsecond.symm))

end

end Erdos207.GainDefectWitness
