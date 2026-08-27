/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CommonThreatWitness
import ErdosProblems.Erdos207.VortexNibbleExponentSplit

/-! # The two exposed roots and the third-moment exponent alternative -/

namespace Erdos207.CommonThreatWitness

open Finset

noncomputable section

variable {W : Type*} [DecidableEq W] {F G : Finset (Finset W)} {T T' : W}

def firstExposureRoot (w : CommonThreatWitness F G T T') (H : Finset W) : Finset W :=
  insert T (w.leftRemainder ∩ H)

def secondExposureRoot (w : CommonThreatWitness F G T T') (H : Finset W) : Finset W :=
  insert T' (insert w.bridge (w.rightRemainder ∩ (w.leftRemainder ∪ H)))

theorem firstExposureRoot_subset (w : CommonThreatWitness F G T T') (H : Finset W) :
    w.firstExposureRoot H ⊆ w.first := by
  apply insert_subset w.first_root
  intro x hx
  exact mem_of_mem_erase (mem_of_mem_erase (mem_inter.mp hx).1)

theorem bridge_not_mem_firstExposureRoot (w : CommonThreatWitness F G T T') (H : Finset W) :
    w.bridge ∉ w.firstExposureRoot H := by
  intro h
  rcases mem_insert.mp h with h | h
  · exact w.bridge_ne_first h
  · exact (mem_erase.mp (mem_inter.mp h).1).1 rfl

theorem firstExposureRoot_card_lt (w : CommonThreatWitness F G T T') (H : Finset W) :
    (w.firstExposureRoot H).card < w.first.card := by
  apply card_lt_card
  apply ssubset_iff_subset_ne.mpr
  refine ⟨w.firstExposureRoot_subset H, ?_⟩
  intro heq
  exact w.bridge_not_mem_firstExposureRoot H (heq ▸ w.bridge_first)

theorem firstExposureRoot_card (w : CommonThreatWitness F G T T') (H : Finset W) :
    (w.firstExposureRoot H).card = 1 + (w.leftRemainder ∩ H).card := by
  have hnot : T ∉ w.leftRemainder ∩ H := by
    intro h
    exact (mem_erase.mp (mem_erase.mp (mem_inter.mp h).1).2).1 rfl
  rw [firstExposureRoot, card_insert_of_notMem hnot]
  omega

theorem secondExposureRoot_card (w : CommonThreatWitness F G T T') (H : Finset W) :
    (w.secondExposureRoot H).card = 2 + (w.rightRemainder ∩ (w.leftRemainder ∪ H)).card := by
  have hbridge : w.bridge ∉ w.rightRemainder ∩ (w.leftRemainder ∪ H) := by
    intro h
    exact (mem_erase.mp (mem_inter.mp h).1).1 rfl
  have hroot : T' ∉ insert w.bridge (w.rightRemainder ∩ (w.leftRemainder ∪ H)) := by
    intro h
    rcases mem_insert.mp h with h | h
    · exact w.bridge_ne_second h.symm
    · exact (mem_erase.mp (mem_erase.mp (mem_inter.mp h).1).2).1 rfl
  rw [secondExposureRoot, card_insert_of_notMem hroot, card_insert_of_notMem hbridge]
  omega

theorem secondExposureRoot_eq_inter (w : CommonThreatWitness F G T T') (H : Finset W) :
    w.secondExposureRoot H = w.second ∩ (w.first ∪ insert T' (w.second ∩ H)) := by
  ext x
  constructor
  · intro hx
    rcases mem_insert.mp hx with rfl | hx
    · exact mem_inter.mpr ⟨w.second_root, mem_union_right _ (mem_insert_self _ _)⟩
    rcases mem_insert.mp hx with rfl | hx
    · exact mem_inter.mpr ⟨w.bridge_second, mem_union_left _ w.bridge_first⟩
    obtain ⟨hB, hAH⟩ := mem_inter.mp hx
    have hsecond := mem_of_mem_erase (mem_of_mem_erase hB)
    refine mem_inter.mpr ⟨hsecond, ?_⟩
    rcases mem_union.mp hAH with hA | hH
    · exact mem_union_left _ (mem_of_mem_erase (mem_of_mem_erase hA))
    · exact mem_union_right _ (mem_insert_of_mem (mem_inter.mpr ⟨hsecond, hH⟩))
  · intro hx
    obtain ⟨hsecond, hrest⟩ := mem_inter.mp hx
    by_cases hxT' : x = T'
    · subst x
      exact mem_insert_self _ _
    by_cases hxb : x = w.bridge
    · subst x
      exact mem_insert_of_mem (mem_insert_self _ _)
    apply mem_insert_of_mem
    apply mem_insert_of_mem
    refine mem_inter.mpr ⟨mem_erase.mpr ⟨hxb, mem_erase.mpr ⟨hxT', hsecond⟩⟩, ?_⟩
    rcases mem_union.mp hrest with hfirst | hrootH
    · have hxT : x ≠ T := by
        intro h
        subst x
        exact hxT' (w.second_cross hsecond)
      exact mem_union_left _ (mem_erase.mpr ⟨hxb, mem_erase.mpr ⟨hxT, hfirst⟩⟩)
    · rcases mem_insert.mp hrootH with hroot | hH
      · exact (hxT' hroot).elim
      · exact mem_union_right _ (mem_inter.mp hH).2

theorem firstExposureRoot_eq_insert_inter (w : CommonThreatWitness F G T T') (H : Finset W)
    (hH : H ⊆ w.remainder) :
    w.firstExposureRoot H = insert T (w.first ∩ H) := by
  ext x
  constructor
  · intro hx
    rcases mem_insert.mp hx with rfl | hx
    · exact mem_insert_self _ _
    exact mem_insert_of_mem (mem_inter.mpr
      ⟨mem_of_mem_erase (mem_of_mem_erase (mem_inter.mp hx).1), (mem_inter.mp hx).2⟩)
  · intro hx
    rcases mem_insert.mp hx with rfl | hx
    · exact mem_insert_self _ _
    obtain ⟨hfirst, hmemH⟩ := mem_inter.mp hx
    have hxT : x ≠ T := by intro heq; subst x; exact w.first_not_mem_remainder (hH hmemH)
    have hxb : x ≠ w.bridge := by intro heq; subst x; exact w.bridge_not_mem_remainder (hH hmemH)
    exact mem_insert_of_mem (mem_inter.mpr
      ⟨mem_erase.mpr ⟨hxb, mem_erase.mpr ⟨hxT, hfirst⟩⟩, hmemH⟩)

theorem exposureRoot_card_add (w : CommonThreatWitness F G T T') (H : Finset W)
    (hH : H ⊆ w.remainder) :
    (w.firstExposureRoot H).card + (w.secondExposureRoot H).card =
      H.card + (w.leftRemainder ∩ w.rightRemainder).card + 3 := by
  rw [w.firstExposureRoot_card, w.secondExposureRoot_card]
  have h := card_inter_add_card_inter_union_of_subset w.leftRemainder w.rightRemainder H hH
  omega

theorem exposureRoot_exponent_split (w : CommonThreatWitness F G T T') (H : Finset W)
    (hH : H ⊆ w.remainder) (r s : ℕ) (hfirst : w.first.card = r - 2) :
    H.card + (w.leftRemainder ∩ w.rightRemainder).card + 8 ≤
        vortexRootExponent r (w.firstExposureRoot H).card +
          vortexRootExponent s (w.secondExposureRoot H).card ∨
      ((w.firstExposureRoot H).card = 1 ∧ (w.secondExposureRoot H).card = s - 2) := by
  have ha : (w.firstExposureRoot H).card < r - 2 := by
    rw [← hfirst]
    exact w.firstExposureRoot_card_lt H
  have hb : 2 ≤ (w.secondExposureRoot H).card := by rw [w.secondExposureRoot_card]; omega
  exact vortexRootExponent_pair_nibble_split ha hb (w.exposureRoot_card_add H hH)

end

end Erdos207.CommonThreatWitness
