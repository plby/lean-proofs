/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CommonThreatExposure

/-! # Ordering exposures forces the exceptional branch into sharp W2 -/

namespace Erdos207.CommonThreatWitness

open Finset

noncomputable section

variable {W : Type*} [DecidableEq W] {F G : Finset (Finset W)} {T T' : W}

def swap (w : CommonThreatWitness F G T T') : CommonThreatWitness G F T' T where
  bridge := w.bridge
  first := w.second
  second := w.first
  first_mem := w.second_mem
  second_mem := w.first_mem
  first_root := w.second_root
  second_root := w.first_root
  bridge_first := w.bridge_second
  bridge_second := w.bridge_first
  bridge_ne_first := w.bridge_ne_second
  bridge_ne_second := w.bridge_ne_first
  first_cross := w.second_cross
  second_cross := w.first_cross
  different := w.different.symm

def OrderedAt (w : CommonThreatWitness F G T T') (H : Finset W) : Prop :=
  (w.rightRemainder ∩ H).card ≤ (w.leftRemainder ∩ H).card ∧
    ((w.leftRemainder ∩ H).card = (w.rightRemainder ∩ H).card → w.first.card ≤ w.second.card)

theorem orderedAt_or_swap (w : CommonThreatWitness F G T T') (H : Finset W) :
    w.OrderedAt H ∨ w.swap.OrderedAt H := by
  dsimp only [OrderedAt, swap, leftRemainder, rightRemainder]
  omega

theorem exceptional_exposure_has_equal_remainders
    (w : CommonThreatWitness F G T T') (H : Finset W)
    (hH : H ⊆ w.remainder) (horder : w.OrderedAt H)
    (hfirst : (w.firstExposureRoot H).card = 1)
    (hsecond : (w.secondExposureRoot H).card = w.second.card) :
    H = ∅ ∧ w.first.erase T = w.second.erase T' := by
  have hA : (w.leftRemainder ∩ H).card = 0 := by
    rw [w.firstExposureRoot_card] at hfirst
    omega
  have hB : (w.rightRemainder ∩ H).card = 0 := by
    have h := horder.1
    omega
  have hHempty : H = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    rcases mem_union.mp (hH hx) with hleft | hright
    · have hmem : x ∈ w.leftRemainder ∩ H := mem_inter.mpr ⟨hleft, hx⟩
      rw [card_eq_zero.mp hA] at hmem
      simp at hmem
    · have hmem : x ∈ w.rightRemainder ∩ H := mem_inter.mpr ⟨hright, hx⟩
      rw [card_eq_zero.mp hB] at hmem
      simp at hmem
  have hsize : w.first.card ≤ w.second.card := horder.2 (by omega)
  have hinter : (w.rightRemainder ∩ w.leftRemainder).card = w.rightRemainder.card := by
    rw [w.secondExposureRoot_card, hHempty, union_empty] at hsecond
    rw [w.rightRemainder_card]
    omega
  have hBsub : w.rightRemainder ⊆ w.leftRemainder := by
    have heq : w.rightRemainder ∩ w.leftRemainder = w.rightRemainder :=
      eq_of_subset_of_card_le inter_subset_left hinter.ge
    intro x hx
    exact (mem_inter.mp (heq ▸ hx)).2
  have hremainders : w.leftRemainder = w.rightRemainder := by
    symm
    apply eq_of_subset_of_card_le hBsub
    rw [w.leftRemainder_card, w.rightRemainder_card]
    exact Nat.sub_le_sub_right hsize 2
  refine ⟨hHempty, ?_⟩
  calc
    w.first.erase T = insert w.bridge w.leftRemainder :=
      (insert_erase (mem_erase.mpr ⟨w.bridge_ne_first, w.bridge_first⟩)).symm
    _ = insert w.bridge w.rightRemainder := by rw [hremainders]
    _ = w.second.erase T' := insert_erase (mem_erase.mpr ⟨w.bridge_ne_second, w.bridge_second⟩)

theorem ordered_exponent_or_equal_remainders
    (w : CommonThreatWitness F G T T') (H : Finset W)
    (hH : H ⊆ w.remainder) (horder : w.OrderedAt H)
    (r s : ℕ) (hfirst : w.first.card = r - 2) (hsecond : w.second.card = s - 2) :
    H.card + (w.leftRemainder ∩ w.rightRemainder).card + 8 ≤
        vortexRootExponent r (w.firstExposureRoot H).card +
          vortexRootExponent s (w.secondExposureRoot H).card ∨
      (H = ∅ ∧ r = s ∧ w.first.erase T = w.second.erase T') := by
  rcases w.exposureRoot_exponent_split H hH r s hfirst with h | h
  · exact Or.inl h
  · obtain ⟨hHempty, hrem⟩ := w.exceptional_exposure_has_equal_remainders H hH horder h.1
      (h.2.trans hsecond.symm)
    have hcard := congrArg Finset.card hrem
    rw [card_erase_of_mem w.first_root, card_erase_of_mem w.second_root] at hcard
    have hp : 0 < w.first.card := card_pos.mpr ⟨T, w.first_root⟩
    have hp' : 0 < w.second.card := card_pos.mpr ⟨T', w.second_root⟩
    exact Or.inr ⟨hHempty, by omega, hrem⟩

/-- In the nonexceptional branch, the two polynomial counting exponents
are fully paid for by the cardinality of the selected remainder. -/
theorem exposure_exponents_le_remainder_card
    (w : CommonThreatWitness F G T T') (H : Finset W)
    (hH : H ⊆ w.remainder) (r s : ℕ)
    (hfirst : w.first.card = r - 2) (hsecond : w.second.card = s - 2)
    (hbudget : H.card + (w.leftRemainder ∩ w.rightRemainder).card + 8 ≤
      vortexRootExponent r (w.firstExposureRoot H).card +
        vortexRootExponent s (w.secondExposureRoot H).card) :
    (r - vortexRootExponent r (w.firstExposureRoot H).card) +
      (s - vortexRootExponent s (w.secondExposureRoot H).card) ≤ (w.remainder \ H).card := by
  have ha1 : 1 ≤ (w.firstExposureRoot H).card := by rw [w.firstExposureRoot_card]; omega
  have ha : (w.firstExposureRoot H).card ≤ r - 2 := by
    rw [← hfirst]
    exact card_le_card (w.firstExposureRoot_subset H)
  have hb1 : 1 ≤ (w.secondExposureRoot H).card := by rw [w.secondExposureRoot_card]; omega
  have hb : (w.secondExposureRoot H).card ≤ s - 2 := by
    rw [← hsecond, w.secondExposureRoot_eq_inter]
    exact card_le_card inter_subset_left
  have hva := vortexRootExponent_le_order ha1 ha
  have hvb := vortexRootExponent_le_order hb1 hb
  have hf2 : 2 ≤ w.first.card := Nat.succ_le_of_lt (one_lt_card.mpr
    ⟨T, w.first_root, w.bridge, w.bridge_first, w.bridge_ne_first.symm⟩)
  have hs2 : 2 ≤ w.second.card := Nat.succ_le_of_lt (one_lt_card.mpr
    ⟨T', w.second_root, w.bridge, w.bridge_second, w.bridge_ne_second.symm⟩)
  have hsum := card_union_add_card_inter w.leftRemainder w.rightRemainder
  rw [w.leftRemainder_card, w.rightRemainder_card, hfirst, hsecond] at hsum
  have hsubcard := card_sdiff_add_card_eq_card hH
  change (w.remainder \ H).card + H.card = w.remainder.card at hsubcard
  change w.remainder.card + (w.leftRemainder ∩ w.rightRemainder).card = _ at hsum
  omega

end

end Erdos207.CommonThreatWitness
