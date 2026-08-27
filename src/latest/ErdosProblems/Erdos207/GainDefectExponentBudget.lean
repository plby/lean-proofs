/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GainDefectReverseExposure

/-! # Paying for two configuration counts with the fourth-moment remainder -/

namespace Erdos207.GainDefectWitness

open Finset

noncomputable section

variable {W : Type*} [DecidableEq W] {F G : Finset (Finset W)} {T : W} {z : ℕ}

theorem forward_exponents_le_remainder_add
    (w : GainDefectWitness F G T z) (H : Finset W) (hH : H ⊆ w.remainder)
    (hz : 1 ≤ z) (r s : ℕ) (hf : w.first.card = r - 2) (hs : w.second.card = s - 2)
    (hb : H.card + (w.leftRemainder ∩ w.rightRemainder).card + 8 ≤
      vortexRootExponent r (w.firstExposureRoot H).card +
        vortexRootExponent s (w.secondExposureRoot H).card) :
    (r - vortexRootExponent r (w.firstExposureRoot H).card) +
      (s - vortexRootExponent s (w.secondExposureRoot H).card) ≤
        (w.remainder \ H).card + (z - 1) := by
  have hfa : 1 ≤ (w.firstExposureRoot H).card := by
    rw [w.firstExposureRoot_card H hH]; omega
  have hfb : (w.firstExposureRoot H).card ≤ r - 2 := by
    rw [← hf]; exact card_le_card (w.firstExposureRoot_subset H)
  have hsa := w.secondExposureRoot_card_ge_two H
  have hsb : (w.secondExposureRoot H).card ≤ s - 2 := by
    rw [← hs]; exact card_le_card inter_subset_left
  have hvr := vortexRootExponent_le_order hfa hfb
  have hvs := vortexRootExponent_le_order (by omega : 1 ≤ (w.secondExposureRoot H).card) hsb
  have hzfirst := card_le_card w.omittedRoot_subset_first
  rw [w.omittedRoot_card, hf] at hzfirst
  rw [w.remainder_sdiff_card H hH, hf, hs]
  omega

theorem reverse_exponents_le_remainder_add
    (w : GainDefectWitness F G T z) (H : Finset W) (hH : H ⊆ w.remainder)
    (he : w.ForwardExceptional H) (hz : 1 ≤ z)
    (r s : ℕ) (hf : w.first.card = r - 2) (hs : w.second.card = s - 2)
    (hb : s + 4 ≤ vortexRootExponent r w.reverseFirstRoot.card +
      vortexRootExponent s (w.reverseSecondRoot H).card) :
    (r - vortexRootExponent r w.reverseFirstRoot.card) +
      (s - vortexRootExponent s (w.reverseSecondRoot H).card) ≤
        (w.remainder \ H).card + (z - 1) := by
  have hfa := w.reverseFirstRoot_card_ge_two
  have hfb : w.reverseFirstRoot.card ≤ r - 2 := by
    rw [← hf]; exact card_le_card w.reverseFirstRoot_subset
  have hsa : 1 ≤ (w.reverseSecondRoot H).card := by
    have hh := card_pos.mpr he.2.2
    have hle : H.card ≤ (w.reverseSecondRoot H).card := card_le_card subset_union_left
    omega
  have hsb : (w.reverseSecondRoot H).card ≤ s - 2 := by
    rw [← hs]; exact card_le_card (w.reverseSecondRoot_subset H hH he)
  have hvr := vortexRootExponent_le_order (by omega : 1 ≤ w.reverseFirstRoot.card) hfb
  have hvs := vortexRootExponent_le_order hsa hsb
  have hzfirst := card_le_card w.omittedRoot_subset_first
  rw [w.omittedRoot_card, hf] at hzfirst
  rw [w.remainder_sdiff_eq_left_of_forwardExceptional H he, w.leftRemainder_card, hf]
  omega

theorem equal_remainders_orders_eq
    (w : GainDefectWitness F G T z) (H : Finset W) (hH : H ⊆ w.remainder)
    (he : w.ForwardExceptional H) (hcard : H.card = 1)
    (hrem : w.second \ H = w.first.erase T)
    (r s : ℕ) (hf : w.first.card = r - 2) (hs : w.second.card = s - 2) : r = s := by
  have hc := congrArg Finset.card hrem
  rw [card_sdiff_of_subset (w.extension_subset_second_of_forwardExceptional H hH he),
    hcard, card_erase_of_mem w.root_mem, hf, hs] at hc
  have hp : 0 < w.first.card := card_pos.mpr ⟨T, w.root_mem⟩
  have hp' : 0 < w.second.card :=
    lt_of_lt_of_le (by omega : 0 < H.card)
      (card_le_card (w.extension_subset_second_of_forwardExceptional H hH he))
  omega

/-- Exhaustive source-correct alternatives; the third case is handled by W2. -/
theorem exposure_three_way_split
    (w : GainDefectWitness F G T z) (H : Finset W) (hH : H ⊆ w.remainder)
    (hz : 1 ≤ z) (r s : ℕ) (hf : w.first.card = r - 2) (hs : w.second.card = s - 2) :
    (H.card + (w.leftRemainder ∩ w.rightRemainder).card + 8 ≤
      vortexRootExponent r (w.firstExposureRoot H).card +
        vortexRootExponent s (w.secondExposureRoot H).card) ∨
    (w.ForwardExceptional H ∧ s + 4 ≤ vortexRootExponent r w.reverseFirstRoot.card +
      vortexRootExponent s (w.reverseSecondRoot H).card) ∨
    (w.ForwardExceptional H ∧ H.card = 1 ∧ r = s ∧ T ∉ w.second ∧
      w.second \ H = w.first.erase T) := by
  rcases w.exposure_exponent_or_forwardExceptional H hH hz r s hf hs with hb | he
  · exact Or.inl hb
  rcases w.reverse_exponent_or_equal_remainders H hH he r s hf hs with hb | hx
  · exact Or.inr (Or.inl ⟨he, hb⟩)
  · exact Or.inr (Or.inr ⟨he, hx.1, w.equal_remainders_orders_eq H hH he hx.1 hx.2.2 r s hf hs,
      hx.2.1, hx.2.2⟩)

end

end Erdos207.GainDefectWitness
