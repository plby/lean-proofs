/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CommonThreatWeightSplit
import ErdosProblems.Erdos207.EqualRemainderOmissionWeight

/-! # Injecting the exceptional common-threat case into off-diagonal W2 -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def exceptionalCommonThreats
    {W : Type*} [Fintype W] [DecidableEq W]
    (F : Finset (Finset W)) (T T' : W) : Finset (CommonThreatWitness F F T T') := by
  classical
  exact univ.filter fun w ↦ w.first.erase T = w.second.erase T'

def exceptionalCommonThreatEmbedding
    {W : Type*} [Fintype W] [DecidableEq W]
    (F : Finset (Finset W)) (T T' : W) :
    exceptionalCommonThreats F T T' ↪ equalRemainderOmissionCodes F T T' 1 := by
  classical
  refine ⟨fun w ↦ ⟨((w.1.first, w.1.second), {w.1.bridge}), ?_⟩, ?_⟩
  · apply mem_equalRemainderOmissionCodes_iff.mpr
    refine ⟨mem_distinctEqualRemainderPairs_iff.mpr
      ⟨w.1.first_mem, w.1.second_mem, w.1.different, w.1.first_root, w.1.second_root,
        (mem_filter.mp w.2).2⟩, ?_, card_singleton _⟩
    exact singleton_subset_iff.mpr (mem_erase.mpr ⟨w.1.bridge_ne_first, w.1.bridge_first⟩)
  · intro w z h
    have hfirst : w.1.first = z.1.first := congrArg (fun u ↦ u.1.1.1) h
    have hsecond : w.1.second = z.1.second := congrArg (fun u ↦ u.1.1.2) h
    have hbridge : w.1.bridge = z.1.bridge :=
      singleton_injective (congrArg (fun u ↦ u.1.2) h)
    apply Subtype.ext
    rcases w with ⟨w, hw⟩
    rcases z with ⟨z, hz⟩
    cases w
    cases z
    simp_all

theorem commonThreat_remainder_eq_left_of_equal_remainders
    {W : Type*} [DecidableEq W] {F G : Finset (Finset W)} {T T' : W}
    (w : CommonThreatWitness F G T T') (h : w.first.erase T = w.second.erase T') :
    w.remainder = w.leftRemainder := by
  unfold CommonThreatWitness.remainder CommonThreatWitness.leftRemainder CommonThreatWitness.rightRemainder
  rw [h, union_self]

theorem commonThreatExceptionalWeight_le_omissionWeight
    {W : Type*} [Fintype W] [DecidableEq W]
    (F : Finset (Finset W)) (T T' : W) (H : Finset W) (m : ℕ) (p : ℝ≥0)
    (hF : ∀ E ∈ F, E.card = m) :
    commonThreatExceptionalWeight F F T T' H p ≤ equalRemainderOmissionWeight F T T' 1 p := by
  classical
  by_cases hH : H = ∅
  · subst H
    have hcard : (exceptionalCommonThreats F T T').card ≤
        (equalRemainderOmissionCodes F T T' 1).card := by
      rw [← Fintype.card_coe, ← Fintype.card_coe]
      exact Fintype.card_le_of_embedding (exceptionalCommonThreatEmbedding F T T')
    have hweight : commonThreatExceptionalWeight F F T T' ∅ p =
        (exceptionalCommonThreats F T T').card * p ^ (m - 2) := by
      unfold commonThreatExceptionalWeight
      simp only [true_and, sdiff_empty]
      rw [← sum_filter]
      change (∑ w ∈ exceptionalCommonThreats F T T', p ^ w.remainder.card) = _
      calc
        _ = ∑ _w ∈ exceptionalCommonThreats F T T', p ^ (m - 2) := by
          apply sum_congr rfl
          intro w hw
          rw [commonThreat_remainder_eq_left_of_equal_remainders w (mem_filter.mp hw).2,
            w.leftRemainder_card, hF w.first w.first_mem]
        _ = _ := by simp
    rw [hweight, equalRemainderOmissionWeight_eq F T T' 1 m p hF]
    have he : m - 1 - 1 = m - 2 := by omega
    rw [he]
    apply mul_le_mul_of_nonneg_right _ zero_le
    exact_mod_cast hcard
  · simp only [commonThreatExceptionalWeight, hH, false_and, if_false, sum_const_zero]
    exact zero_le

theorem commonThreatExceptionalWeight_eq_zero_of_orders_ne
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T T' : W) (H : Finset W) (r s : ℕ) (p : ℝ≥0)
    (hF : ∀ E ∈ F, E.card = r - 2) (hG : ∀ E ∈ G, E.card = s - 2) (hne : r ≠ s) :
    commonThreatExceptionalWeight F G T T' H p = 0 := by
  classical
  have hnot : ∀ w : CommonThreatWitness F G T T', w.first.erase T ≠ w.second.erase T' := by
    intro w heq
    have hcard := congrArg Finset.card heq
    rw [card_erase_of_mem w.first_root, card_erase_of_mem w.second_root,
      hF w.first w.first_mem, hG w.second w.second_mem] at hcard
    have hp : 0 < w.first.card := card_pos.mpr ⟨T, w.first_root⟩
    have hp' : 0 < w.second.card := card_pos.mpr ⟨T', w.second_root⟩
    rw [hF w.first w.first_mem] at hp
    rw [hG w.second w.second_mem] at hp'
    exact hne (by omega)
  simp only [commonThreatExceptionalWeight, hnot, and_false, if_false, sum_const_zero]

end

end Erdos207
