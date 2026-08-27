/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CommonThreatOrdering

/-! # Fixed exposure classes retain the bridge multiplicity -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def commonThreatExposureClass
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T T' : W) (H Q Q' : Finset W) (b k : ℕ) :
    Finset (CommonThreatWitness F G T T') := by
  classical
  exact univ.filter fun w ↦ H ⊆ w.remainder ∧ w.firstExposureRoot H = Q ∧
    insert T' (w.second ∩ H) = Q' ∧ (w.secondExposureRoot H).card = b ∧
    (w.leftRemainder ∩ w.rightRemainder).card = k

def commonThreatExposureClassEmbedding
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T T' : W) (H Q Q' : Finset W) (b k : ℕ) :
    commonThreatExposureClass F G T T' H Q Q' b k ↪
      Σ p : rootedTwoFamilyExtensions F G Q Q' b, p.1.1 := by
  classical
  let pairCode : commonThreatExposureClass F G T T' H Q Q' b k →
      rootedTwoFamilyExtensions F G Q Q' b := fun w ↦ by
    rcases w with ⟨w, hw⟩
    have hw := (mem_filter.mp hw).2
    refine ⟨(w.first, w.second), mem_rootedTwoFamilyExtensions_iff.mpr ?_⟩
    refine ⟨w.first_mem, ?_, w.second_mem, ?_, ?_⟩
    · rw [← hw.2.1]
      exact w.firstExposureRoot_subset H
    · rw [← hw.2.2.1]
      exact insert_subset w.second_root inter_subset_left
    · rw [← hw.2.2.1, ← w.secondExposureRoot_eq_inter H]
      exact hw.2.2.2.1
  refine ⟨fun w ↦ ⟨pairCode w, ⟨w.1.bridge, w.1.bridge_first⟩⟩, ?_⟩
  intro w z h
  have hfirst : w.1.first = z.1.first := congrArg (fun p ↦ p.1.1.1) h
  have hsecond : w.1.second = z.1.second := congrArg (fun p ↦ p.1.1.2) h
  have hbridge : w.1.bridge = z.1.bridge := congrArg (fun p ↦ p.2.1) h
  apply Subtype.ext
  rcases w with ⟨w, hw⟩
  rcases z with ⟨z, hz⟩
  cases w
  cases z
  simp_all

theorem card_commonThreatExposureClass_le
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T T' : W) (H Q Q' : Finset W) (b k m : ℕ)
    (hcard : ∀ E ∈ F, E.card = m) :
    (commonThreatExposureClass F G T T' H Q Q' b k).card ≤
      (rootedTwoFamilyExtensions F G Q Q' b).card * m := by
  calc
    _ = Fintype.card (commonThreatExposureClass F G T T' H Q Q' b k) :=
      (Fintype.card_coe _).symm
    _ ≤ Fintype.card (Σ p : rootedTwoFamilyExtensions F G Q Q' b, p.1.1) :=
      Fintype.card_le_of_embedding (commonThreatExposureClassEmbedding F G T T' H Q Q' b k)
    _ = ∑ p : rootedTwoFamilyExtensions F G Q Q' b, p.1.1.card := by simp
    _ = ∑ _p : rootedTwoFamilyExtensions F G Q Q' b, m := by
      apply sum_congr rfl
      intro p _
      exact hcard p.1.1 (mem_rootedTwoFamilyExtensions_iff.mp p.2).1
    _ = _ := by simp

def commonThreatExposureClassWeight
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T T' : W) (H Q Q' : Finset W) (b k : ℕ) (p : ℝ≥0) : ℝ≥0 :=
  ∑ w ∈ commonThreatExposureClass F G T T' H Q Q' b k, p ^ (w.remainder \ H).card

theorem commonThreatExposureClassWeight_eq
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T T' : W) (H Q Q' : Finset W)
    (b k m n : ℕ) (p : ℝ≥0)
    (hF : ∀ E ∈ F, E.card = m) (hG : ∀ E ∈ G, E.card = n) :
    commonThreatExposureClassWeight F G T T' H Q Q' b k p =
      (commonThreatExposureClass F G T T' H Q Q' b k).card *
        p ^ ((m - 2) + (n - 2) - k - H.card) := by
  classical
  unfold commonThreatExposureClassWeight
  calc
    _ = ∑ _w ∈ commonThreatExposureClass F G T T' H Q Q' b k,
        p ^ ((m - 2) + (n - 2) - k - H.card) := by
      apply sum_congr rfl
      intro w hw
      have h := (mem_filter.mp hw).2
      rw [w.remainder_sdiff_card H h.1, hF w.first w.first_mem, hG w.second w.second_mem,
        h.2.2.2.2]
    _ = _ := by simp

theorem commonThreatExposureClassWeight_le_pair_weight
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T T' : W) (H Q Q' : Finset W)
    (b k m n : ℕ) (p : ℝ≥0)
    (hF : ∀ E ∈ F, E.card = m) (hG : ∀ E ∈ G, E.card = n) :
    commonThreatExposureClassWeight F G T T' H Q Q' b k p ≤
      m * ((rootedTwoFamilyExtensions F G Q Q' b).card *
        p ^ ((m - 2) + (n - 2) - k - H.card)) := by
  rw [commonThreatExposureClassWeight_eq F G T T' H Q Q' b k m n p hF hG]
  have hcast : ((commonThreatExposureClass F G T T' H Q Q' b k).card : ℝ≥0) ≤
      (rootedTwoFamilyExtensions F G Q Q' b).card * (m : ℝ≥0) := by
    exact_mod_cast card_commonThreatExposureClass_le F G T T' H Q Q' b k m hF
  calc
    _ ≤ ((rootedTwoFamilyExtensions F G Q Q' b).card * (m : ℝ≥0)) *
        p ^ ((m - 2) + (n - 2) - k - H.card) := mul_le_mul_of_nonneg_right hcast zero_le
    _ = _ := by ring

theorem commonThreatExposureClassWeight_le_of_root_bounds
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T T' : W) (H Q Q' : Finset W)
    (b k m n N A B a e : ℕ)
    (hF : ∀ E ∈ F, E.card = m) (hG : ∀ E ∈ G, E.card = n)
    (hfirst : (familyExtensions F Q).card ≤ A * N ^ a)
    (hsecond : ∀ R : Finset W, R.card = b → (familyExtensions G R).card ≤ B * N ^ e)
    (hN : 1 ≤ N) (hexp : a + e ≤ (m - 2) + (n - 2) - k - H.card) :
    commonThreatExposureClassWeight F G T T' H Q Q' b k (N : ℝ≥0)⁻¹ ≤
      m * ((A : ℝ≥0) * 2 ^ (m + Q'.card) * B) := by
  refine (commonThreatExposureClassWeight_le_pair_weight F G T T' H Q Q' b k m n
    (N : ℝ≥0)⁻¹ hF hG).trans ?_
  apply mul_le_mul_of_nonneg_left _ zero_le
  exact rootedTwoFamilyExtensions_card_mul_inv_pow_le F G Q Q' b m A B N a e
    ((m - 2) + (n - 2) - k - H.card) (fun E hE ↦ (hF E hE).le)
    hfirst hsecond hN hexp

end

end Erdos207
