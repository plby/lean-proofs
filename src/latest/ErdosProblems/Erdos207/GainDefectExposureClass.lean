/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GainDefectExponentBudget
import ErdosProblems.Erdos207.TwoFamilyRootExposurePower

/-! # Fixed forward exposure classes retain every omission set -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def gainDefectExposureClass
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T : W) (z : ℕ) (H Q Q' : Finset W) (b k : ℕ) :
    Finset (GainDefectWitness F G T z) := by
  classical
  exact univ.filter fun w ↦ H ⊆ w.remainder ∧ w.firstExposureRoot H = Q ∧
    w.second ∩ H = Q' ∧ (w.secondExposureRoot H).card = b ∧
    (w.leftRemainder ∩ w.rightRemainder).card = k

def gainDefectExposureClassEmbedding
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T : W) (z : ℕ) (H Q Q' : Finset W) (b k : ℕ) :
    gainDefectExposureClass F G T z H Q Q' b k ↪
      Σ p : rootedTwoFamilyExtensions F G Q Q' b, p.1.1.powerset := by
  classical
  let code : gainDefectExposureClass F G T z H Q Q' b k →
      rootedTwoFamilyExtensions F G Q Q' b := fun u ↦ by
    rcases u with ⟨w, hw⟩
    have h := (mem_filter.mp hw).2
    refine ⟨(w.first, w.second), mem_rootedTwoFamilyExtensions_iff.mpr
      ⟨w.first_mem, ?_, w.second_mem, ?_, ?_⟩⟩
    · rw [← h.2.1]; exact w.firstExposureRoot_subset H
    · rw [← h.2.2.1]; exact inter_subset_left
    · have he : w.second ∩ (w.first ∪ (w.second ∩ H)) = w.secondExposureRoot H := by
        ext x
        simp only [GainDefectWitness.secondExposureRoot, mem_inter, mem_union]
        tauto
      rw [← h.2.2.1, he]
      exact h.2.2.2.1
  refine ⟨fun w ↦ ⟨code w, ⟨w.1.omitted, mem_powerset.mpr
    (w.1.omitted_subset.trans (erase_subset T w.1.first))⟩⟩, ?_⟩
  intro w u h
  have hf : w.1.first = u.1.first := congrArg (fun p ↦ p.1.1.1) h
  have hs : w.1.second = u.1.second := congrArg (fun p ↦ p.1.1.2) h
  have ho : w.1.omitted = u.1.omitted := congrArg (fun p ↦ p.2.1) h
  apply Subtype.ext
  rcases w with ⟨w, hw⟩
  rcases u with ⟨u, hu⟩
  cases w
  cases u
  simp_all

theorem card_gainDefectExposureClass_le
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T : W) (z : ℕ) (H Q Q' : Finset W) (b k m : ℕ)
    (hF : ∀ E ∈ F, E.card = m) :
    (gainDefectExposureClass F G T z H Q Q' b k).card ≤
      (rootedTwoFamilyExtensions F G Q Q' b).card * 2 ^ m := by
  calc
    _ = Fintype.card (gainDefectExposureClass F G T z H Q Q' b k) := (Fintype.card_coe _).symm
    _ ≤ Fintype.card (Σ p : rootedTwoFamilyExtensions F G Q Q' b, p.1.1.powerset) :=
      Fintype.card_le_of_embedding (gainDefectExposureClassEmbedding F G T z H Q Q' b k)
    _ = ∑ p : rootedTwoFamilyExtensions F G Q Q' b, 2 ^ p.1.1.card := by
      simp only [Fintype.card_sigma, Fintype.card_coe, card_powerset]
    _ = ∑ _p : rootedTwoFamilyExtensions F G Q Q' b, 2 ^ m := by
      apply sum_congr rfl
      intro p _
      rw [hF p.1.1 (mem_rootedTwoFamilyExtensions_iff.mp p.2).1]
    _ = _ := by simp

def gainDefectExposureClassWeight
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T : W) (z : ℕ) (H Q Q' : Finset W) (b k : ℕ) (p : ℝ≥0) : ℝ≥0 :=
  ∑ w ∈ gainDefectExposureClass F G T z H Q Q' b k, p ^ (w.remainder \ H).card

theorem gainDefectExposureClassWeight_eq
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T : W) (z : ℕ) (H Q Q' : Finset W)
    (b k m n : ℕ) (p : ℝ≥0) (hF : ∀ E ∈ F, E.card = m) (hG : ∀ E ∈ G, E.card = n) :
    gainDefectExposureClassWeight F G T z H Q Q' b k p =
      (gainDefectExposureClass F G T z H Q Q' b k).card *
        p ^ ((m - (z + 1)) + (n - 2) - k - H.card) := by
  unfold gainDefectExposureClassWeight
  calc
    _ = ∑ _w ∈ gainDefectExposureClass F G T z H Q Q' b k,
        p ^ ((m - (z + 1)) + (n - 2) - k - H.card) := by
      apply sum_congr rfl
      intro w hw
      have h := (mem_filter.mp hw).2
      rw [w.remainder_sdiff_card H h.1, hF w.first w.first_mem, hG w.second w.second_mem,
        h.2.2.2.2]
    _ = _ := by simp

theorem gainDefectExposureClassWeight_le_of_root_bounds
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T : W) (z : ℕ) (H Q Q' : Finset W)
    (b k m n N A B a e d : ℕ)
    (hF : ∀ E ∈ F, E.card = m) (hG : ∀ E ∈ G, E.card = n)
    (hfirst : (familyExtensions F Q).card ≤ A * N ^ a)
    (hsecond : ∀ R : Finset W, R.card = b → (familyExtensions G R).card ≤ B * N ^ e)
    (hN : 1 ≤ N) (hexp : a + e ≤ (m - (z + 1)) + (n - 2) - k - H.card + d) :
    gainDefectExposureClassWeight F G T z H Q Q' b k (N : ℝ≥0)⁻¹ ≤
      (2 : ℝ≥0) ^ m * (((A : ℝ≥0) * 2 ^ (m + Q'.card) * B) * (N : ℝ≥0) ^ d) := by
  rw [gainDefectExposureClassWeight_eq F G T z H Q Q' b k m n _ hF hG]
  have hc : ((gainDefectExposureClass F G T z H Q Q' b k).card : ℝ≥0) ≤
      (rootedTwoFamilyExtensions F G Q Q' b).card * (2 : ℝ≥0) ^ m := by
    exact_mod_cast card_gainDefectExposureClass_le F G T z H Q Q' b k m hF
  calc
    _ ≤ ((rootedTwoFamilyExtensions F G Q Q' b).card * (2 : ℝ≥0) ^ m) *
        (N : ℝ≥0)⁻¹ ^ ((m - (z + 1)) + (n - 2) - k - H.card) :=
      mul_le_mul_of_nonneg_right hc zero_le
    _ = (2 : ℝ≥0) ^ m * ((rootedTwoFamilyExtensions F G Q Q' b).card *
        (N : ℝ≥0)⁻¹ ^ ((m - (z + 1)) + (n - 2) - k - H.card)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (rootedTwoFamilyExtensions_card_mul_inv_pow_le_pow F G Q Q' b m A B N a e
        ((m - (z + 1)) + (n - 2) - k - H.card) d (fun E hE ↦ (hF E hE).le)
        hfirst hsecond hN hexp) zero_le

end

end Erdos207
