/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GainDefectExponentBudget
import ErdosProblems.Erdos207.TwoFamilyRootExposurePower

/-! # Reverse exposure classes for fourth-moment witnesses -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def gainDefectReverseClass
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T : W) (z : ℕ) (H Q : Finset W) (b : ℕ) :
    Finset (GainDefectWitness F G T z) := by
  classical
  exact univ.filter fun w ↦ H ⊆ w.remainder ∧ w.ForwardExceptional H ∧
    w.reverseSecondRoot H = Q ∧ w.reverseFirstRoot.card = b

def gainDefectReverseClassEmbedding
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T : W) (z : ℕ) (H Q : Finset W) (b : ℕ) :
    gainDefectReverseClass F G T z H Q b ↪
      Σ p : rootedTwoFamilyExtensions G F Q {T} b, p.1.2.powerset := by
  classical
  let code : gainDefectReverseClass F G T z H Q b →
      rootedTwoFamilyExtensions G F Q {T} b := fun u ↦ by
    rcases u with ⟨w, hw⟩
    have h := (mem_filter.mp hw).2
    refine ⟨(w.second, w.first), mem_rootedTwoFamilyExtensions_iff.mpr
      ⟨w.second_mem, ?_, w.first_mem, singleton_subset_iff.mpr w.root_mem, ?_⟩⟩
    · rw [← h.2.2.1]
      exact w.reverseSecondRoot_subset H h.1 h.2.1
    · have he : w.first ∩ (w.second ∪ {T}) = w.reverseFirstRoot := by
        ext x
        by_cases hx : x = T
        · subst x
          simp [GainDefectWitness.reverseFirstRoot, w.root_mem]
        · simp only [GainDefectWitness.reverseFirstRoot, mem_inter, mem_union, mem_singleton,
            mem_insert, hx, or_false, false_or]
          tauto
      rw [he]
      exact h.2.2.2
  refine ⟨fun w ↦ ⟨code w, ⟨w.1.omitted, mem_powerset.mpr
    (w.1.omitted_subset.trans (erase_subset T w.1.first))⟩⟩, ?_⟩
  intro w u h
  have hf : w.1.first = u.1.first := congrArg (fun p ↦ p.1.1.2) h
  have hs : w.1.second = u.1.second := congrArg (fun p ↦ p.1.1.1) h
  have ho : w.1.omitted = u.1.omitted := congrArg (fun p ↦ p.2.1) h
  apply Subtype.ext
  rcases w with ⟨w, hw⟩
  rcases u with ⟨u, hu⟩
  cases w
  cases u
  simp_all

theorem card_gainDefectReverseClass_le
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T : W) (z : ℕ) (H Q : Finset W) (b m : ℕ)
    (hF : ∀ E ∈ F, E.card = m) :
    (gainDefectReverseClass F G T z H Q b).card ≤
      (rootedTwoFamilyExtensions G F Q {T} b).card * 2 ^ m := by
  calc
    _ = Fintype.card (gainDefectReverseClass F G T z H Q b) := (Fintype.card_coe _).symm
    _ ≤ Fintype.card (Σ p : rootedTwoFamilyExtensions G F Q {T} b, p.1.2.powerset) :=
      Fintype.card_le_of_embedding (gainDefectReverseClassEmbedding F G T z H Q b)
    _ = ∑ p : rootedTwoFamilyExtensions G F Q {T} b, 2 ^ p.1.2.card := by
      simp only [Fintype.card_sigma, Fintype.card_coe, card_powerset]
    _ = ∑ _p : rootedTwoFamilyExtensions G F Q {T} b, 2 ^ m := by
      apply sum_congr rfl
      intro p _
      rw [hF p.1.2 (mem_rootedTwoFamilyExtensions_iff.mp p.2).2.2.1]
    _ = _ := by simp

def gainDefectReverseClassWeight
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T : W) (z : ℕ) (H Q : Finset W) (b : ℕ) (p : ℝ≥0) : ℝ≥0 :=
  ∑ w ∈ gainDefectReverseClass F G T z H Q b, p ^ (w.remainder \ H).card

theorem gainDefectReverseClassWeight_eq
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T : W) (z : ℕ) (H Q : Finset W)
    (b m : ℕ) (p : ℝ≥0) (hF : ∀ E ∈ F, E.card = m) :
    gainDefectReverseClassWeight F G T z H Q b p =
      (gainDefectReverseClass F G T z H Q b).card * p ^ (m - (z + 1)) := by
  classical
  unfold gainDefectReverseClassWeight
  calc
    _ = ∑ _w ∈ gainDefectReverseClass F G T z H Q b, p ^ (m - (z + 1)) := by
      apply sum_congr rfl
      intro w hw
      have h := (mem_filter.mp hw).2
      rw [w.remainder_sdiff_eq_left_of_forwardExceptional H h.2.1,
        w.leftRemainder_card, hF w.first w.first_mem]
    _ = _ := by simp

theorem gainDefectReverseClassWeight_le_of_root_bounds
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T : W) (z : ℕ) (H Q : Finset W)
    (b m n N A B a e d : ℕ)
    (hF : ∀ E ∈ F, E.card = m) (hG : ∀ E ∈ G, E.card = n)
    (hfirst : (familyExtensions G Q).card ≤ A * N ^ a)
    (hsecond : ∀ R : Finset W, R.card = b → (familyExtensions F R).card ≤ B * N ^ e)
    (hN : 1 ≤ N) (hexp : a + e ≤ (m - (z + 1)) + d) :
    gainDefectReverseClassWeight F G T z H Q b (N : ℝ≥0)⁻¹ ≤
      (2 : ℝ≥0) ^ m * (((A : ℝ≥0) * 2 ^ (n + 1) * B) * (N : ℝ≥0) ^ d) := by
  rw [gainDefectReverseClassWeight_eq F G T z H Q b m _ hF]
  have hc : ((gainDefectReverseClass F G T z H Q b).card : ℝ≥0) ≤
      (rootedTwoFamilyExtensions G F Q {T} b).card * (2 : ℝ≥0) ^ m := by
    exact_mod_cast card_gainDefectReverseClass_le F G T z H Q b m hF
  calc
    _ ≤ ((rootedTwoFamilyExtensions G F Q {T} b).card * (2 : ℝ≥0) ^ m) *
        (N : ℝ≥0)⁻¹ ^ (m - (z + 1)) := mul_le_mul_of_nonneg_right hc zero_le
    _ = (2 : ℝ≥0) ^ m * ((rootedTwoFamilyExtensions G F Q {T} b).card *
        (N : ℝ≥0)⁻¹ ^ (m - (z + 1))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by
      simpa only [card_singleton] using
        rootedTwoFamilyExtensions_card_mul_inv_pow_le_pow G F Q {T} b n A B N a e
          (m - (z + 1)) d (fun E hE ↦ (hG E hE).le) hfirst hsecond hN hexp) zero_le

end

end Erdos207
