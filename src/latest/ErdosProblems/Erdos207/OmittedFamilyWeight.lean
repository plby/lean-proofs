/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.UniformExtensionWeight
import ErdosProblems.Erdos207.ExactBankInverseWeight

/-! # Uniform extension weights with a prescribed omitted subfamily -/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

abbrev OmittedFamilyIndex
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : Finset (Finset W)) (R : Finset W) (z : ℕ) :=
  {u : Finset W × Finset W //
    u.1 ∈ G ∧ R ⊆ u.1 ∧ u.2 ⊆ u.1 \ R ∧ u.2.card = z}

def omittedFamilyRemainder
    {W : Type*} [Fintype W] [DecidableEq W]
    {G : Finset (Finset W)} {R : Finset W} {z : ℕ}
    (u : OmittedFamilyIndex G R z) : Finset W := u.1.1 \ (R ∪ u.1.2)

abbrev ActiveOmittedFamilyIndex
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : Finset (Finset W)) (R : Finset W) (z : ℕ) (H : Finset W) :=
  {u : OmittedFamilyIndex G R z // H ⊆ omittedFamilyRemainder u}

theorem omittedFamilyRemainder_card
    {W : Type*} [Fintype W] [DecidableEq W]
    {G : Finset (Finset W)} {R : Finset W} {z m : ℕ}
    (hcard : ∀ S ∈ G, S.card = m) (u : OmittedFamilyIndex G R z) :
    (omittedFamilyRemainder u).card = m - R.card - z := by
  have hdis : Disjoint R u.1.2 := by
    apply disjoint_left.mpr
    intro x hxR hxO
    exact (mem_sdiff.mp (u.2.2.2.1 hxO)).2 hxR
  have hsub : R ∪ u.1.2 ⊆ u.1.1 :=
    union_subset u.2.2.1 (u.2.2.2.1.trans sdiff_subset)
  rw [omittedFamilyRemainder, card_sdiff_of_subset hsub,
    card_union_of_disjoint hdis, hcard _ u.2.1, u.2.2.2.2]
  omega

theorem activeOmittedFamily_root_disjoint
    {W : Type*} [Fintype W] [DecidableEq W]
    {G : Finset (Finset W)} {R H : Finset W} {z : ℕ}
    (u : ActiveOmittedFamilyIndex G R z H) : Disjoint R H := by
  apply disjoint_left.mpr
  intro x hxR hxH
  exact (mem_sdiff.mp (u.2 hxH)).2 (mem_union_left _ hxR)

theorem activeOmittedFamily_enlargedRoot_subset
    {W : Type*} [Fintype W] [DecidableEq W]
    {G : Finset (Finset W)} {R H : Finset W} {z : ℕ}
    (u : ActiveOmittedFamilyIndex G R z H) : R ∪ H ⊆ u.1.1.1 :=
  union_subset u.1.2.2.1 (u.2.trans sdiff_subset)

def activeOmittedFamilyEmbedding
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : Finset (Finset W)) (R H : Finset W) (z : ℕ) :
    ActiveOmittedFamilyIndex G R z H ↪
      Σ S : familyExtensions G (R ∪ H), S.1.powerset where
  toFun u := ⟨⟨u.1.1.1, mem_familyExtensions_iff.mpr
    ⟨u.1.2.1, activeOmittedFamily_enlargedRoot_subset u⟩⟩,
      ⟨u.1.1.2, mem_powerset.mpr (u.1.2.2.2.1.trans sdiff_subset)⟩⟩
  inj' := by
    intro u v h
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun x ↦ x.1.1) h
    · exact congrArg (fun x ↦ x.2.1) h

theorem card_activeOmittedFamilyIndex_le
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : Finset (Finset W)) (R H : Finset W) (z m : ℕ)
    (hcard : ∀ S ∈ G, S.card = m) :
    Fintype.card (ActiveOmittedFamilyIndex G R z H) ≤
      (familyExtensions G (R ∪ H)).card * 2 ^ m := by
  classical
  calc
    _ ≤ Fintype.card (Σ S : familyExtensions G (R ∪ H), S.1.powerset) :=
      Fintype.card_le_of_injective (activeOmittedFamilyEmbedding G R H z)
        (activeOmittedFamilyEmbedding G R H z).injective
    _ = ∑ S : familyExtensions G (R ∪ H), 2 ^ S.1.card := by
      rw [Fintype.card_sigma]
      apply sum_congr rfl
      intro S _
      exact (Fintype.card_coe S.1.powerset).trans (card_powerset S.1)
    _ = ∑ _S : familyExtensions G (R ∪ H), 2 ^ m := by
      apply sum_congr rfl
      intro S _
      rw [hcard S.1 (mem_familyExtensions_iff.mp S.2).1]
    _ = _ := by simp

theorem extensionWeight_omittedFamily_eq
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : Finset (Finset W)) (R H : Finset W) (z m : ℕ)
    (hcard : ∀ S ∈ G, S.card = m) (p : ℝ≥0) :
    extensionWeight (fun u : OmittedFamilyIndex G R z ↦ omittedFamilyRemainder u)
      (fun _ ↦ p) H =
        (Fintype.card (ActiveOmittedFamilyIndex G R z H) : ℝ≥0) *
          p ^ (m - R.card - z - H.card) := by
  classical
  unfold extensionWeight
  calc
    _ = ∑ u : OmittedFamilyIndex G R z,
        if H ⊆ omittedFamilyRemainder u then p ^ (m - R.card - z - H.card) else 0 := by
      apply sum_congr rfl
      intro u _
      by_cases hH : H ⊆ omittedFamilyRemainder u
      · rw [if_pos hH, if_pos hH]
        simp only [setWeight, prod_const, card_sdiff_of_subset hH,
          omittedFamilyRemainder_card hcard u]
      · rw [if_neg hH, if_neg hH]
    _ = _ := by
      rw [Fintype.card_subtype, ← sum_filter]
      simp

/-- The first KSSS nibble-moment exponent in the uniform-weight setting.
The factor `2^m` pays for the omitted subfamily, retaining multiplicities. -/
theorem omittedFamily_hasExtensionBound
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : Finset (Finset W)) (R : Finset W) (z m n B : ℕ)
    (hcard : ∀ S ∈ G, S.card = m) (hR : R.card = 2) (hz : 1 ≤ z) (hn : 1 ≤ n)
    (hcount : ∀ Q : Finset W, 2 ≤ Q.card → Q.card < m →
      (familyExtensions G Q).card ≤ B * n ^ (m - Q.card - 1)) :
    HasExtensionBound
      (fun u : OmittedFamilyIndex G R z ↦ omittedFamilyRemainder u)
      (fun _ ↦ (n : ℝ≥0)⁻¹) ((2 : ℝ≥0) ^ m * B * (n : ℝ≥0) ^ (z - 1)) := by
  classical
  intro H
  rw [extensionWeight_omittedFamily_eq G R H z m hcard]
  by_cases hpos : 0 < Fintype.card (ActiveOmittedFamilyIndex G R z H)
  · obtain ⟨u⟩ := Fintype.card_pos_iff.mp hpos
    have hRle : R.card ≤ m :=
      (card_le_card u.1.2.2.1).trans_eq (hcard _ u.1.2.1)
    have hzle : z ≤ m - R.card := by
      have h := card_le_card u.1.2.2.2.1
      rw [u.1.2.2.2.2, card_sdiff_of_subset u.1.2.2.1, hcard _ u.1.2.1] at h
      exact h
    have hHle : H.card ≤ m - R.card - z :=
      (card_le_card u.2).trans_eq (omittedFamilyRemainder_card hcard u.1)
    have hQcard : (R ∪ H).card = 2 + H.card := by
      rw [card_union_of_disjoint (activeOmittedFamily_root_disjoint u), hR]
    have hQlo : 2 ≤ (R ∪ H).card := by omega
    have hQhi : (R ∪ H).card < m := by omega
    have hfamily := hcount (R ∪ H) hQlo hQhi
    have hindices : Fintype.card (ActiveOmittedFamilyIndex G R z H) ≤
        B * n ^ (m - (R ∪ H).card - 1) * 2 ^ m :=
      (card_activeOmittedFamilyIndex_le G R H z m hcard).trans
        (Nat.mul_le_mul_right _ hfamily)
    have hexp : m - R.card - z - H.card ≤ m - (R ∪ H).card - 1 := by omega
    have hcancel : (n : ℝ≥0) ^ (m - (R ∪ H).card - 1) *
        ((n : ℝ≥0)⁻¹) ^ (m - R.card - z - H.card) = (n : ℝ≥0) ^ (z - 1) := by
      rw [pow_mul_inv_pow_eq_pow_sub n _ _ hn hexp]
      congr 1
      omega
    have hindicesR : (Fintype.card (ActiveOmittedFamilyIndex G R z H) : ℝ≥0) ≤
        (B : ℝ≥0) * (n : ℝ≥0) ^ (m - (R ∪ H).card - 1) * (2 : ℝ≥0) ^ m := by
      exact_mod_cast hindices
    calc
      _ ≤ ((B : ℝ≥0) * (n : ℝ≥0) ^ (m - (R ∪ H).card - 1) * (2 : ℝ≥0) ^ m) *
          ((n : ℝ≥0)⁻¹) ^ (m - R.card - z - H.card) :=
            mul_le_mul_of_nonneg_right hindicesR zero_le
      _ = (2 : ℝ≥0) ^ m * B * ((n : ℝ≥0) ^ (m - (R ∪ H).card - 1) *
          ((n : ℝ≥0)⁻¹) ^ (m - R.card - z - H.card)) := by ring
      _ = _ := by rw [hcancel]
  · have hzero : Fintype.card (ActiveOmittedFamilyIndex G R z H) = 0 := by omega
    simp only [hzero, Nat.cast_zero, zero_mul]
    exact zero_le

end

end Erdos207
