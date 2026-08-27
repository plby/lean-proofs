/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.UniformExtensionWeight

/-! # Counting the second configuration after exposing the first -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def secondRootExposureFibre
    {W : Type*} [DecidableEq W] (G : Finset (Finset W))
    (S R' : Finset W) (b : ℕ) : Finset (Finset W) :=
  G.filter fun S' ↦ R' ⊆ S' ∧ (S' ∩ (S ∪ R')).card = b

theorem card_secondRootExposureFibre_le
    {W : Type*} [DecidableEq W] (G : Finset (Finset W))
    (S R' : Finset W) (b B : ℕ)
    (hcount : ∀ Q : Finset W, Q.card = b → (familyExtensions G Q).card ≤ B) :
    (secondRootExposureFibre G S R' b).card ≤ 2 ^ (S.card + R'.card) * B := by
  have hsub : secondRootExposureFibre G S R' b ⊆
      ((S ∪ R').powersetCard b).biUnion (familyExtensions G) := by
    intro S' hS'
    obtain ⟨hG, _, hsize⟩ := mem_filter.mp hS'
    exact mem_biUnion.mpr ⟨S' ∩ (S ∪ R'),
      mem_powersetCard.mpr ⟨inter_subset_right, hsize⟩,
      mem_familyExtensions_iff.mpr ⟨hG, inter_subset_left⟩⟩
  have hroots : ((S ∪ R').powersetCard b).card ≤ 2 ^ (S.card + R'.card) := by
    calc
      _ ≤ ((S ∪ R').powerset).card := card_le_card (fun _ hQ ↦
        mem_powerset.mpr (mem_powersetCard.mp hQ).1)
      _ = 2 ^ (S ∪ R').card := card_powerset _
      _ ≤ _ := pow_le_pow_right' (by omega) (card_union_le S R')
  calc
    _ ≤ (((S ∪ R').powersetCard b).biUnion (familyExtensions G)).card := card_le_card hsub
    _ ≤ ∑ Q ∈ (S ∪ R').powersetCard b, (familyExtensions G Q).card := card_biUnion_le
    _ ≤ ∑ _Q ∈ (S ∪ R').powersetCard b, B :=
      sum_le_sum (fun Q hQ ↦ hcount Q (mem_powersetCard.mp hQ).2)
    _ = ((S ∪ R').powersetCard b).card * B := by simp
    _ ≤ _ := Nat.mul_le_mul_right B hroots

def rootedTwoFamilyExtensions
    {W : Type*} [DecidableEq W] (F G : Finset (Finset W))
    (R R' : Finset W) (b : ℕ) : Finset (Finset W × Finset W) :=
  (familyExtensions F R).biUnion fun S ↦
    (secondRootExposureFibre G S R' b).image fun S' ↦ (S, S')

theorem mem_rootedTwoFamilyExtensions_iff
    {W : Type*} [DecidableEq W] {F G : Finset (Finset W)}
    {R R' S S' : Finset W} {b : ℕ} :
    (S, S') ∈ rootedTwoFamilyExtensions F G R R' b ↔
      S ∈ F ∧ R ⊆ S ∧ S' ∈ G ∧ R' ⊆ S' ∧ (S' ∩ (S ∪ R')).card = b := by
  simp only [rootedTwoFamilyExtensions, mem_biUnion, mem_image,
    mem_familyExtensions_iff, secondRootExposureFibre, mem_filter, Prod.mk.injEq]
  constructor
  · rintro ⟨C, hC, D, hD, hCS, hDS'⟩
    subst C
    subst D
    exact ⟨hC.1, hC.2, hD.1, hD.2.1, hD.2.2⟩
  · rintro ⟨hSF, hRS, hS'G, hR'S', hsize⟩
    exact ⟨S, ⟨hSF, hRS⟩, S', ⟨hS'G, hR'S', hsize⟩, rfl, rfl⟩

theorem card_rootedTwoFamilyExtensions_le
    {W : Type*} [DecidableEq W] (F G : Finset (Finset W))
    (R R' : Finset W) (b m A B : ℕ)
    (hcard : ∀ S ∈ F, S.card ≤ m)
    (hfirst : (familyExtensions F R).card ≤ A)
    (hsecond : ∀ Q : Finset W, Q.card = b → (familyExtensions G Q).card ≤ B) :
    (rootedTwoFamilyExtensions F G R R' b).card ≤ A * (2 ^ (m + R'.card) * B) := by
  unfold rootedTwoFamilyExtensions
  calc
    _ ≤ ∑ S ∈ familyExtensions F R,
        ((secondRootExposureFibre G S R' b).image fun S' ↦ (S, S')).card := card_biUnion_le
    _ ≤ ∑ S ∈ familyExtensions F R, (secondRootExposureFibre G S R' b).card :=
      sum_le_sum (fun _ _ ↦ card_image_le)
    _ ≤ ∑ _S ∈ familyExtensions F R, 2 ^ (m + R'.card) * B := by
      apply sum_le_sum
      intro S hS
      refine (card_secondRootExposureFibre_le G S R' b B hsecond).trans ?_
      apply Nat.mul_le_mul_right
      exact pow_le_pow_right' (by omega)
        (Nat.add_le_add_right (hcard S (mem_familyExtensions_iff.mp hS).1) _)
    _ = (familyExtensions F R).card * (2 ^ (m + R'.card) * B) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hfirst

/-- After the two exposure exponents are paid for by the selected remainder,
the uniform weighted count has no remaining ambient-size factor. -/
theorem rootedTwoFamilyExtensions_card_mul_inv_pow_le
    {W : Type*} [DecidableEq W] (F G : Finset (Finset W))
    (R R' : Finset W) (b m A B n a e f : ℕ)
    (hcard : ∀ S ∈ F, S.card ≤ m)
    (hfirst : (familyExtensions F R).card ≤ A * n ^ a)
    (hsecond : ∀ Q : Finset W, Q.card = b →
      (familyExtensions G Q).card ≤ B * n ^ e)
    (hn : 1 ≤ n) (hexp : a + e ≤ f) :
    ((rootedTwoFamilyExtensions F G R R' b).card : ℝ≥0) * (n : ℝ≥0)⁻¹ ^ f ≤
      (A : ℝ≥0) * 2 ^ (m + R'.card) * B := by
  have hcount : ((rootedTwoFamilyExtensions F G R R' b).card : ℝ≥0) ≤
      ((A * n ^ a : ℕ) : ℝ≥0) *
        ((2 ^ (m + R'.card) * (B * n ^ e) : ℕ) : ℝ≥0) := by
    exact_mod_cast card_rootedTwoFamilyExtensions_le F G R R' b m
      (A * n ^ a) (B * n ^ e) hcard hfirst hsecond
  have hn1 : (1 : ℝ≥0) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ≥0) < n := lt_of_lt_of_le zero_lt_one hn1
  have hcancel : (n : ℝ≥0) ^ (a + e) * (n : ℝ≥0)⁻¹ ^ f ≤ 1 := by
    rw [inv_pow, mul_inv_le_iff₀ (pow_pos hn0 f), one_mul]
    exact pow_le_pow_right' hn1 hexp
  calc
    _ ≤ (((A * n ^ a : ℕ) : ℝ≥0) *
        ((2 ^ (m + R'.card) * (B * n ^ e) : ℕ) : ℝ≥0)) * (n : ℝ≥0)⁻¹ ^ f :=
      mul_le_mul_of_nonneg_right hcount zero_le
    _ = ((A : ℝ≥0) * 2 ^ (m + R'.card) * B) *
        ((n : ℝ≥0) ^ (a + e) * (n : ℝ≥0)⁻¹ ^ f) := by
      push_cast
      rw [pow_add]
      ring
    _ ≤ ((A : ℝ≥0) * 2 ^ (m + R'.card) * B) * 1 :=
      mul_le_mul_of_nonneg_left hcancel zero_le
    _ = _ := mul_one _

end

end Erdos207
