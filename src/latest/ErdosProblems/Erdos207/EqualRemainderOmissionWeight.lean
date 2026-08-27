/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberEqualRemainderCount

/-! # Uniform weighted exceptional cases with omission multiplicities retained -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def equalRemainderOmissionCodes
    {W : Type*} [DecidableEq W] (F : Finset (Finset W)) (T T' : W) (z : ℕ) :
    Finset ((Finset W × Finset W) × Finset W) :=
  (distinctEqualRemainderPairs F T T').biUnion fun p ↦
    ((p.1.erase T).powersetCard z).image fun O ↦ (p, O)

theorem mem_equalRemainderOmissionCodes_iff
    {W : Type*} [DecidableEq W] {F : Finset (Finset W)} {T T' : W} {z : ℕ}
    {u : (Finset W × Finset W) × Finset W} :
    u ∈ equalRemainderOmissionCodes F T T' z ↔
      u.1 ∈ distinctEqualRemainderPairs F T T' ∧
        u.2 ⊆ u.1.1.erase T ∧ u.2.card = z := by
  rcases u with ⟨p, O⟩
  simp only [equalRemainderOmissionCodes, mem_biUnion, mem_image,
    mem_powersetCard, Prod.mk.injEq]
  constructor
  · rintro ⟨p', hp', O', hO', hp, hO⟩
    subst p'
    subst O'
    exact ⟨hp', hO'⟩
  · rintro ⟨hp, hO⟩
    exact ⟨p, hp, O, hO, rfl, rfl⟩

theorem card_equalRemainderOmissionCodes_le
    {W : Type*} [DecidableEq W] (F : Finset (Finset W)) (T T' : W) (z m : ℕ)
    (hcard : ∀ E ∈ F, E.card = m) :
    (equalRemainderOmissionCodes F T T' z).card ≤
      (distinctEqualRemainderPairs F T T').card * 2 ^ (m - 1) := by
  unfold equalRemainderOmissionCodes
  calc
    _ ≤ ∑ p ∈ distinctEqualRemainderPairs F T T',
        (((p.1.erase T).powersetCard z).image fun O ↦ (p, O)).card := card_biUnion_le
    _ ≤ ∑ _p ∈ distinctEqualRemainderPairs F T T', 2 ^ (m - 1) := by
      apply sum_le_sum
      intro p hp
      have h := mem_distinctEqualRemainderPairs_iff.mp hp
      calc
        _ ≤ ((p.1.erase T).powersetCard z).card := card_image_le
        _ ≤ ((p.1.erase T).powerset).card := card_le_card (fun _ hO ↦
          mem_powerset.mpr (mem_powersetCard.mp hO).1)
        _ = 2 ^ (m - 1) := by rw [card_powerset, card_erase_of_mem h.2.2.2.1, hcard p.1 h.1]
    _ = _ := by simp

def equalRemainderOmissionWeight
    {W : Type*} [DecidableEq W] (F : Finset (Finset W)) (T T' : W) (z : ℕ) (p : ℝ≥0) : ℝ≥0 :=
  ∑ u ∈ equalRemainderOmissionCodes F T T' z, p ^ ((u.1.1.erase T) \ u.2).card

theorem equalRemainderOmissionWeight_eq
    {W : Type*} [DecidableEq W] (F : Finset (Finset W)) (T T' : W)
    (z m : ℕ) (p : ℝ≥0) (hcard : ∀ E ∈ F, E.card = m) :
    equalRemainderOmissionWeight F T T' z p =
      (equalRemainderOmissionCodes F T T' z).card * p ^ (m - 1 - z) := by
  unfold equalRemainderOmissionWeight
  calc
    _ = ∑ _u ∈ equalRemainderOmissionCodes F T T' z, p ^ (m - 1 - z) := by
      apply sum_congr rfl
      intro u hu
      have h := mem_equalRemainderOmissionCodes_iff.mp hu
      have hp := mem_distinctEqualRemainderPairs_iff.mp h.1
      rw [card_sdiff_of_subset h.2.1, card_erase_of_mem hp.2.2.2.1, hcard u.1.1 hp.1, h.2.2]
    _ = _ := by simp

theorem equalRemainderOmissionWeight_le_of_pair_count
    {W : Type*} [DecidableEq W] (F : Finset (Finset W)) (T T' : W)
    (z m n B : ℕ) (hcard : ∀ E ∈ F, E.card = m)
    (hm : 2 ≤ m) (hz : 1 ≤ z) (hn : 1 ≤ n)
    (hcount : (distinctEqualRemainderPairs F T T').card ≤ B * n ^ (m - 2)) :
    equalRemainderOmissionWeight F T T' z (n : ℝ≥0)⁻¹ ≤
      (2 : ℝ≥0) ^ (m - 1) * B * (n : ℝ≥0) ^ (z - 1) := by
  rw [equalRemainderOmissionWeight_eq F T T' z m _ hcard]
  have hcodes : ((equalRemainderOmissionCodes F T T' z).card : ℝ≥0) ≤
      ((B * n ^ (m - 2) * 2 ^ (m - 1) : ℕ) : ℝ≥0) := by
    exact_mod_cast (card_equalRemainderOmissionCodes_le F T T' z m hcard).trans
      (Nat.mul_le_mul_right _ hcount)
  have hcancel : (n : ℝ≥0) ^ (m - 2) * (n : ℝ≥0)⁻¹ ^ (m - 1 - z) ≤
      (n : ℝ≥0) ^ (z - 1) := by
    rw [pow_mul_inv_pow_eq_pow_sub n _ _ hn (by omega)]
    exact pow_le_pow_right' (by exact_mod_cast hn) (by omega)
  calc
    _ ≤ (((B * n ^ (m - 2) * 2 ^ (m - 1) : ℕ) : ℝ≥0)) *
        (n : ℝ≥0)⁻¹ ^ (m - 1 - z) := mul_le_mul_of_nonneg_right hcodes zero_le
    _ = ((2 : ℝ≥0) ^ (m - 1) * B) *
        ((n : ℝ≥0) ^ (m - 2) * (n : ℝ≥0)⁻¹ ^ (m - 1 - z)) := by push_cast; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcancel zero_le

theorem equalRemainderOmissionWeight_absorberInduced_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j z : ℕ) (B : TripleSystemOn V) (T T' : TripleOn V)
    (hj : 4 ≤ j) (hz : 1 ≤ z) :
    equalRemainderOmissionWeight (absorberInducedConfigurationsOn q j B) T T' z
      (Fintype.card V + 1 : ℝ≥0)⁻¹ ≤
      (2 : ℝ≥0) ^ (j - 3) *
        (2 * pairExactBankExtensionCoefficient q B + 2 ^ (j ^ 3) * (j + 1) : ℕ) *
        (Fintype.card V + 1 : ℝ≥0) ^ (z - 1) := by
  have h := equalRemainderOmissionWeight_le_of_pair_count
    (absorberInducedConfigurationsOn q j B) T T' z (j - 2) (Fintype.card V + 1)
    (2 * pairExactBankExtensionCoefficient q B + 2 ^ (j ^ 3) * (j + 1))
    absorberInducedConfigurationsOn_fixed_card (by omega) hz (by omega)
    (by simpa only [Nat.sub_sub] using
      card_distinctEqualRemainderPairs_absorberInduced_le q j B T T' hj)
  simpa only [Nat.sub_sub, Nat.cast_add, Nat.cast_one] using h

end

end Erdos207
