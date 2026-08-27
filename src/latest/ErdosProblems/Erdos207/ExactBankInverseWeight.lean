/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ExactBankWeightedBound

/-!
# Cancellation for exact bank classes at inverse ambient weight

At the uniform weight `(|V|+1)⁻¹`, the polynomial count supplied by
minimality cancels against the probability of the unprescribed outside
triangles.  Both the strong interior exponent and the weak endpoint exponent
give a remaining inverse ambient factor in the situations used for rooted
threats.
-/

namespace Erdos207

open Finset
open scoped NNReal

/-- If the inverse power contains at least one more factor than the positive
power, their product is at most one inverse factor. -/
lemma pow_mul_inv_pow_le_inv
    (N d e : ℕ) (hN : 1 ≤ N) (hde : d + 1 ≤ e) :
    (N : ℝ≥0) ^ d * ((N : ℝ≥0)⁻¹) ^ e ≤ (N : ℝ≥0)⁻¹ := by
  have hNpos : (0 : ℝ≥0) < N := by exact_mod_cast (show 0 < N by omega)
  have hinvle : (N : ℝ≥0)⁻¹ ≤ 1 :=
    (inv_le_one₀ hNpos).2 (by exact_mod_cast hN)
  have he : e = d + (e - d) := by omega
  have hk : 1 ≤ e - d := by omega
  rw [he, pow_add, ← mul_assoc, ← mul_pow]
  simp only [mul_inv_cancel₀ (ne_of_gt hNpos), one_pow, one_mul]
  simpa only [pow_one] using
    pow_le_pow_right_of_le_one' hinvle hk

/-- Two strict exponent gains leave two inverse ambient factors. -/
lemma pow_mul_inv_pow_le_inv_sq
    (N d e : ℕ) (hN : 1 ≤ N) (hde : d + 2 ≤ e) :
    (N : ℝ≥0) ^ d * ((N : ℝ≥0)⁻¹) ^ e ≤
      ((N : ℝ≥0)⁻¹) ^ 2 := by
  have hNpos : (0 : ℝ≥0) < N := by exact_mod_cast (show 0 < N by omega)
  have hinvle : (N : ℝ≥0)⁻¹ ≤ 1 :=
    (inv_le_one₀ hNpos).2 (by exact_mod_cast hN)
  have he : e = d + (e - d) := by omega
  have hk : 2 ≤ e - d := by omega
  rw [he, pow_add, ← mul_assoc, ← mul_pow]
  simp only [mul_inv_cancel₀ (ne_of_gt hNpos), one_pow, one_mul]
  exact pow_le_pow_right_of_le_one' hinvle hk

/-- With no strict exponent gain the same cancellation is bounded by one. -/
lemma pow_mul_inv_pow_le_one
    (N d e : ℕ) (hN : 1 ≤ N) (hde : d ≤ e) :
    (N : ℝ≥0) ^ d * ((N : ℝ≥0)⁻¹) ^ e ≤ 1 := by
  have hNpos : (0 : ℝ≥0) < N := by exact_mod_cast (show 0 < N by omega)
  have hinvle : (N : ℝ≥0)⁻¹ ≤ 1 :=
    (inv_le_one₀ hNpos).2 (by exact_mod_cast hN)
  have he : e = d + (e - d) := by omega
  rw [he, pow_add, ← mul_assoc, ← mul_pow]
  simp only [mul_inv_cancel₀ (ne_of_gt hNpos), one_pow, one_mul]
  exact pow_le_one₀ zero_le hinvle

/-- Exact cancellation when the positive exponent dominates the inverse
exponent. -/
lemma pow_mul_inv_pow_eq_pow_sub
    (N d e : ℕ) (hN : 1 ≤ N) (hed : e ≤ d) :
    (N : ℝ≥0) ^ d * ((N : ℝ≥0)⁻¹) ^ e =
      (N : ℝ≥0) ^ (d - e) := by
  have hNpos : (0 : ℝ≥0) < N := by exact_mod_cast (show 0 < N by omega)
  have hd : d = e + (d - e) := by omega
  have hp : (N : ℝ≥0) ^ d =
      (N : ℝ≥0) ^ e * (N : ℝ≥0) ^ (d - e) := by
    nth_rewrite 1 [hd]
    rw [pow_add]
  calc
    (N : ℝ≥0) ^ d * ((N : ℝ≥0)⁻¹) ^ e =
        ((N : ℝ≥0) ^ e * (N : ℝ≥0) ^ (d - e)) *
          ((N : ℝ≥0)⁻¹) ^ e := by rw [hp]
    _ = ((N : ℝ≥0) ^ e * ((N : ℝ≥0)⁻¹) ^ e) *
          (N : ℝ≥0) ^ (d - e) := by ac_rfl
    _ = (N : ℝ≥0) ^ (d - e) := by
      rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hNpos), one_pow, one_mul]

/-- Strong minimality gives a full inverse ambient factor for one exact bank
class at uniform inverse-ambient triangle weight. -/
theorem extensionWeight_exactBankOutsideExtensions_le_inv_strong
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K A : TripleSystemOn V}
    (hr : 5 ≤ r) (hj : 2 ≤ j) (hjr : j ≤ r)
    (hRA : Disjoint R A)
    (hroot2 : 2 ≤ ((R ∪ A) ∪ K).card)
    (hrootsmall : ((R ∪ A) ∪ K).card ≤ r - 3) :
    extensionWeight
        (fun S : exactBankOutsideExtensions r j B R K ↦ S.1)
        (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) A ≤
      (2 ^ (r ^ 3) * (r + 1) : ℕ) *
        (Fintype.card V + 1 : ℝ≥0)⁻¹ := by
  by_cases hne : (familyExtensions
      (exactBankOutsideExtensions r j B R K) A).Nonempty
  · rw [extensionWeight_exactBankOutsideExtensions]
    have hcardNat :=
      card_familyExtensions_exactBankOutsideExtensions_le_strong
        hr hne hroot2 hrootsmall
    have hcard :
        ((familyExtensions
          (exactBankOutsideExtensions r j B R K) A).card : ℝ≥0) ≤
          (2 ^ (r ^ 3) * (r + 1) : ℕ) *
            (Fintype.card V + 1 : ℝ≥0) ^
              (r - (((R ∪ A) ∪ K).card + 3)) := by
      exact_mod_cast hcardNat
    have hrootcard :=
      exactBank_enlarged_root_union_card_of_disjoint
        (by omega : 2 ≤ r) hj hjr hne hRA
    have hpower :
        r - (((R ∪ A) ∪ K).card + 3) + 1 ≤
          j - 2 - A.card := by omega
    have hcancel := pow_mul_inv_pow_le_inv
      (Fintype.card V + 1)
      (r - (((R ∪ A) ∪ K).card + 3))
      (j - 2 - A.card) (by omega) hpower
    calc
      ((familyExtensions
          (exactBankOutsideExtensions r j B R K) A).card : ℝ≥0) *
          ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ (j - 2 - A.card) ≤
          ((2 ^ (r ^ 3) * (r + 1) : ℕ) *
            (Fintype.card V + 1 : ℝ≥0) ^
              (r - (((R ∪ A) ∪ K).card + 3))) *
            ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^
              (j - 2 - A.card) :=
        by
          simpa only [mul_comm] using
            mul_le_mul_right hcard
              (((Fintype.card V + 1 : ℝ≥0)⁻¹) ^
                (j - 2 - A.card))
      _ = (2 ^ (r ^ 3) * (r + 1) : ℕ) *
          ((Fintype.card V + 1 : ℝ≥0) ^
              (r - (((R ∪ A) ∪ K).card + 3)) *
            ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^
              (j - 2 - A.card)) := by
        simp only [mul_assoc]
      _ ≤ (2 ^ (r ^ 3) * (r + 1) : ℕ) *
          (Fintype.card V + 1 : ℝ≥0)⁻¹ := by
        simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using
          mul_le_mul_left hcancel
            (2 ^ (r ^ 3) * (r + 1) : ℕ)
  · have hempty : familyExtensions
        (exactBankOutsideExtensions r j B R K) A = ∅ :=
      not_nonempty_iff_eq_empty.mp hne
    rw [extensionWeight_exactBankOutsideExtensions, hempty]
    simp

/-- If the original exact root is already nonempty, the strong interior
minimality exponent leaves two inverse ambient factors.  This is the form
needed when a nonlocal support triangle is exposed in addition to a rooted
threat triangle. -/
theorem extensionWeight_exactBankOutsideExtensions_le_inv_sq_strong
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K A : TripleSystemOn V}
    (hr : 5 ≤ r) (hj : 2 ≤ j) (hjr : j ≤ r)
    (hRA : Disjoint R A) (hR : 1 ≤ R.card)
    (hroot2 : 2 ≤ ((R ∪ A) ∪ K).card)
    (hrootsmall : ((R ∪ A) ∪ K).card ≤ r - 3) :
    extensionWeight
        (fun S : exactBankOutsideExtensions r j B R K ↦ S.1)
        (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) A ≤
      (2 ^ (r ^ 3) * (r + 1) : ℕ) *
        ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ 2 := by
  by_cases hne : (familyExtensions
      (exactBankOutsideExtensions r j B R K) A).Nonempty
  · rw [extensionWeight_exactBankOutsideExtensions]
    have hcardNat :=
      card_familyExtensions_exactBankOutsideExtensions_le_strong
        hr hne hroot2 hrootsmall
    have hcard :
        ((familyExtensions
          (exactBankOutsideExtensions r j B R K) A).card : ℝ≥0) ≤
          (2 ^ (r ^ 3) * (r + 1) : ℕ) *
            (Fintype.card V + 1 : ℝ≥0) ^
              (r - (((R ∪ A) ∪ K).card + 3)) := by
      exact_mod_cast hcardNat
    have hrootcard :=
      exactBank_enlarged_root_union_card_of_disjoint
        (by omega : 2 ≤ r) hj hjr hne hRA
    have hpower :
        r - (((R ∪ A) ∪ K).card + 3) + 2 ≤
          j - 2 - A.card := by omega
    have hcancel := pow_mul_inv_pow_le_inv_sq
      (Fintype.card V + 1)
      (r - (((R ∪ A) ∪ K).card + 3))
      (j - 2 - A.card) (by omega) hpower
    calc
      ((familyExtensions
          (exactBankOutsideExtensions r j B R K) A).card : ℝ≥0) *
          ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ (j - 2 - A.card) ≤
          ((2 ^ (r ^ 3) * (r + 1) : ℕ) *
            (Fintype.card V + 1 : ℝ≥0) ^
              (r - (((R ∪ A) ∪ K).card + 3))) *
            ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^
              (j - 2 - A.card) := by
        simpa only [mul_comm] using
          mul_le_mul_right hcard
            (((Fintype.card V + 1 : ℝ≥0)⁻¹) ^
              (j - 2 - A.card))
      _ = (2 ^ (r ^ 3) * (r + 1) : ℕ) *
          ((Fintype.card V + 1 : ℝ≥0) ^
              (r - (((R ∪ A) ∪ K).card + 3)) *
            ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^
              (j - 2 - A.card)) := by simp only [mul_assoc]
      _ ≤ (2 ^ (r ^ 3) * (r + 1) : ℕ) *
          ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ 2 := by
        simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using
          mul_le_mul_left hcancel
            (2 ^ (r ^ 3) * (r + 1) : ℕ)
  · have hempty : familyExtensions
        (exactBankOutsideExtensions r j B R K) A = ∅ :=
      not_nonempty_iff_eq_empty.mp hne
    rw [extensionWeight_exactBankOutsideExtensions, hempty]
    simp

/-- Strong minimality for a class rooted at its own prescribed outside
part.  If `R ∪ K` is in the interior range, the remaining exact-class
weight has one inverse ambient factor. -/
theorem extensionWeight_exactBankOutsideExtensions_self_le_inv_strong
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K : TripleSystemOn V}
    (hr : 5 ≤ r) (hj : 2 ≤ j)
    (hroot2 : 2 ≤ (R ∪ K).card)
    (hrootsmall : (R ∪ K).card ≤ r - 3) :
    extensionWeight
        (fun S : exactBankOutsideExtensions r j B R K ↦ S.1)
        (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) R ≤
      (2 ^ (r ^ 3) * (r + 1) : ℕ) *
        (Fintype.card V + 1 : ℝ≥0)⁻¹ := by
  change extensionWeight
      (fun S : exactBankOutsideExtensions r j B R K ↦ S.1)
      (fun _ ↦ (Fintype.card V + 1 : ℝ≥0)⁻¹) R ≤ _
  rw [extensionWeight_constant_eq _ (j - 2)
    exactBankOutsideExtensions_fixed_card
    ((Fintype.card V + 1 : ℝ≥0)⁻¹) R]
  have hself : familyExtensions (exactBankOutsideExtensions r j B R K) R =
      exactBankOutsideExtensions r j B R K := by
    ext S
    constructor
    · exact fun hS ↦ (mem_familyExtensions_iff.mp hS).1
    · intro hS
      exact mem_familyExtensions_iff.mpr
        ⟨hS, (mem_exactBankOutsideExtensions_iff.mp hS).2.1⟩
  rw [hself]
  by_cases hne : (exactBankOutsideExtensions r j B R K).Nonempty
  · have hne' := hne
    obtain ⟨S, hS⟩ := hne
    obtain ⟨hScard, _hRS, E, hE, hEout, _hEin⟩ :=
      mem_exactBankOutsideExtensions_iff.mp hS
    have hSsubE : S ⊆ E := by
      intro T hTS
      exact (mem_sdiff.mp (by rw [hEout]; exact hTS)).1
    have hjr : j ≤ r := by
      have hc := card_le_card hSsubE
      rw [hScard, hE.1.1] at hc
      omega
    have hfamily :
        (familyExtensions
          (exactBankOutsideExtensions r j B R K) ∅).Nonempty := by
      simpa [familyExtensions] using hne'
    have hcardNat :=
      card_familyExtensions_exactBankOutsideExtensions_le_strong
        (B := B) (R := R) (K := K) (A := ∅)
        hr hfamily (by simpa using hroot2) (by simpa using hrootsmall)
    have hcard :
        ((exactBankOutsideExtensions r j B R K).card : ℝ≥0) ≤
          (2 ^ (r ^ 3) * (r + 1) : ℕ) *
            (Fintype.card V + 1 : ℝ≥0) ^
              (r - ((R ∪ K).card + 3)) := by
      have hcast :
          ((familyExtensions
            (exactBankOutsideExtensions r j B R K) ∅).card : ℝ≥0) ≤
            (2 ^ (r ^ 3) * (r + 1) : ℕ) *
              (Fintype.card V + 1 : ℝ≥0) ^
                (r - (((R ∪ ∅) ∪ K).card + 3)) := by
        exact_mod_cast hcardNat
      simpa [familyExtensions] using hcast
    have hKcard := exactBankOutsideExtensions_bank_card
      (by omega : 2 ≤ r) hj hjr hS
    have hrootcard := exactBankOutsideExtensions_root_union_card hS
    have hpower : r - ((R ∪ K).card + 3) + 1 ≤
        j - 2 - R.card := by omega
    have hcancel := pow_mul_inv_pow_le_inv
      (Fintype.card V + 1)
      (r - ((R ∪ K).card + 3))
      (j - 2 - R.card) (by omega) hpower
    calc
      ((exactBankOutsideExtensions r j B R K).card : ℝ≥0) *
          ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ (j - 2 - R.card) ≤
        ((2 ^ (r ^ 3) * (r + 1) : ℕ) *
          (Fintype.card V + 1 : ℝ≥0) ^
            (r - ((R ∪ K).card + 3))) *
          ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^
            (j - 2 - R.card) := by
        simpa only [mul_comm] using mul_le_mul_right hcard
          (((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ (j - 2 - R.card))
      _ = (2 ^ (r ^ 3) * (r + 1) : ℕ) *
          ((Fintype.card V + 1 : ℝ≥0) ^
              (r - ((R ∪ K).card + 3)) *
            ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^
              (j - 2 - R.card)) := by simp only [mul_assoc]
      _ ≤ (2 ^ (r ^ 3) * (r + 1) : ℕ) *
          (Fintype.card V + 1 : ℝ≥0)⁻¹ := by
        simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using
          mul_le_mul_left hcancel
            (2 ^ (r ^ 3) * (r + 1) : ℕ)
  · rw [not_nonempty_iff_eq_empty.mp hne]
    simp

/-- At an endpoint the weak exponent still leaves one inverse ambient factor
provided the original outside root is nonempty. -/
theorem extensionWeight_exactBankOutsideExtensions_le_inv_weak
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K A : TripleSystemOn V}
    (hr : 5 ≤ r) (hj : 2 ≤ j) (hjr : j ≤ r)
    (hRA : Disjoint R A) (hR : 1 ≤ R.card)
    (hrootsmall : ((R ∪ A) ∪ K).card ≤ r - 2) :
    extensionWeight
        (fun S : exactBankOutsideExtensions r j B R K ↦ S.1)
        (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) A ≤
      (2 ^ (r ^ 3) * (r + 1) : ℕ) *
        (Fintype.card V + 1 : ℝ≥0)⁻¹ := by
  by_cases hne : (familyExtensions
      (exactBankOutsideExtensions r j B R K) A).Nonempty
  · rw [extensionWeight_exactBankOutsideExtensions]
    have hrootcard :=
      exactBank_enlarged_root_union_card_of_disjoint
        (by omega : 2 ≤ r) hj hjr hne hRA
    have hroot : 1 ≤ ((R ∪ A) ∪ K).card := by omega
    have hcardNat :=
      card_familyExtensions_exactBankOutsideExtensions_le_weak
        hr hne hroot
    have hcard :
        ((familyExtensions
          (exactBankOutsideExtensions r j B R K) A).card : ℝ≥0) ≤
          (2 ^ (r ^ 3) * (r + 1) : ℕ) *
            (Fintype.card V + 1 : ℝ≥0) ^
              (r - (((R ∪ A) ∪ K).card + 2)) := by
      exact_mod_cast hcardNat
    have hpower :
        r - (((R ∪ A) ∪ K).card + 2) + 1 ≤
          j - 2 - A.card := by omega
    have hcancel := pow_mul_inv_pow_le_inv
      (Fintype.card V + 1)
      (r - (((R ∪ A) ∪ K).card + 2))
      (j - 2 - A.card) (by omega) hpower
    calc
      ((familyExtensions
          (exactBankOutsideExtensions r j B R K) A).card : ℝ≥0) *
          ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ (j - 2 - A.card) ≤
          ((2 ^ (r ^ 3) * (r + 1) : ℕ) *
            (Fintype.card V + 1 : ℝ≥0) ^
              (r - (((R ∪ A) ∪ K).card + 2))) *
            ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^
              (j - 2 - A.card) :=
        by
          simpa only [mul_comm] using
            mul_le_mul_right hcard
              (((Fintype.card V + 1 : ℝ≥0)⁻¹) ^
                (j - 2 - A.card))
      _ = (2 ^ (r ^ 3) * (r + 1) : ℕ) *
          ((Fintype.card V + 1 : ℝ≥0) ^
              (r - (((R ∪ A) ∪ K).card + 2)) *
            ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^
              (j - 2 - A.card)) := by
        simp only [mul_assoc]
      _ ≤ (2 ^ (r ^ 3) * (r + 1) : ℕ) *
          (Fintype.card V + 1 : ℝ≥0)⁻¹ := by
        simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using
          mul_le_mul_left hcancel
            (2 ^ (r ^ 3) * (r + 1) : ℕ)
  · have hempty : familyExtensions
        (exactBankOutsideExtensions r j B R K) A = ∅ :=
      not_nonempty_iff_eq_empty.mp hne
    rw [extensionWeight_exactBankOutsideExtensions, hempty]
    simp

/-- The weak endpoint exponent always gives a constant bound, even when the
original prescribed outside root is empty. -/
theorem extensionWeight_exactBankOutsideExtensions_le_one_weak
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K A : TripleSystemOn V}
    (hr : 5 ≤ r) (hj : 2 ≤ j) (hjr : j ≤ r)
    (hRA : Disjoint R A)
    (hroot : 1 ≤ ((R ∪ A) ∪ K).card) :
    extensionWeight
        (fun S : exactBankOutsideExtensions r j B R K ↦ S.1)
        (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) A ≤
      (2 ^ (r ^ 3) * (r + 1) : ℕ) := by
  by_cases hne : (familyExtensions
      (exactBankOutsideExtensions r j B R K) A).Nonempty
  · rw [extensionWeight_exactBankOutsideExtensions]
    have hrootcard :=
      exactBank_enlarged_root_union_card_of_disjoint
        (by omega : 2 ≤ r) hj hjr hne hRA
    have hcardNat :=
      card_familyExtensions_exactBankOutsideExtensions_le_weak
        hr hne hroot
    have hcard :
        ((familyExtensions
          (exactBankOutsideExtensions r j B R K) A).card : ℝ≥0) ≤
          (2 ^ (r ^ 3) * (r + 1) : ℕ) *
            (Fintype.card V + 1 : ℝ≥0) ^
              (r - (((R ∪ A) ∪ K).card + 2)) := by
      exact_mod_cast hcardNat
    have hpower :
        r - (((R ∪ A) ∪ K).card + 2) ≤
          j - 2 - A.card := by omega
    have hcancel := pow_mul_inv_pow_le_one
      (Fintype.card V + 1)
      (r - (((R ∪ A) ∪ K).card + 2))
      (j - 2 - A.card) (by omega) hpower
    calc
      ((familyExtensions
          (exactBankOutsideExtensions r j B R K) A).card : ℝ≥0) *
          ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ (j - 2 - A.card) ≤
          ((2 ^ (r ^ 3) * (r + 1) : ℕ) *
            (Fintype.card V + 1 : ℝ≥0) ^
              (r - (((R ∪ A) ∪ K).card + 2))) *
            ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^
              (j - 2 - A.card) := by
        simpa only [mul_comm] using
          mul_le_mul_right hcard
            (((Fintype.card V + 1 : ℝ≥0)⁻¹) ^
              (j - 2 - A.card))
      _ = (2 ^ (r ^ 3) * (r + 1) : ℕ) *
          ((Fintype.card V + 1 : ℝ≥0) ^
              (r - (((R ∪ A) ∪ K).card + 2)) *
            ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^
              (j - 2 - A.card)) := by
        simp only [mul_assoc]
      _ ≤ (2 ^ (r ^ 3) * (r + 1) : ℕ) := by
        simpa only [Nat.cast_add, Nat.cast_one, mul_comm, one_mul, mul_one] using
          mul_le_mul_left hcancel
            (2 ^ (r ^ 3) * (r + 1) : ℕ)
  · have hempty : familyExtensions
        (exactBankOutsideExtensions r j B R K) A = ∅ :=
      not_nonempty_iff_eq_empty.mp hne
    rw [extensionWeight_exactBankOutsideExtensions, hempty]
    simp

end Erdos207
