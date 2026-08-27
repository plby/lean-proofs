/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ExactBankInverseWeight

/-!
# A uniform quadratic bound for every exact bank class

The empty-root extension weight of a family of bounded configurations has
the natural quadratic scale `n²`.  As soon as the enlarged exact root is
nonempty, weak minimality cancels all ambient powers.  Combining the two
cases gives one uniform bound that is valid for every further root and is
therefore suitable for `HasExtensionBound`.
-/

namespace Erdos207

open Finset
open scoped NNReal

/-- Every exact bank class has uniform inverse-ambient extension weight at
most its bounded configuration constant times the ambient quadratic scale. -/
theorem extensionWeight_exactBankOutsideExtensions_le_quadratic
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K A : TripleSystemOn V}
    (hr : 5 ≤ r) (hj : 2 ≤ j) :
    extensionWeight
        (fun S : exactBankOutsideExtensions r j B R K ↦ S.1)
        (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) A ≤
      (2 ^ (r ^ 3) * (r + 1) : ℕ) *
        (Fintype.card V + 1 : ℝ≥0) ^ 2 := by
  by_cases hne : (familyExtensions
      (exactBankOutsideExtensions r j B R K) A).Nonempty
  · rw [extensionWeight_exactBankOutsideExtensions]
    have hne' := hne
    obtain ⟨S, hS⟩ := hne
    have hSenlarged :
        S ∈ exactBankOutsideExtensions r j B (R ∪ A) K :=
      familyExtensions_exactBankOutsideExtensions_subset r j B R K A hS
    obtain ⟨hScard, _hrootS, E, hE, hEout, _hEin⟩ :=
      mem_exactBankOutsideExtensions_iff.mp hSenlarged
    have hSsubE : S ⊆ E := by
      intro T hTS
      have hTdiff : T ∈ E \ B := by rw [hEout]; exact hTS
      exact (mem_sdiff.mp hTdiff).1
    have hjr : j ≤ r := by
      have hcard := card_le_card hSsubE
      rw [hScard, hE.1.1] at hcard
      omega
    have hKcard : K.card = r - j :=
      exactBankOutsideExtensions_bank_card (by omega) hj hjr hSenlarged
    have hrootcard : ((R ∪ A) ∪ K).card =
        (R ∪ A).card + K.card :=
      exactBankOutsideExtensions_root_union_card hSenlarged
    have hAroot : A ⊆ (R ∪ A) ∪ K := by
      exact subset_trans subset_union_right subset_union_left
    have hrootlower : A.card + (r - j) ≤ ((R ∪ A) ∪ K).card := by
      have hAcard := card_le_card (subset_union_right : A ⊆ R ∪ A)
      omega
    by_cases hrootzero : ((R ∪ A) ∪ K).card = 0
    · have hAempty : A = ∅ := by
        apply card_eq_zero.mp
        have := card_le_card hAroot
        omega
      have hrootempty : (R ∪ A) ∪ K = ∅ := card_eq_zero.mp hrootzero
      have hrj : r = j := by omega
      have hcardNat :=
        card_familyExtensions_exactBankOutsideExtensions_le
          (r := r) (j := j) (B := B) (R := R) (K := K) (A := A) hr
      have hcard :
          ((familyExtensions
            (exactBankOutsideExtensions r j B R K) A).card : ℝ≥0) ≤
            (2 ^ (r ^ 3) * (r + 1) : ℕ) *
              (Fintype.card V + 1 : ℝ≥0) ^ r := by
        have hcardCast :
            ((familyExtensions
              (exactBankOutsideExtensions r j B R K) A).card : ℝ≥0) ≤
              (2 ^ (r ^ 3) *
                ((r - (verticesOn ((R ∪ A) ∪ K)).card + 1) *
                  (((univ \ verticesOn ((R ∪ A) ∪ K) : Finset V).card + 1) ^
                    (r - (verticesOn ((R ∪ A) ∪ K)).card))) : ℕ) := by
          exact_mod_cast hcardNat
        rw [hrootempty] at hcardCast
        simpa [verticesOn, mul_assoc] using hcardCast
      have hcancel :
          (Fintype.card V + 1 : ℝ≥0) ^ r *
              ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ (j - 2 - A.card) =
            (Fintype.card V + 1 : ℝ≥0) ^ 2 := by
        rw [hAempty, card_empty, Nat.sub_zero, ← hrj]
        have hsub : r - (r - 2) = 2 := by omega
        simpa only [Nat.cast_add, Nat.cast_one, hsub] using
          pow_mul_inv_pow_eq_pow_sub (Fintype.card V + 1)
            r (r - 2) (by omega) (by omega)
      calc
        ((familyExtensions
            (exactBankOutsideExtensions r j B R K) A).card : ℝ≥0) *
            ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^
              (j - 2 - A.card) ≤
            ((2 ^ (r ^ 3) * (r + 1) : ℕ) *
              (Fintype.card V + 1 : ℝ≥0) ^ r) *
              ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^
                (j - 2 - A.card) := by
          simpa only [mul_comm] using mul_le_mul_right hcard
            (((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ (j - 2 - A.card))
        _ = (2 ^ (r ^ 3) * (r + 1) : ℕ) *
            ((Fintype.card V + 1 : ℝ≥0) ^ r *
              ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^
                (j - 2 - A.card)) := by simp only [mul_assoc]
        _ = (2 ^ (r ^ 3) * (r + 1) : ℕ) *
            (Fintype.card V + 1 : ℝ≥0) ^ 2 := by rw [hcancel]
    · have hroot : 1 ≤ ((R ∪ A) ∪ K).card :=
        Nat.one_le_iff_ne_zero.mpr hrootzero
      have hcardNat :=
        card_familyExtensions_exactBankOutsideExtensions_le_weak
          hr hne' hroot
      have hcard :
          ((familyExtensions
            (exactBankOutsideExtensions r j B R K) A).card : ℝ≥0) ≤
            (2 ^ (r ^ 3) * (r + 1) : ℕ) *
              (Fintype.card V + 1 : ℝ≥0) ^
                (r - (((R ∪ A) ∪ K).card + 2)) := by
        exact_mod_cast hcardNat
      have hpower : r - (((R ∪ A) ∪ K).card + 2) ≤
          j - 2 - A.card := by omega
      have hcancel := pow_mul_inv_pow_le_one
        (Fintype.card V + 1)
        (r - (((R ∪ A) ∪ K).card + 2))
        (j - 2 - A.card) (by omega) hpower
      have hone : (1 : ℝ≥0) ≤ (Fintype.card V + 1 : ℝ≥0) ^ 2 := by
        exact one_le_pow₀ (by exact_mod_cast (show 1 ≤ Fintype.card V + 1 by omega))
      calc
        ((familyExtensions
            (exactBankOutsideExtensions r j B R K) A).card : ℝ≥0) *
            ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^
              (j - 2 - A.card) ≤
            ((2 ^ (r ^ 3) * (r + 1) : ℕ) *
              (Fintype.card V + 1 : ℝ≥0) ^
                (r - (((R ∪ A) ∪ K).card + 2))) *
              ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^
                (j - 2 - A.card) := by
          simpa only [mul_comm] using mul_le_mul_right hcard
            (((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ (j - 2 - A.card))
        _ = (2 ^ (r ^ 3) * (r + 1) : ℕ) *
            ((Fintype.card V + 1 : ℝ≥0) ^
                (r - (((R ∪ A) ∪ K).card + 2)) *
              ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^
                (j - 2 - A.card)) := by simp only [mul_assoc]
        _ ≤ (2 ^ (r ^ 3) * (r + 1) : ℕ) * 1 := by
          simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using
            mul_le_mul_right hcancel (2 ^ (r ^ 3) * (r + 1) : ℕ)
        _ ≤ (2 ^ (r ^ 3) * (r + 1) : ℕ) *
            (Fintype.card V + 1 : ℝ≥0) ^ 2 :=
          by
            simpa only [mul_comm] using
              mul_le_mul_left hone (2 ^ (r ^ 3) * (r + 1) : ℕ)
  · have hempty : familyExtensions
        (exactBankOutsideExtensions r j B R K) A = ∅ :=
      not_nonempty_iff_eq_empty.mp hne
    rw [extensionWeight_exactBankOutsideExtensions, hempty]
    simp

/-- Once the prescribed outside root is nonempty, weak minimality cancels the
quadratic empty-root scale completely. -/
theorem extensionWeight_exactBankOutsideExtensions_self_le_constant
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K : TripleSystemOn V}
    (hr : 5 ≤ r) (hj : 2 ≤ j) (hR : 1 ≤ R.card) :
    extensionWeight
        (fun S : exactBankOutsideExtensions r j B R K ↦ S.1)
        (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) R ≤
      (2 ^ (r ^ 3) * (r + 1) : ℕ) := by
  have hself :
      familyExtensions (exactBankOutsideExtensions r j B R K) R =
        exactBankOutsideExtensions r j B R K := by
    ext S
    constructor
    · exact fun hS ↦ (mem_familyExtensions_iff.mp hS).1
    · intro hS
      exact mem_familyExtensions_iff.mpr
        ⟨hS, (mem_exactBankOutsideExtensions_iff.mp hS).2.1⟩
  change extensionWeight
      (fun S : exactBankOutsideExtensions r j B R K ↦ S.1)
      (fun _ ↦ (Fintype.card V + 1 : ℝ≥0)⁻¹) R ≤ _
  rw [extensionWeight_constant_eq _ (j - 2)
    exactBankOutsideExtensions_fixed_card
    ((Fintype.card V + 1 : ℝ≥0)⁻¹) R, hself]
  by_cases hne : (exactBankOutsideExtensions r j B R K).Nonempty
  · obtain ⟨S, hS⟩ := hne
    have hSfamily :
        S ∈ familyExtensions (exactBankOutsideExtensions r j B R K) R := by
      rw [hself]
      exact hS
    have hSenlarged :
        S ∈ exactBankOutsideExtensions r j B (R ∪ R) K :=
      familyExtensions_exactBankOutsideExtensions_subset r j B R K R hSfamily
    obtain ⟨hScard, _hrootS, E, hE, hEout, _hEin⟩ :=
      mem_exactBankOutsideExtensions_iff.mp hSenlarged
    have hSsubE : S ⊆ E := by
      intro T hTS
      have hTdiff : T ∈ E \ B := by rw [hEout]; exact hTS
      exact (mem_sdiff.mp hTdiff).1
    have hjr : j ≤ r := by
      have hc := card_le_card hSsubE
      rw [hScard, hE.1.1] at hc
      omega
    have hKcard := exactBankOutsideExtensions_bank_card
      (by omega : 2 ≤ r) hj hjr hSenlarged
    have hrootcard := exactBankOutsideExtensions_root_union_card hSenlarged
    have hroot : 1 ≤ ((R ∪ R) ∪ K).card := by
      have hRsub : R ⊆ (R ∪ R) ∪ K :=
        subset_trans subset_union_left subset_union_left
      have hc := card_le_card hRsub
      omega
    have hrootlower : R.card + (r - j) ≤ ((R ∪ R) ∪ K).card := by
      have hRunion : R.card ≤ (R ∪ R).card :=
        card_le_card subset_union_left
      omega
    have hcardNat :=
      card_familyExtensions_exactBankOutsideExtensions_le_weak
        hr ⟨S, hSfamily⟩ hroot
    rw [hself] at hcardNat
    have hcard :
        ((exactBankOutsideExtensions r j B R K).card : ℝ≥0) ≤
          (2 ^ (r ^ 3) * (r + 1) : ℕ) *
            (Fintype.card V + 1 : ℝ≥0) ^
              (r - (((R ∪ R) ∪ K).card + 2)) := by
      exact_mod_cast hcardNat
    have hpower : r - (((R ∪ R) ∪ K).card + 2) ≤
        j - 2 - R.card := by omega
    have hcancel := pow_mul_inv_pow_le_one
      (Fintype.card V + 1)
      (r - (((R ∪ R) ∪ K).card + 2))
      (j - 2 - R.card) (by omega) hpower
    calc
      ((exactBankOutsideExtensions r j B R K).card : ℝ≥0) *
          ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ (j - 2 - R.card) ≤
        ((2 ^ (r ^ 3) * (r + 1) : ℕ) *
          (Fintype.card V + 1 : ℝ≥0) ^
            (r - (((R ∪ R) ∪ K).card + 2))) *
          ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^
            (j - 2 - R.card) := by
        simpa only [mul_comm] using mul_le_mul_right hcard
          (((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ (j - 2 - R.card))
      _ = (2 ^ (r ^ 3) * (r + 1) : ℕ) *
          ((Fintype.card V + 1 : ℝ≥0) ^
              (r - (((R ∪ R) ∪ K).card + 2)) *
            ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^
              (j - 2 - R.card)) := by simp only [mul_assoc]
      _ ≤ (2 ^ (r ^ 3) * (r + 1) : ℕ) * 1 := by
        simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using
          mul_le_mul_right hcancel (2 ^ (r ^ 3) * (r + 1) : ℕ)
      _ = (2 ^ (r ^ 3) * (r + 1) : ℕ) := by simp
  · have hempty : exactBankOutsideExtensions r j B R K = ∅ :=
      not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    simp

end Erdos207
