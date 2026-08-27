/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ExactBankQuadraticWeight

/-!
# Weighted A2-local extension bound

The local branch of absorber property A2 is a union over boundedly many
configuration orders and subsets of one bounded local bank.  Combining the
exact cardinal union bound with the uniform quadratic estimate for every
exact class gives the corresponding extension-weight estimate.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

lemma absorberInducedLocalExtensions_fixed_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {q j : ℕ} {B R L : TripleSystemOn V} :
    ∀ S ∈ absorberInducedLocalExtensions q j B R L,
      S.card = j - 2 := by
  intro S hS
  exact (mem_absorberInducedConfigurationsOn_iff.mp
    (mem_absorberInducedLocalExtensions_iff.mp hS).1).1

lemma familyExtensions_absorberInducedLocalExtensions_self
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (B R L : TripleSystemOn V) :
    familyExtensions (absorberInducedLocalExtensions q j B R L) R =
      absorberInducedLocalExtensions q j B R L := by
  ext S
  constructor
  · exact fun hS ↦ (mem_familyExtensions_iff.mp hS).1
  · intro hS
    apply mem_familyExtensions_iff.mpr
    exact ⟨hS, (mem_absorberInducedLocalExtensions_iff.mp hS).2.1⟩

lemma familyExtensions_exactBankOutsideExtensions_self
    {V : Type*} [Fintype V] [DecidableEq V]
    (r j : ℕ) (B R K : TripleSystemOn V) :
    familyExtensions (exactBankOutsideExtensions r j B R K) R =
      exactBankOutsideExtensions r j B R K := by
  ext S
  constructor
  · exact fun hS ↦ (mem_familyExtensions_iff.mp hS).1
  · intro hS
    apply mem_familyExtensions_iff.mpr
    exact ⟨hS, (mem_exactBankOutsideExtensions_iff.mp hS).2.1⟩

/-- Exact iterated-sum extension-weight bound for the A2-local branch. -/
theorem extensionWeight_absorberInducedLocalExtensions_le_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (B R L : TripleSystemOn V) (hj : 2 ≤ j) :
    extensionWeight
        (fun S : absorberInducedLocalExtensions q j B R L ↦ S.1)
        (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) R ≤
      ∑ r ∈ Icc 5 q, ∑ _K ∈ L.powerset,
        (2 ^ (r ^ 3) * (r + 1) : ℕ) *
          (Fintype.card V + 1 : ℝ≥0) ^ 2 := by
  change extensionWeight
      (fun S : absorberInducedLocalExtensions q j B R L ↦ S.1)
      (fun _ ↦ (Fintype.card V + 1 : ℝ≥0)⁻¹) R ≤ _
  rw [extensionWeight_constant_eq _ (j - 2)
    absorberInducedLocalExtensions_fixed_card
    ((Fintype.card V + 1 : ℝ≥0)⁻¹) R]
  rw [familyExtensions_absorberInducedLocalExtensions_self]
  have hcardNat :=
    card_absorberInducedLocalExtensions_le_sum q j B R L
  have hcard :
      ((absorberInducedLocalExtensions q j B R L).card : ℝ≥0) ≤
        (∑ r ∈ Icc 5 q, ∑ K ∈ L.powerset,
          (exactBankOutsideExtensions r j B R K).card : ℕ) := by
    exact_mod_cast hcardNat
  calc
    ((absorberInducedLocalExtensions q j B R L).card : ℝ≥0) *
        ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ (j - 2 - R.card) ≤
      (∑ r ∈ Icc 5 q, ∑ K ∈ L.powerset,
        (exactBankOutsideExtensions r j B R K).card : ℕ) *
          ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^
            (j - 2 - R.card) := by
      simpa only [mul_comm] using mul_le_mul_right hcard
        (((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ (j - 2 - R.card))
    _ = ∑ r ∈ Icc 5 q, ∑ K ∈ L.powerset,
        ((exactBankOutsideExtensions r j B R K).card : ℝ≥0) *
          ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^
            (j - 2 - R.card) := by
      simp only [Nat.cast_sum, sum_mul]
    _ ≤ ∑ r ∈ Icc 5 q, ∑ _K ∈ L.powerset,
        (2 ^ (r ^ 3) * (r + 1) : ℕ) *
          (Fintype.card V + 1 : ℝ≥0) ^ 2 := by
      apply sum_le_sum
      intro r hrq
      apply sum_le_sum
      intro K _hKL
      have hr5 : 5 ≤ r := (mem_Icc.mp hrq).1
      have hquad :=
        extensionWeight_exactBankOutsideExtensions_le_quadratic
          (V := V) (r := r) (j := j) (B := B) (R := R)
          (K := K) (A := R) hr5 hj
      rw [extensionWeight_exactBankOutsideExtensions,
        familyExtensions_exactBankOutsideExtensions_self] at hquad
      exact hquad

/-- With a nonempty prescribed outside root, the local branch loses the
quadratic empty-root factor. -/
theorem extensionWeight_absorberInducedLocalExtensions_le_sum_of_nonempty
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (B R L : TripleSystemOn V) (hj : 2 ≤ j)
    (hR : 1 ≤ R.card) :
    extensionWeight
        (fun S : absorberInducedLocalExtensions q j B R L ↦ S.1)
        (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) R ≤
      ∑ r ∈ Icc 5 q, ∑ _K ∈ L.powerset,
        (2 ^ (r ^ 3) * (r + 1) : ℕ) := by
  change extensionWeight
      (fun S : absorberInducedLocalExtensions q j B R L ↦ S.1)
      (fun _ ↦ (Fintype.card V + 1 : ℝ≥0)⁻¹) R ≤ _
  rw [extensionWeight_constant_eq _ (j - 2)
    absorberInducedLocalExtensions_fixed_card
    ((Fintype.card V + 1 : ℝ≥0)⁻¹) R]
  rw [familyExtensions_absorberInducedLocalExtensions_self]
  have hcardNat :=
    card_absorberInducedLocalExtensions_le_sum q j B R L
  have hcard :
      ((absorberInducedLocalExtensions q j B R L).card : ℝ≥0) ≤
        (∑ r ∈ Icc 5 q, ∑ K ∈ L.powerset,
          (exactBankOutsideExtensions r j B R K).card : ℕ) := by
    exact_mod_cast hcardNat
  calc
    ((absorberInducedLocalExtensions q j B R L).card : ℝ≥0) *
        ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ (j - 2 - R.card) ≤
      (∑ r ∈ Icc 5 q, ∑ K ∈ L.powerset,
        (exactBankOutsideExtensions r j B R K).card : ℕ) *
          ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^
            (j - 2 - R.card) := by
      simpa only [mul_comm] using mul_le_mul_right hcard
        (((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ (j - 2 - R.card))
    _ = ∑ r ∈ Icc 5 q, ∑ K ∈ L.powerset,
        ((exactBankOutsideExtensions r j B R K).card : ℝ≥0) *
          ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^
            (j - 2 - R.card) := by
      simp only [Nat.cast_sum, sum_mul]
    _ ≤ ∑ r ∈ Icc 5 q, ∑ _K ∈ L.powerset,
        (2 ^ (r ^ 3) * (r + 1) : ℕ) := by
      simp only [Nat.cast_sum]
      apply sum_le_sum
      intro r hrq
      apply sum_le_sum
      intro K _hKL
      have hr5 : 5 ≤ r := (mem_Icc.mp hrq).1
      have hconstant :=
        extensionWeight_exactBankOutsideExtensions_self_le_constant
          (V := V) (r := r) (j := j) (B := B) (R := R)
          (K := K) hr5 hj hR
      change extensionWeight
          (fun S : exactBankOutsideExtensions r j B R K ↦ S.1)
          (fun _ ↦ (Fintype.card V + 1 : ℝ≥0)⁻¹) R ≤ _ at hconstant
      rw [extensionWeight_constant_eq _ (j - 2)
        exactBankOutsideExtensions_fixed_card
        ((Fintype.card V + 1 : ℝ≥0)⁻¹) R,
        familyExtensions_exactBankOutsideExtensions_self] at hconstant
      exact hconstant

end Erdos207
