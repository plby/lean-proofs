/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SupportBankWeightedBound

/-!
# Weighted indexed absorber-extension theorem

This is the direct weighted form of the uniform A2 split.  For every
prescribed outside root, one bounded local bank controls the local classes;
all remaining extensions lie in the explicitly exposed support branch.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

lemma absorberInducedConfigurationsOn_fixed_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {q j : ℕ} {B : TripleSystemOn V} :
    ∀ S ∈ absorberInducedConfigurationsOn q j B,
      S.card = j - 2 := by
  intro S hS
  exact (mem_absorberInducedConfigurationsOn_iff.mp hS).1

lemma familyExtensions_absorberInducedConfigurationsOn
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (B R : TripleSystemOn V) :
    familyExtensions (absorberInducedConfigurationsOn q j B) R =
      absorberInducedExtensions q j B R := by
  ext S
  rw [mem_familyExtensions_iff, mem_absorberInducedExtensions_iff]

/-- Uniform weighted A2 split for one indexed family and one prescribed
outside root. -/
theorem exists_local_bank_extensionWeight_absorberInduced_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M j : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B R : TripleSystemOn V}
    (hA2 : HasAbsorberLocalization q M H X B)
    (hRq : R.card ≤ q) (hj : 2 ≤ j) :
    ∃ L : TripleSystemOn V, L ⊆ B ∧ L.card ≤ M ∧
      extensionWeight
          (fun S : absorberInducedConfigurationsOn q j B ↦ S.1)
          (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) R ≤
        (∑ r ∈ Icc 5 q, ∑ _K ∈ L.powerset,
          (2 ^ (r ^ 3) * (r + 1) : ℕ) *
            (Fintype.card V + 1 : ℝ≥0) ^ 2) +
        (∑ v ∈ graphSupportFinset H \ X,
          ∑ _T ∈ universeTriplesThrough v,
            ∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j),
              (2 ^ (r ^ 3) * (r + 1) : ℕ) *
                (Fintype.card V + 1 : ℝ≥0)⁻¹) := by
  obtain ⟨L, hLB, hLM, hsplit⟩ :=
    card_absorberInducedExtensions_le_split hA2 hRq
  refine ⟨L, hLB, hLM, ?_⟩
  let p : ℝ≥0 := (Fintype.card V + 1 : ℝ≥0)⁻¹
  have hcard :
      ((absorberInducedExtensions q j B R).card : ℝ≥0) ≤
        (absorberInducedLocalExtensions q j B R L).card +
          (absorberInducedSupportExtensions q j H X B R).card := by
    exact_mod_cast hsplit
  have hlocalEq :
      extensionWeight
          (fun S : absorberInducedLocalExtensions q j B R L ↦ S.1)
          (constantTripleWeight p) R =
        ((absorberInducedLocalExtensions q j B R L).card : ℝ≥0) *
          p ^ (j - 2 - R.card) := by
    change extensionWeight
      (fun S : absorberInducedLocalExtensions q j B R L ↦ S.1)
      (fun _ ↦ p) R = _
    rw [extensionWeight_constant_eq _ (j - 2)
      absorberInducedLocalExtensions_fixed_card p R,
      familyExtensions_absorberInducedLocalExtensions_self]
  have hsupportEq :
      extensionWeight
          (fun S : absorberInducedSupportExtensions q j H X B R ↦ S.1)
          (constantTripleWeight p) R =
        ((absorberInducedSupportExtensions q j H X B R).card : ℝ≥0) *
          p ^ (j - 2 - R.card) := by
    change extensionWeight
      (fun S : absorberInducedSupportExtensions q j H X B R ↦ S.1)
      (fun _ ↦ p) R = _
    rw [extensionWeight_constant_eq _ (j - 2)
      absorberInducedSupportExtensions_fixed_card p R,
      familyExtensions_absorberInducedSupportExtensions_self]
  change extensionWeight
      (fun S : absorberInducedConfigurationsOn q j B ↦ S.1)
      (fun _ ↦ p) R ≤ _
  rw [extensionWeight_constant_eq _ (j - 2)
    absorberInducedConfigurationsOn_fixed_card p R,
    familyExtensions_absorberInducedConfigurationsOn]
  calc
    ((absorberInducedExtensions q j B R).card : ℝ≥0) *
        p ^ (j - 2 - R.card) ≤
      (((absorberInducedLocalExtensions q j B R L).card : ℝ≥0) +
        (absorberInducedSupportExtensions q j H X B R).card) *
          p ^ (j - 2 - R.card) := by
      simpa only [mul_comm] using
        mul_le_mul_right hcard (p ^ (j - 2 - R.card))
    _ = extensionWeight
          (fun S : absorberInducedLocalExtensions q j B R L ↦ S.1)
          (constantTripleWeight p) R +
        extensionWeight
          (fun S : absorberInducedSupportExtensions q j H X B R ↦ S.1)
          (constantTripleWeight p) R := by
      rw [add_mul, hlocalEq, hsupportEq]
    _ ≤ (∑ r ∈ Icc 5 q, ∑ _K ∈ L.powerset,
          (2 ^ (r ^ 3) * (r + 1) : ℕ) *
            (Fintype.card V + 1 : ℝ≥0) ^ 2) +
        (∑ v ∈ graphSupportFinset H \ X,
          ∑ _T ∈ universeTriplesThrough v,
            ∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j),
              (2 ^ (r ^ 3) * (r + 1) : ℕ) *
                (Fintype.card V + 1 : ℝ≥0)⁻¹) := by
      apply add_le_add
      · exact extensionWeight_absorberInducedLocalExtensions_le_sum
          q j B R L hj
      · exact extensionWeight_absorberInducedSupportExtensions_le_sum
          q j H X B R hj

/-- The rooted version of the weighted A2 split.  Once the prescribed
outside root contains at least one triangle, the local exact classes have
constant rather than quadratic ambient scale. -/
theorem exists_local_bank_extensionWeight_absorberInduced_le_of_nonempty
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M j : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B R : TripleSystemOn V}
    (hA2 : HasAbsorberLocalization q M H X B)
    (hRq : R.card ≤ q) (hj : 2 ≤ j) (hR : 1 ≤ R.card) :
    ∃ L : TripleSystemOn V, L ⊆ B ∧ L.card ≤ M ∧
      extensionWeight
          (fun S : absorberInducedConfigurationsOn q j B ↦ S.1)
          (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) R ≤
        (∑ r ∈ Icc 5 q, ∑ _K ∈ L.powerset,
          (2 ^ (r ^ 3) * (r + 1) : ℕ)) +
        (∑ v ∈ graphSupportFinset H \ X,
          ∑ _T ∈ universeTriplesThrough v,
            ∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j),
              (2 ^ (r ^ 3) * (r + 1) : ℕ) *
                (Fintype.card V + 1 : ℝ≥0)⁻¹) := by
  obtain ⟨L, hLB, hLM, hsplit⟩ :=
    card_absorberInducedExtensions_le_split hA2 hRq
  refine ⟨L, hLB, hLM, ?_⟩
  let p : ℝ≥0 := (Fintype.card V + 1 : ℝ≥0)⁻¹
  have hcard :
      ((absorberInducedExtensions q j B R).card : ℝ≥0) ≤
        (absorberInducedLocalExtensions q j B R L).card +
          (absorberInducedSupportExtensions q j H X B R).card := by
    exact_mod_cast hsplit
  have hlocalEq :
      extensionWeight
          (fun S : absorberInducedLocalExtensions q j B R L ↦ S.1)
          (constantTripleWeight p) R =
        ((absorberInducedLocalExtensions q j B R L).card : ℝ≥0) *
          p ^ (j - 2 - R.card) := by
    change extensionWeight
      (fun S : absorberInducedLocalExtensions q j B R L ↦ S.1)
      (fun _ ↦ p) R = _
    rw [extensionWeight_constant_eq _ (j - 2)
      absorberInducedLocalExtensions_fixed_card p R,
      familyExtensions_absorberInducedLocalExtensions_self]
  have hsupportEq :
      extensionWeight
          (fun S : absorberInducedSupportExtensions q j H X B R ↦ S.1)
          (constantTripleWeight p) R =
        ((absorberInducedSupportExtensions q j H X B R).card : ℝ≥0) *
          p ^ (j - 2 - R.card) := by
    change extensionWeight
      (fun S : absorberInducedSupportExtensions q j H X B R ↦ S.1)
      (fun _ ↦ p) R = _
    rw [extensionWeight_constant_eq _ (j - 2)
      absorberInducedSupportExtensions_fixed_card p R,
      familyExtensions_absorberInducedSupportExtensions_self]
  change extensionWeight
      (fun S : absorberInducedConfigurationsOn q j B ↦ S.1)
      (fun _ ↦ p) R ≤ _
  rw [extensionWeight_constant_eq _ (j - 2)
    absorberInducedConfigurationsOn_fixed_card p R,
    familyExtensions_absorberInducedConfigurationsOn]
  calc
    ((absorberInducedExtensions q j B R).card : ℝ≥0) *
        p ^ (j - 2 - R.card) ≤
      (((absorberInducedLocalExtensions q j B R L).card : ℝ≥0) +
        (absorberInducedSupportExtensions q j H X B R).card) *
          p ^ (j - 2 - R.card) := by
      simpa only [mul_comm] using
        mul_le_mul_right hcard (p ^ (j - 2 - R.card))
    _ = extensionWeight
          (fun S : absorberInducedLocalExtensions q j B R L ↦ S.1)
          (constantTripleWeight p) R +
        extensionWeight
          (fun S : absorberInducedSupportExtensions q j H X B R ↦ S.1)
          (constantTripleWeight p) R := by
      rw [add_mul, hlocalEq, hsupportEq]
    _ ≤ (∑ r ∈ Icc 5 q, ∑ _K ∈ L.powerset,
          (2 ^ (r ^ 3) * (r + 1) : ℕ)) +
        (∑ v ∈ graphSupportFinset H \ X,
          ∑ _T ∈ universeTriplesThrough v,
            ∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j),
              (2 ^ (r ^ 3) * (r + 1) : ℕ) *
                (Fintype.card V + 1 : ℝ≥0)⁻¹) := by
      apply add_le_add
      · exact extensionWeight_absorberInducedLocalExtensions_le_sum_of_nonempty
          q j B R L hj hR
      · exact extensionWeight_absorberInducedSupportExtensions_le_sum
          q j H X B R hj

/-- Refined rooted A2 split with the support endpoint regrouping. -/
theorem exists_local_bank_extensionWeight_absorberInduced_le_refined
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M j : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B R : TripleSystemOn V}
    (hA2 : HasAbsorberLocalization q M H X B)
    (hRq : R.card ≤ q) (hj : 2 ≤ j) (hR : 1 ≤ R.card) :
    ∃ L : TripleSystemOn V, L ⊆ B ∧ L.card ≤ M ∧
      extensionWeight
          (fun S : absorberInducedConfigurationsOn q j B ↦ S.1)
          (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) R ≤
        (∑ r ∈ Icc 5 q, ∑ _K ∈ L.powerset,
          (2 ^ (r ^ 3) * (r + 1) : ℕ)) +
        ((∑ v ∈ graphSupportFinset H \ X,
          ∑ _T ∈ universeTriplesThrough v,
            ∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j),
              (2 ^ (r ^ 3) * (r + 1) : ℕ) *
                ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ 2) +
          (∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j),
            (2 ^ (r ^ 3) * (r + 1) : ℕ) *
              (Fintype.card V + 1 : ℝ≥0)⁻¹)) := by
  obtain ⟨L, hLB, hLM, hsplit⟩ :=
    card_absorberInducedExtensions_le_split hA2 hRq
  refine ⟨L, hLB, hLM, ?_⟩
  let p : ℝ≥0 := (Fintype.card V + 1 : ℝ≥0)⁻¹
  have hcard :
      ((absorberInducedExtensions q j B R).card : ℝ≥0) ≤
        (absorberInducedLocalExtensions q j B R L).card +
          (absorberInducedSupportExtensions q j H X B R).card := by
    exact_mod_cast hsplit
  have hlocalEq :
      extensionWeight
          (fun S : absorberInducedLocalExtensions q j B R L ↦ S.1)
          (constantTripleWeight p) R =
        ((absorberInducedLocalExtensions q j B R L).card : ℝ≥0) *
          p ^ (j - 2 - R.card) := by
    change extensionWeight
      (fun S : absorberInducedLocalExtensions q j B R L ↦ S.1)
      (fun _ ↦ p) R = _
    rw [extensionWeight_constant_eq _ (j - 2)
      absorberInducedLocalExtensions_fixed_card p R,
      familyExtensions_absorberInducedLocalExtensions_self]
  have hsupportEq :
      extensionWeight
          (fun S : absorberInducedSupportExtensions q j H X B R ↦ S.1)
          (constantTripleWeight p) R =
        ((absorberInducedSupportExtensions q j H X B R).card : ℝ≥0) *
          p ^ (j - 2 - R.card) := by
    change extensionWeight
      (fun S : absorberInducedSupportExtensions q j H X B R ↦ S.1)
      (fun _ ↦ p) R = _
    rw [extensionWeight_constant_eq _ (j - 2)
      absorberInducedSupportExtensions_fixed_card p R,
      familyExtensions_absorberInducedSupportExtensions_self]
  change extensionWeight
      (fun S : absorberInducedConfigurationsOn q j B ↦ S.1)
      (fun _ ↦ p) R ≤ _
  rw [extensionWeight_constant_eq _ (j - 2)
    absorberInducedConfigurationsOn_fixed_card p R,
    familyExtensions_absorberInducedConfigurationsOn]
  calc
    ((absorberInducedExtensions q j B R).card : ℝ≥0) *
        p ^ (j - 2 - R.card) ≤
      (((absorberInducedLocalExtensions q j B R L).card : ℝ≥0) +
        (absorberInducedSupportExtensions q j H X B R).card) *
          p ^ (j - 2 - R.card) := by
      simpa only [mul_comm] using
        mul_le_mul_right hcard (p ^ (j - 2 - R.card))
    _ = extensionWeight
          (fun S : absorberInducedLocalExtensions q j B R L ↦ S.1)
          (constantTripleWeight p) R +
        extensionWeight
          (fun S : absorberInducedSupportExtensions q j H X B R ↦ S.1)
          (constantTripleWeight p) R := by
      rw [add_mul, hlocalEq, hsupportEq]
    _ ≤ (∑ r ∈ Icc 5 q, ∑ _K ∈ L.powerset,
          (2 ^ (r ^ 3) * (r + 1) : ℕ)) +
        ((∑ v ∈ graphSupportFinset H \ X,
          ∑ _T ∈ universeTriplesThrough v,
            ∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j),
              (2 ^ (r ^ 3) * (r + 1) : ℕ) *
                ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ 2) +
          (∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j),
            (2 ^ (r ^ 3) * (r + 1) : ℕ) *
              (Fintype.card V + 1 : ℝ≥0)⁻¹)) := by
      apply add_le_add
      · exact extensionWeight_absorberInducedLocalExtensions_le_sum_of_nonempty
          q j B R L hj hR
      · exact extensionWeight_absorberInducedSupportExtensions_le_refined_sum
          q j H X B R hj hR

end Erdos207
