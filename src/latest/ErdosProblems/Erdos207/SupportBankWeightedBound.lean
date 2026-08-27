/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalBankWeightedBound

/-!
# Weighted A2 support-branch bound

The nonlocal branch exposes a non-flexible absorber vertex and an outside
triangle through it.  This file first records the exact weighted iterated
sum over those witnesses.  The sharper lost-vertex estimate can subsequently
replace the quadratic per-class term without changing the decomposition.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

lemma absorberInducedSupportExtensions_fixed_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {q j : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B R : TripleSystemOn V} :
    ∀ S ∈ absorberInducedSupportExtensions q j H X B R,
      S.card = j - 2 := by
  intro S hS
  exact (mem_absorberInducedConfigurationsOn_iff.mp
    (mem_absorberInducedSupportExtensions_iff.mp hS).1).1

lemma familyExtensions_absorberInducedSupportExtensions_self
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (H : SimpleGraph V) (X : Finset V)
    (B R : TripleSystemOn V) :
    familyExtensions (absorberInducedSupportExtensions q j H X B R) R =
      absorberInducedSupportExtensions q j H X B R := by
  ext S
  constructor
  · exact fun hS ↦ (mem_familyExtensions_iff.mp hS).1
  · intro hS
    apply mem_familyExtensions_iff.mpr
    exact ⟨hS, (mem_absorberInducedSupportExtensions_iff.mp hS).2.1⟩

lemma familyExtensions_exactBankOutsideExtensionsThrough_self
    {V : Type*} [Fintype V] [DecidableEq V]
    (r j : ℕ) (B R K : TripleSystemOn V) (T : TripleOn V) :
    familyExtensions (exactBankOutsideExtensionsThrough r j B R K T) R =
      exactBankOutsideExtensionsThrough r j B R K T := by
  ext S
  constructor
  · exact fun hS ↦ (mem_familyExtensions_iff.mp hS).1
  · intro hS
    apply mem_familyExtensions_iff.mpr
    exact ⟨hS,
      (mem_exactBankOutsideExtensions_iff.mp
        (mem_exactBankOutsideExtensionsThrough_iff.mp hS).1).2.1⟩

/-- Exposing a distinguished outside triangle not already in the prescribed
root gains one full inverse ambient factor for each exact nonlocal class. -/
theorem extensionWeight_exactBankOutsideExtensionsThrough_le_inv
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K : TripleSystemOn V} {T : TripleOn V}
    (hr : 5 ≤ r) (hj : 2 ≤ j) :
    extensionWeight
        (fun S : exactBankOutsideExtensionsThrough r j B R K T ↦ S.1)
        (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) R ≤
      (2 ^ (r ^ 3) * (r + 1) : ℕ) *
        (Fintype.card V + 1 : ℝ≥0)⁻¹ := by
  by_cases hne : (exactBankOutsideExtensionsThrough r j B R K T).Nonempty
  · obtain ⟨S, hS⟩ := hne
    obtain ⟨hSexact, hTS, hTR⟩ :=
      mem_exactBankOutsideExtensionsThrough_iff.mp hS
    obtain ⟨hScard, hRS, E, hE, hEout, hEin⟩ :=
      mem_exactBankOutsideExtensions_iff.mp hSexact
    have hSsubE : S ⊆ E := by
      intro U hUS
      have hUdiff : U ∈ E \ B := by rw [hEout]; exact hUS
      exact (mem_sdiff.mp hUdiff).1
    have hjr : j ≤ r := by
      have hc := card_le_card hSsubE
      rw [hScard, hE.1.1] at hc
      omega
    have hrootE : ({T} ∪ R) ∪ K ⊆ E := by
      intro U hU
      rcases mem_union.mp hU with hUout | hUK
      · rcases mem_union.mp hUout with hUT | hUR
        · have : U = T := by simpa using hUT
          subst U
          exact hSsubE hTS
        · exact hSsubE (hRS hUR)
      · have hUinter : U ∈ E ∩ B := by rw [hEin]; exact hUK
        exact (mem_inter.mp hUinter).1
    have hrootsmall : (({T} ∪ R) ∪ K).card ≤ r - 2 := by
      have hc := card_le_card hrootE
      rw [hE.1.1] at hc
      omega
    have hdisjoint : Disjoint ({T} : TripleSystemOn V) R := by
      simpa [Finset.disjoint_left] using hTR
    have hgeneric :=
      extensionWeight_exactBankOutsideExtensions_le_inv_weak
        (V := V) (r := r) (j := j) (B := B)
        (R := ({T} : TripleSystemOn V)) (K := K) (A := R)
        hr hj hjr hdisjoint (by simp) hrootsmall
    rw [extensionWeight_exactBankOutsideExtensions] at hgeneric
    change extensionWeight
        (fun S : exactBankOutsideExtensionsThrough r j B R K T ↦ S.1)
        (fun _ ↦ (Fintype.card V + 1 : ℝ≥0)⁻¹) R ≤ _
    rw [extensionWeight_constant_eq _ (j - 2)
      exactBankOutsideExtensionsThrough_fixed_card
      ((Fintype.card V + 1 : ℝ≥0)⁻¹) R,
      familyExtensions_exactBankOutsideExtensionsThrough_self]
    have hsub : exactBankOutsideExtensionsThrough r j B R K T ⊆
        familyExtensions
          (exactBankOutsideExtensions r j B ({T} : TripleSystemOn V) K) R := by
      intro U hU
      obtain ⟨hUexact, hTU, _hTRU⟩ :=
        mem_exactBankOutsideExtensionsThrough_iff.mp hU
      obtain ⟨hUcard, hRU, E', hE', hE'out, hE'in⟩ :=
        mem_exactBankOutsideExtensions_iff.mp hUexact
      apply mem_familyExtensions_iff.mpr
      refine ⟨mem_exactBankOutsideExtensions_iff.mpr ?_, hRU⟩
      exact ⟨hUcard, by simpa using hTU, E', hE', hE'out, hE'in⟩
    have hc :
        ((exactBankOutsideExtensionsThrough r j B R K T).card : ℝ≥0) ≤
          (familyExtensions
            (exactBankOutsideExtensions r j B ({T} : TripleSystemOn V) K)
            R).card := by
      exact_mod_cast card_le_card hsub
    have hmul :
        ((exactBankOutsideExtensionsThrough r j B R K T).card : ℝ≥0) *
            ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ (j - 2 - R.card) ≤
          ((familyExtensions
            (exactBankOutsideExtensions r j B ({T} : TripleSystemOn V) K)
            R).card : ℝ≥0) *
            ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ (j - 2 - R.card) := by
      simpa only [mul_comm] using mul_le_mul_right hc
        (((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ (j - 2 - R.card))
    exact hmul.trans hgeneric
  · have hempty : exactBankOutsideExtensionsThrough r j B R K T = ∅ :=
      not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    simp [extensionWeight]

/-- Away from the endpoint, a pre-existing outside root and the newly
exposed support triangle leave two inverse ambient factors. -/
theorem extensionWeight_exactBankOutsideExtensionsThrough_le_inv_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K : TripleSystemOn V} {T : TripleOn V}
    (hr : 5 ≤ r) (hj : 2 ≤ j) (hR : 1 ≤ R.card)
    (hrootsmall : (({T} ∪ R) ∪ K).card ≤ r - 3) :
    extensionWeight
        (fun S : exactBankOutsideExtensionsThrough r j B R K T ↦ S.1)
        (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) R ≤
      (2 ^ (r ^ 3) * (r + 1) : ℕ) *
        ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ 2 := by
  by_cases hne : (exactBankOutsideExtensionsThrough r j B R K T).Nonempty
  · obtain ⟨S, hS⟩ := hne
    obtain ⟨hSexact, hTS, hTR⟩ :=
      mem_exactBankOutsideExtensionsThrough_iff.mp hS
    obtain ⟨hScard, hRS, E, hE, hEout, hEin⟩ :=
      mem_exactBankOutsideExtensions_iff.mp hSexact
    have hSsubE : S ⊆ E := by
      intro U hUS
      have hUdiff : U ∈ E \ B := by rw [hEout]; exact hUS
      exact (mem_sdiff.mp hUdiff).1
    have hjr : j ≤ r := by
      have hc := card_le_card hSsubE
      rw [hScard, hE.1.1] at hc
      omega
    have hdisjoint : Disjoint ({T} : TripleSystemOn V) R := by
      simpa [Finset.disjoint_left] using hTR
    have hroot2 : 2 ≤ (({T} ∪ R) ∪ K).card := by
      have hcardTR : ({T} ∪ R : TripleSystemOn V).card = 1 + R.card := by
        rw [card_union_of_disjoint hdisjoint]
        simp
      have hsub : ({T} ∪ R : TripleSystemOn V) ⊆ ({T} ∪ R) ∪ K :=
        subset_union_left
      have hc := card_le_card hsub
      omega
    have hgeneric :=
      extensionWeight_exactBankOutsideExtensions_le_inv_sq_strong
        (V := V) (r := r) (j := j) (B := B)
        (R := ({T} : TripleSystemOn V)) (K := K) (A := R)
        hr hj hjr hdisjoint (by simp) hroot2 hrootsmall
    rw [extensionWeight_exactBankOutsideExtensions] at hgeneric
    change extensionWeight
        (fun S : exactBankOutsideExtensionsThrough r j B R K T ↦ S.1)
        (fun _ ↦ (Fintype.card V + 1 : ℝ≥0)⁻¹) R ≤ _
    rw [extensionWeight_constant_eq _ (j - 2)
      exactBankOutsideExtensionsThrough_fixed_card
      ((Fintype.card V + 1 : ℝ≥0)⁻¹) R,
      familyExtensions_exactBankOutsideExtensionsThrough_self]
    have hsub : exactBankOutsideExtensionsThrough r j B R K T ⊆
        familyExtensions
          (exactBankOutsideExtensions r j B ({T} : TripleSystemOn V) K) R := by
      intro U hU
      obtain ⟨hUexact, hTU, _hTRU⟩ :=
        mem_exactBankOutsideExtensionsThrough_iff.mp hU
      obtain ⟨hUcard, hRU, E', hE', hE'out, hE'in⟩ :=
        mem_exactBankOutsideExtensions_iff.mp hUexact
      apply mem_familyExtensions_iff.mpr
      refine ⟨mem_exactBankOutsideExtensions_iff.mpr ?_, hRU⟩
      exact ⟨hUcard, by simpa using hTU, E', hE', hE'out, hE'in⟩
    have hc :
        ((exactBankOutsideExtensionsThrough r j B R K T).card : ℝ≥0) ≤
          (familyExtensions
            (exactBankOutsideExtensions r j B ({T} : TripleSystemOn V) K)
            R).card := by
      exact_mod_cast card_le_card hsub
    have hmul :
        ((exactBankOutsideExtensionsThrough r j B R K T).card : ℝ≥0) *
            ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ (j - 2 - R.card) ≤
          ((familyExtensions
            (exactBankOutsideExtensions r j B ({T} : TripleSystemOn V) K)
            R).card : ℝ≥0) *
            ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^
              (j - 2 - R.card) := by
      simpa only [mul_comm] using mul_le_mul_right hc
        (((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ (j - 2 - R.card))
    exact hmul.trans hgeneric
  · have hempty : exactBankOutsideExtensionsThrough r j B R K T = ∅ :=
      not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    simp [extensionWeight]

/-- An exact class is empty unless the fixed bank part has its forced size. -/
lemma exactBankOutsideExtensionsThrough_eq_empty_of_bank_card_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K : TripleSystemOn V} {T : TripleOn V}
    (hr : 2 ≤ r) (hj : 2 ≤ j) (hK : K.card ≠ r - j) :
    exactBankOutsideExtensionsThrough r j B R K T = ∅ := by
  apply not_nonempty_iff_eq_empty.mp
  intro hne
  obtain ⟨S, hS⟩ := hne
  have hSexact := (mem_exactBankOutsideExtensionsThrough_iff.mp hS).1
  obtain ⟨hScard, _hRS, E, hE, hEout, _hEin⟩ :=
    mem_exactBankOutsideExtensions_iff.mp hSexact
  have hSsubE : S ⊆ E := by
    intro U hUS
    have hUdiff : U ∈ E \ B := by rw [hEout]; exact hUS
    exact (mem_sdiff.mp hUdiff).1
  have hjr : j ≤ r := by
    have hc := card_le_card hSsubE
    rw [hScard, hE.1.1] at hc
    omega
  exact hK (exactBankOutsideExtensions_bank_card hr hj hjr hSexact)

/-- The powerset sum may be restricted to the forced bank-part size. -/
lemma sum_powerset_exactBankOutsideExtensionsThrough_card_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} (B R : TripleSystemOn V) (T : TripleOn V)
    (hr : 2 ≤ r) (hj : 2 ≤ j) :
    (∑ K ∈ B.powerset,
      (exactBankOutsideExtensionsThrough r j B R K T).card) =
      ∑ K ∈ B.powersetCard (r - j),
        (exactBankOutsideExtensionsThrough r j B R K T).card := by
  symm
  apply Finset.sum_subset
  · intro K hK
    exact mem_powerset.mpr (mem_powersetCard.mp hK).1
  · intro K hKB hKnot
    have hKcard : K.card ≠ r - j := by
      intro hcard
      exact hKnot (mem_powersetCard.mpr
        ⟨mem_powerset.mp hKB, hcard⟩)
    rw [exactBankOutsideExtensionsThrough_eq_empty_of_bank_card_ne
      hr hj hKcard, card_empty]

lemma exactBankOutsideExtensions_eq_empty_of_bank_card_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K : TripleSystemOn V}
    (hr : 2 ≤ r) (hj : 2 ≤ j) (hK : K.card ≠ r - j) :
    exactBankOutsideExtensions r j B R K = ∅ := by
  apply not_nonempty_iff_eq_empty.mp
  rintro ⟨S, hS⟩
  obtain ⟨hScard, _hRS, E, hE, hEout, _hEin⟩ :=
    mem_exactBankOutsideExtensions_iff.mp hS
  have hSsubE : S ⊆ E := by
    intro U hUS
    exact (mem_sdiff.mp (by rw [hEout]; exact hUS)).1
  have hjr : j ≤ r := by
    have hc := card_le_card hSsubE
    rw [hScard, hE.1.1] at hc
    omega
  exact hK (exactBankOutsideExtensions_bank_card hr hj hjr hS)

lemma sum_powerset_if_exactBankOutsideExtensionsThrough_card_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} (B R : TripleSystemOn V) (T : TripleOn V)
    (hr : 2 ≤ r) (hj : 2 ≤ j) :
    (∑ K ∈ B.powerset,
      if (insert T R ∪ K).card ≤ r - 3 then
        (exactBankOutsideExtensionsThrough r j B R K T).card else 0) =
      ∑ K ∈ B.powersetCard (r - j),
        if (insert T R ∪ K).card ≤ r - 3 then
          (exactBankOutsideExtensionsThrough r j B R K T).card else 0 := by
  symm
  apply Finset.sum_subset
  · intro K hK
    exact mem_powerset.mpr (mem_powersetCard.mp hK).1
  · intro K hKB hKnot
    have hKcard : K.card ≠ r - j := by
      intro hcard
      exact hKnot (mem_powersetCard.mpr
        ⟨mem_powerset.mp hKB, hcard⟩)
    rw [exactBankOutsideExtensionsThrough_eq_empty_of_bank_card_ne
      hr hj hKcard]
    split_ifs <;> simp

lemma sum_powerset_if_endpoint_exactBankOutsideExtensions_card_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} (B R : TripleSystemOn V)
    (hr : 2 ≤ r) (hj : 2 ≤ j) :
    (∑ K ∈ B.powerset,
      if (R ∪ K).card = r - 3 then
        (exactBankOutsideExtensions r j B R K).card else 0) =
      ∑ K ∈ B.powersetCard (r - j),
        if (R ∪ K).card = r - 3 then
          (exactBankOutsideExtensions r j B R K).card else 0 := by
  symm
  apply Finset.sum_subset
  · intro K hK
    exact mem_powerset.mpr (mem_powersetCard.mp hK).1
  · intro K hKB hKnot
    have hKcard : K.card ≠ r - j := by
      intro hcard
      exact hKnot (mem_powersetCard.mpr
        ⟨mem_powerset.mp hKB, hcard⟩)
    rw [exactBankOutsideExtensions_eq_empty_of_bank_card_ne
      hr hj hKcard]
    split_ifs <;> simp

/-- Refined support weight for a nonempty root.  Interior support classes
gain two inverse factors; endpoint classes are regrouped by their exact bank
part and gain one. -/
theorem extensionWeight_absorberInducedSupportExtensions_le_refined_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (H : SimpleGraph V) (X : Finset V)
    (B R : TripleSystemOn V) (hj : 2 ≤ j) (hR : 1 ≤ R.card) :
    extensionWeight
        (fun S : absorberInducedSupportExtensions q j H X B R ↦ S.1)
        (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) R ≤
      (∑ v ∈ graphSupportFinset H \ X,
        ∑ _T ∈ universeTriplesThrough v,
          ∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j),
            (2 ^ (r ^ 3) * (r + 1) : ℕ) *
              ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ 2) +
      (∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j),
        (2 ^ (r ^ 3) * (r + 1) : ℕ) *
          (Fintype.card V + 1 : ℝ≥0)⁻¹) := by
  change extensionWeight
      (fun S : absorberInducedSupportExtensions q j H X B R ↦ S.1)
      (fun _ ↦ (Fintype.card V + 1 : ℝ≥0)⁻¹) R ≤ _
  rw [extensionWeight_constant_eq _ (j - 2)
    absorberInducedSupportExtensions_fixed_card
    ((Fintype.card V + 1 : ℝ≥0)⁻¹) R,
    familyExtensions_absorberInducedSupportExtensions_self]
  have hcardNat :=
    card_absorberInducedSupportExtensions_le_refined_sum
      q j H X B R
  have hcardSized :
      (absorberInducedSupportExtensions q j H X B R).card ≤
        (∑ v ∈ graphSupportFinset H \ X,
          ∑ T ∈ universeTriplesThrough v,
            ∑ r ∈ Icc 5 q, ∑ K ∈ B.powersetCard (r - j),
              if (insert T R ∪ K).card ≤ r - 3 then
                (exactBankOutsideExtensionsThrough r j B R K T).card
              else 0) +
        (∑ r ∈ Icc 5 q, ∑ K ∈ B.powersetCard (r - j),
          if (R ∪ K).card = r - 3 then
            (exactBankOutsideExtensions r j B R K).card else 0) := by
    calc
      (absorberInducedSupportExtensions q j H X B R).card ≤
          (∑ v ∈ graphSupportFinset H \ X,
            ∑ T ∈ universeTriplesThrough v,
              ∑ r ∈ Icc 5 q, ∑ K ∈ B.powerset,
                if (insert T R ∪ K).card ≤ r - 3 then
                  (exactBankOutsideExtensionsThrough r j B R K T).card
                else 0) +
          (∑ r ∈ Icc 5 q, ∑ K ∈ B.powerset,
            if (R ∪ K).card = r - 3 then
              (exactBankOutsideExtensions r j B R K).card else 0) := hcardNat
      _ = _ := by
        congr 1
        · apply sum_congr rfl
          intro v _hv
          apply sum_congr rfl
          intro T _hT
          apply sum_congr rfl
          intro r hrq
          exact sum_powerset_if_exactBankOutsideExtensionsThrough_card_eq
            B R T (by have := (mem_Icc.mp hrq).1; omega) hj
        · apply sum_congr rfl
          intro r hrq
          exact sum_powerset_if_endpoint_exactBankOutsideExtensions_card_eq
            B R (by have := (mem_Icc.mp hrq).1; omega) hj
  let Z : ℕ :=
    (∑ v ∈ graphSupportFinset H \ X,
      ∑ T ∈ universeTriplesThrough v,
        ∑ r ∈ Icc 5 q, ∑ K ∈ B.powersetCard (r - j),
          if (insert T R ∪ K).card ≤ r - 3 then
            (exactBankOutsideExtensionsThrough r j B R K T).card
          else 0) +
    (∑ r ∈ Icc 5 q, ∑ K ∈ B.powersetCard (r - j),
      if (R ∪ K).card = r - 3 then
        (exactBankOutsideExtensions r j B R K).card else 0)
  have hcard :
      ((absorberInducedSupportExtensions q j H X B R).card : ℝ≥0) ≤
        (Z : ℝ≥0) := by
    exact_mod_cast hcardSized
  calc
    ((absorberInducedSupportExtensions q j H X B R).card : ℝ≥0) *
        ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ (j - 2 - R.card) ≤
      (Z : ℝ≥0) * ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^
        (j - 2 - R.card) := by
      exact mul_le_mul_left hcard
        (((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ (j - 2 - R.card))
    _ = (∑ v ∈ graphSupportFinset H \ X,
          ∑ T ∈ universeTriplesThrough v,
            ∑ r ∈ Icc 5 q, ∑ K ∈ B.powersetCard (r - j),
              (if (insert T R ∪ K).card ≤ r - 3 then
                ((exactBankOutsideExtensionsThrough r j B R K T).card : ℝ≥0)
              else 0) *
                ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^
                  (j - 2 - R.card)) +
        (∑ r ∈ Icc 5 q, ∑ K ∈ B.powersetCard (r - j),
          (if (R ∪ K).card = r - 3 then
            ((exactBankOutsideExtensions r j B R K).card : ℝ≥0) else 0) *
              ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^
                (j - 2 - R.card)) := by
      simp only [Z, Nat.cast_add, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero,
        add_mul, sum_mul]
    _ ≤ (∑ v ∈ graphSupportFinset H \ X,
          ∑ _T ∈ universeTriplesThrough v,
            ∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j),
              (2 ^ (r ^ 3) * (r + 1) : ℕ) *
                ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ 2) +
        (∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j),
          (2 ^ (r ^ 3) * (r + 1) : ℕ) *
            (Fintype.card V + 1 : ℝ≥0)⁻¹) := by
      apply add_le_add
      · apply sum_le_sum
        intro v _hv
        apply sum_le_sum
        intro T _hT
        apply sum_le_sum
        intro r hrq
        apply sum_le_sum
        intro K _hK
        split_ifs with hsmall
        · have hb :=
            extensionWeight_exactBankOutsideExtensionsThrough_le_inv_sq
              (V := V) (r := r) (j := j) (B := B) (R := R)
              (K := K) (T := T) (mem_Icc.mp hrq).1 hj hR hsmall
          change extensionWeight
              (fun S : exactBankOutsideExtensionsThrough r j B R K T ↦ S.1)
              (fun _ ↦ (Fintype.card V + 1 : ℝ≥0)⁻¹) R ≤ _ at hb
          rw [extensionWeight_constant_eq _ (j - 2)
            exactBankOutsideExtensionsThrough_fixed_card
            ((Fintype.card V + 1 : ℝ≥0)⁻¹) R,
            familyExtensions_exactBankOutsideExtensionsThrough_self] at hb
          exact hb
        · simp
      · apply sum_le_sum
        intro r hrq
        apply sum_le_sum
        intro K _hK
        split_ifs with hendpoint
        · have hroot2 : 2 ≤ (R ∪ K).card := by
            rw [hendpoint]
            have := (mem_Icc.mp hrq).1
            omega
          have hb :=
            extensionWeight_exactBankOutsideExtensions_self_le_inv_strong
              (V := V) (r := r) (j := j) (B := B) (R := R) (K := K)
              (mem_Icc.mp hrq).1 hj hroot2 (by rw [hendpoint])
          change extensionWeight
              (fun S : exactBankOutsideExtensions r j B R K ↦ S.1)
              (fun _ ↦ (Fintype.card V + 1 : ℝ≥0)⁻¹) R ≤ _ at hb
          rw [extensionWeight_constant_eq _ (j - 2)
            exactBankOutsideExtensions_fixed_card
            ((Fintype.card V + 1 : ℝ≥0)⁻¹) R,
            familyExtensions_exactBankOutsideExtensions_self] at hb
          exact hb
        · simp

/-- Exact iterated-sum extension-weight bound for the nonlocal support
branch. -/
theorem extensionWeight_absorberInducedSupportExtensions_le_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (H : SimpleGraph V) (X : Finset V)
    (B R : TripleSystemOn V) (hj : 2 ≤ j) :
    extensionWeight
        (fun S : absorberInducedSupportExtensions q j H X B R ↦ S.1)
        (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) R ≤
      ∑ v ∈ graphSupportFinset H \ X,
        ∑ _T ∈ universeTriplesThrough v,
          ∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j),
            (2 ^ (r ^ 3) * (r + 1) : ℕ) *
              (Fintype.card V + 1 : ℝ≥0)⁻¹ := by
  change extensionWeight
      (fun S : absorberInducedSupportExtensions q j H X B R ↦ S.1)
      (fun _ ↦ (Fintype.card V + 1 : ℝ≥0)⁻¹) R ≤ _
  rw [extensionWeight_constant_eq _ (j - 2)
    absorberInducedSupportExtensions_fixed_card
    ((Fintype.card V + 1 : ℝ≥0)⁻¹) R]
  rw [familyExtensions_absorberInducedSupportExtensions_self]
  have hcardNat :=
    card_absorberInducedSupportExtensions_le_sum q j H X B R
  have hcardSized :
      (absorberInducedSupportExtensions q j H X B R).card ≤
        ∑ v ∈ graphSupportFinset H \ X,
          ∑ T ∈ universeTriplesThrough v,
            ∑ r ∈ Icc 5 q, ∑ K ∈ B.powersetCard (r - j),
              (exactBankOutsideExtensionsThrough r j B R K T).card := by
    calc
      (absorberInducedSupportExtensions q j H X B R).card ≤
          ∑ v ∈ graphSupportFinset H \ X,
            ∑ T ∈ universeTriplesThrough v,
              ∑ r ∈ Icc 5 q, ∑ K ∈ B.powerset,
                (exactBankOutsideExtensionsThrough r j B R K T).card :=
        hcardNat
      _ = ∑ v ∈ graphSupportFinset H \ X,
          ∑ T ∈ universeTriplesThrough v,
            ∑ r ∈ Icc 5 q, ∑ K ∈ B.powersetCard (r - j),
              (exactBankOutsideExtensionsThrough r j B R K T).card := by
        apply sum_congr rfl
        intro v _hv
        apply sum_congr rfl
        intro T _hT
        apply sum_congr rfl
        intro r hrq
        exact sum_powerset_exactBankOutsideExtensionsThrough_card_eq
          B R T (by have := (mem_Icc.mp hrq).1; omega) hj
  have hcard :
      ((absorberInducedSupportExtensions q j H X B R).card : ℝ≥0) ≤
        (∑ v ∈ graphSupportFinset H \ X,
          ∑ T ∈ universeTriplesThrough v,
            ∑ r ∈ Icc 5 q, ∑ K ∈ B.powersetCard (r - j),
              (exactBankOutsideExtensionsThrough r j B R K T).card : ℕ) := by
    exact_mod_cast hcardSized
  calc
    ((absorberInducedSupportExtensions q j H X B R).card : ℝ≥0) *
        ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ (j - 2 - R.card) ≤
      (∑ v ∈ graphSupportFinset H \ X,
        ∑ T ∈ universeTriplesThrough v,
          ∑ r ∈ Icc 5 q, ∑ K ∈ B.powersetCard (r - j),
            (exactBankOutsideExtensionsThrough r j B R K T).card : ℕ) *
        ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^
          (j - 2 - R.card) := by
      simpa only [mul_comm] using mul_le_mul_right hcard
        (((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ (j - 2 - R.card))
    _ = ∑ v ∈ graphSupportFinset H \ X,
        ∑ T ∈ universeTriplesThrough v,
          ∑ r ∈ Icc 5 q, ∑ K ∈ B.powersetCard (r - j),
            ((exactBankOutsideExtensionsThrough r j B R K T).card : ℝ≥0) *
              ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^
                (j - 2 - R.card) := by
      simp only [Nat.cast_sum, sum_mul]
    _ ≤ ∑ v ∈ graphSupportFinset H \ X,
        ∑ T ∈ universeTriplesThrough v,
          ∑ r ∈ Icc 5 q, ∑ _K ∈ B.powersetCard (r - j),
            (2 ^ (r ^ 3) * (r + 1) : ℕ) *
              (Fintype.card V + 1 : ℝ≥0)⁻¹ := by
      apply sum_le_sum
      intro v _hv
      apply sum_le_sum
      intro T _hT
      apply sum_le_sum
      intro r hrq
      apply sum_le_sum
      intro K _hKB
      have hr5 : 5 ≤ r := (mem_Icc.mp hrq).1
      have hdistinguished :=
        extensionWeight_exactBankOutsideExtensionsThrough_le_inv
          (V := V) (r := r) (j := j) (B := B) (R := R)
          (K := K) (T := T) hr5 hj
      change extensionWeight
          (fun S : exactBankOutsideExtensionsThrough r j B R K T ↦ S.1)
          (fun _ ↦ (Fintype.card V + 1 : ℝ≥0)⁻¹) R ≤ _ at hdistinguished
      rw [extensionWeight_constant_eq _ (j - 2)
        exactBankOutsideExtensionsThrough_fixed_card
        ((Fintype.card V + 1 : ℝ≥0)⁻¹) R,
        familyExtensions_exactBankOutsideExtensionsThrough_self] at hdistinguished
      exact hdistinguished

end Erdos207
