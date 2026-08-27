/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalBankExtensionCount

/-!
# Counting the nonlocal support branch of absorber property A2

In the nonlocal A2 branch an additional outside triangle contains a vertex
of `V(H) \ X`.  We expose that vertex, the triangle, the configuration order,
and the exact bank part.  The remaining family is then a bounded-span class
with the larger root `insert T R ∪ K`, recording the lost ambient-vertex
choice used in KSSS Lemma 7.2.
-/

namespace Erdos207

open Finset

/-- All ambient triples through a fixed vertex. -/
def universeTriplesThrough
    {V : Type*} [Fintype V] [DecidableEq V]
    (v : V) : TripleSystemOn V :=
  (univ : TripleSystemOn V).filter fun T ↦ v ∈ T.1

@[simp]
lemma mem_universeTriplesThrough_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {v : V} {T : TripleOn V} :
    T ∈ universeTriplesThrough v ↔ v ∈ T.1 := by
  simp [universeTriplesThrough]

/-- One exact bank class with an additional distinguished outside triangle. -/
noncomputable def exactBankOutsideExtensionsThrough
    {V : Type*} [Fintype V] [DecidableEq V]
    (r j : ℕ) (B R K : TripleSystemOn V) (T : TripleOn V) :
    ForbiddenFamilyOn V := by
  classical
  exact (exactBankOutsideExtensions r j B R K).filter fun S ↦
    T ∈ S ∧ T ∉ R

@[simp]
lemma mem_exactBankOutsideExtensionsThrough_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K S : TripleSystemOn V} {T : TripleOn V} :
    S ∈ exactBankOutsideExtensionsThrough r j B R K T ↔
      S ∈ exactBankOutsideExtensions r j B R K ∧ T ∈ S ∧ T ∉ R := by
  classical
  simp [exactBankOutsideExtensionsThrough, and_assoc]

/-- Fixing the distinguished outside triangle enlarges the root by that
triangle before the bounded-span count is applied. -/
theorem exactBankOutsideExtensionsThrough_subset_image
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K : TripleSystemOn V} {T : TripleOn V}
    (hr : 5 ≤ r) :
    exactBankOutsideExtensionsThrough r j B R K T ⊆
      (erdosConfigExtensions r (insert T R ∪ K)).image
        (fun z ↦ z.2 \ B) := by
  intro S hS
  obtain ⟨hSexact, hTS, _hTR⟩ :=
    mem_exactBankOutsideExtensionsThrough_iff.mp hS
  obtain ⟨_hScard, hRS, E, hE, hEout, hEin⟩ :=
    mem_exactBankOutsideExtensions_iff.mp hSexact
  have hroot : insert T R ∪ K ⊆ E := by
    intro U hU
    rcases mem_union.mp hU with hUinsert | hUK
    · have hUS : U ∈ S := by
        rw [mem_insert] at hUinsert
        rcases hUinsert with rfl | hUR
        · exact hTS
        · exact hRS hUR
      have hUdiff : U ∈ E \ B := by rw [hEout]; exact hUS
      exact (mem_sdiff.mp hUdiff).1
    · have hUinter : U ∈ E ∩ B := by rw [hEin]; exact hUK
      exact (mem_inter.mp hUinter).1
  apply mem_image.mpr
  exact ⟨(r, E), mem_erdosConfigExtensions_iff.mpr
    ⟨hr, le_rfl, hE, hroot⟩, hEout⟩

theorem card_exactBankOutsideExtensionsThrough_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K : TripleSystemOn V} {T : TripleOn V}
    (hr : 5 ≤ r) :
    (exactBankOutsideExtensionsThrough r j B R K T).card ≤
      2 ^ (r ^ 3) *
        ((r - (verticesOn (insert T R ∪ K)).card + 1) *
          (((univ \ verticesOn (insert T R ∪ K) : Finset V).card + 1) ^
            (r - (verticesOn (insert T R ∪ K)).card))) := by
  calc
    (exactBankOutsideExtensionsThrough r j B R K T).card ≤
        ((erdosConfigExtensions r (insert T R ∪ K)).image
          (fun z ↦ z.2 \ B)).card :=
      card_le_card (exactBankOutsideExtensionsThrough_subset_image hr)
    _ ≤ (erdosConfigExtensions r (insert T R ∪ K)).card := card_image_le
    _ ≤ _ := card_erdosConfigExtensions_le r (insert T R ∪ K)

/-- Literal union of the exposed nonlocal witness classes. -/
noncomputable def supportExactBankExtensionUnion
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (H : SimpleGraph V) (X : Finset V)
    (B R : TripleSystemOn V) : ForbiddenFamilyOn V := by
  classical
  exact (graphSupportFinset H \ X).biUnion fun v ↦
    (universeTriplesThrough v).biUnion fun T ↦
      (Icc 5 q).biUnion fun r ↦
        B.powerset.biUnion fun K ↦
          exactBankOutsideExtensionsThrough r j B R K T

/-- Every A2-nonlocal extension lies in the exposed witness union. -/
theorem absorberInducedSupportExtensions_subset_exact_union
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (H : SimpleGraph V) (X : Finset V)
    (B R : TripleSystemOn V) :
    absorberInducedSupportExtensions q j H X B R ⊆
      supportExactBankExtensionUnion q j H X B R := by
  classical
  intro S hS
  obtain ⟨hSinduced, hRS, r, E, T, v, hr5, hrq, hE, hEout,
    hTS, hTR, hvT, hvH, hvX⟩ :=
    mem_absorberInducedSupportExtensions_iff.mp hS
  obtain ⟨hScard, _r', _hr'5, _hr'q, _E', _hE', _hE'out⟩ :=
    mem_absorberInducedConfigurationsOn_iff.mp hSinduced
  let K := E ∩ B
  have hKB : K ⊆ B := inter_subset_right
  unfold supportExactBankExtensionUnion
  apply mem_biUnion.mpr
  refine ⟨v, mem_sdiff.mpr ⟨hvH, hvX⟩, ?_⟩
  apply mem_biUnion.mpr
  refine ⟨T, mem_universeTriplesThrough_iff.mpr hvT, ?_⟩
  apply mem_biUnion.mpr
  refine ⟨r, mem_Icc.mpr ⟨hr5, hrq⟩, ?_⟩
  apply mem_biUnion.mpr
  refine ⟨K, mem_powerset.mpr hKB, ?_⟩
  apply mem_exactBankOutsideExtensionsThrough_iff.mpr
  exact ⟨mem_exactBankOutsideExtensions_iff.mpr
    ⟨hScard, hRS, E, hE, hEout, rfl⟩, hTS, hTR⟩

/-- Exact iterated-sum bound for the nonlocal branch. -/
theorem card_absorberInducedSupportExtensions_le_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (H : SimpleGraph V) (X : Finset V)
    (B R : TripleSystemOn V) :
    (absorberInducedSupportExtensions q j H X B R).card ≤
      ∑ v ∈ graphSupportFinset H \ X,
        ∑ T ∈ universeTriplesThrough v,
          ∑ r ∈ Icc 5 q, ∑ K ∈ B.powerset,
            (exactBankOutsideExtensionsThrough r j B R K T).card := by
  calc
    (absorberInducedSupportExtensions q j H X B R).card ≤
        (supportExactBankExtensionUnion q j H X B R).card :=
      card_le_card
        (absorberInducedSupportExtensions_subset_exact_union
          q j H X B R)
    _ ≤ ∑ v ∈ graphSupportFinset H \ X,
        ((universeTriplesThrough v).biUnion fun T ↦
          (Icc 5 q).biUnion fun r ↦
            B.powerset.biUnion fun K ↦
              exactBankOutsideExtensionsThrough r j B R K T).card :=
      card_biUnion_le
    _ ≤ ∑ v ∈ graphSupportFinset H \ X,
        ∑ T ∈ universeTriplesThrough v,
          ((Icc 5 q).biUnion fun r ↦
            B.powerset.biUnion fun K ↦
              exactBankOutsideExtensionsThrough r j B R K T).card := by
      apply sum_le_sum
      intro v _hv
      exact card_biUnion_le
    _ ≤ ∑ v ∈ graphSupportFinset H \ X,
        ∑ T ∈ universeTriplesThrough v,
          ∑ r ∈ Icc 5 q,
            (B.powerset.biUnion fun K ↦
              exactBankOutsideExtensionsThrough r j B R K T).card := by
      apply sum_le_sum
      intro v _hv
      apply sum_le_sum
      intro T _hT
      exact card_biUnion_le
    _ ≤ ∑ v ∈ graphSupportFinset H \ X,
        ∑ T ∈ universeTriplesThrough v,
          ∑ r ∈ Icc 5 q, ∑ K ∈ B.powerset,
            (exactBankOutsideExtensionsThrough r j B R K T).card := by
      apply sum_le_sum
      intro v _hv
      apply sum_le_sum
      intro T _hT
      apply sum_le_sum
      intro r _hr
      exact card_biUnion_le

/-- Interior support classes, where adjoining the distinguished support
triangle still leaves at least one unprescribed configuration triangle. -/
noncomputable def supportInteriorExactBankExtensionUnion
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (H : SimpleGraph V) (X : Finset V)
    (B R : TripleSystemOn V) : ForbiddenFamilyOn V := by
  classical
  exact (graphSupportFinset H \ X).biUnion fun v ↦
    (universeTriplesThrough v).biUnion fun T ↦
      (Icc 5 q).biUnion fun r ↦
        B.powerset.biUnion fun K ↦
          if (insert T R ∪ K).card ≤ r - 3 then
            exactBankOutsideExtensionsThrough r j B R K T
          else ∅

/-- Endpoint support classes regrouped without the distinguished support
triangle.  This prevents a spurious independent quadratic triangle count. -/
noncomputable def supportEndpointExactBankExtensionUnion
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (B R : TripleSystemOn V) : ForbiddenFamilyOn V := by
  classical
  exact (Icc 5 q).biUnion fun r ↦
    B.powerset.biUnion fun K ↦
      if (R ∪ K).card = r - 3 then
        exactBankOutsideExtensions r j B R K
      else ∅

/-- Refined A2 support split into strong interior classes and regrouped
endpoint classes. -/
theorem absorberInducedSupportExtensions_subset_refined_union
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (H : SimpleGraph V) (X : Finset V)
    (B R : TripleSystemOn V) :
    absorberInducedSupportExtensions q j H X B R ⊆
      supportInteriorExactBankExtensionUnion q j H X B R ∪
        supportEndpointExactBankExtensionUnion q j B R := by
  classical
  intro S hS
  obtain ⟨hSinduced, hRS, r, E, T, v, hr5, hrq, hE, hEout,
    hTS, hTR, hvT, hvH, hvX⟩ :=
    mem_absorberInducedSupportExtensions_iff.mp hS
  obtain ⟨hScard, _r', _hr'5, _hr'q, _E', _hE', _hE'out⟩ :=
    mem_absorberInducedConfigurationsOn_iff.mp hSinduced
  let K := E ∩ B
  have hKB : K ⊆ B := inter_subset_right
  have hSexact : S ∈ exactBankOutsideExtensions r j B R K :=
    mem_exactBankOutsideExtensions_iff.mpr
      ⟨hScard, hRS, E, hE, hEout, rfl⟩
  have hSThrough :
      S ∈ exactBankOutsideExtensionsThrough r j B R K T :=
    mem_exactBankOutsideExtensionsThrough_iff.mpr ⟨hSexact, hTS, hTR⟩
  have hrootE : insert T R ∪ K ⊆ E := by
    intro U hU
    rcases mem_union.mp hU with hUinsert | hUK
    · have hUS : U ∈ S := by
        rw [mem_insert] at hUinsert
        rcases hUinsert with rfl | hUR
        · exact hTS
        · exact hRS hUR
      exact (mem_sdiff.mp (by rw [hEout]; exact hUS)).1
    · exact (mem_inter.mp (by change U ∈ E ∩ B; exact hUK)).1
  have hrootMax : (insert T R ∪ K).card ≤ r - 2 := by
    have hc := card_le_card hrootE
    rw [hE.1.1] at hc
    exact hc
  by_cases hsmall : (insert T R ∪ K).card ≤ r - 3
  · apply mem_union.mpr
    left
    unfold supportInteriorExactBankExtensionUnion
    apply mem_biUnion.mpr
    refine ⟨v, mem_sdiff.mpr ⟨hvH, hvX⟩, ?_⟩
    apply mem_biUnion.mpr
    refine ⟨T, mem_universeTriplesThrough_iff.mpr hvT, ?_⟩
    apply mem_biUnion.mpr
    refine ⟨r, mem_Icc.mpr ⟨hr5, hrq⟩, ?_⟩
    apply mem_biUnion.mpr
    refine ⟨K, mem_powerset.mpr hKB, ?_⟩
    rw [if_pos hsmall]
    exact hSThrough
  · apply mem_union.mpr
    right
    have hTnotB : T ∉ B := by
      have hTdiff : T ∈ E \ B := by rw [hEout]; exact hTS
      exact (mem_sdiff.mp hTdiff).2
    have hTnotK : T ∉ K := fun hTK ↦ hTnotB (hKB hTK)
    have hTnotUnion : T ∉ R ∪ K := by simp [hTR, hTnotK]
    have hcardInsert : (insert T R ∪ K).card = (R ∪ K).card + 1 := by
      rw [insert_union, card_insert_of_notMem hTnotUnion]
    have hendpointRoot : (R ∪ K).card = r - 3 := by omega
    unfold supportEndpointExactBankExtensionUnion
    apply mem_biUnion.mpr
    refine ⟨r, mem_Icc.mpr ⟨hr5, hrq⟩, ?_⟩
    apply mem_biUnion.mpr
    refine ⟨K, mem_powerset.mpr hKB, ?_⟩
    rw [if_pos hendpointRoot]
    exact hSexact

/-- Cardinal form of the refined support split. -/
theorem card_absorberInducedSupportExtensions_le_refined_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (H : SimpleGraph V) (X : Finset V)
    (B R : TripleSystemOn V) :
    (absorberInducedSupportExtensions q j H X B R).card ≤
      (∑ v ∈ graphSupportFinset H \ X,
        ∑ T ∈ universeTriplesThrough v,
          ∑ r ∈ Icc 5 q, ∑ K ∈ B.powerset,
            if (insert T R ∪ K).card ≤ r - 3 then
              (exactBankOutsideExtensionsThrough r j B R K T).card
            else 0) +
      (∑ r ∈ Icc 5 q, ∑ K ∈ B.powerset,
        if (R ∪ K).card = r - 3 then
          (exactBankOutsideExtensions r j B R K).card
        else 0) := by
  calc
    (absorberInducedSupportExtensions q j H X B R).card ≤
        (supportInteriorExactBankExtensionUnion q j H X B R ∪
          supportEndpointExactBankExtensionUnion q j B R).card :=
      card_le_card
        (absorberInducedSupportExtensions_subset_refined_union
          q j H X B R)
    _ ≤ (supportInteriorExactBankExtensionUnion q j H X B R).card +
        (supportEndpointExactBankExtensionUnion q j B R).card :=
      card_union_le _ _
    _ ≤ (∑ v ∈ graphSupportFinset H \ X,
          ∑ T ∈ universeTriplesThrough v,
            ∑ r ∈ Icc 5 q, ∑ K ∈ B.powerset,
              if (insert T R ∪ K).card ≤ r - 3 then
                (exactBankOutsideExtensionsThrough r j B R K T).card
              else 0) +
        (∑ r ∈ Icc 5 q, ∑ K ∈ B.powerset,
          if (R ∪ K).card = r - 3 then
            (exactBankOutsideExtensions r j B R K).card
          else 0) := by
      apply Nat.add_le_add
      · unfold supportInteriorExactBankExtensionUnion
        refine card_biUnion_le.trans ?_
        apply sum_le_sum
        intro v _hv
        refine card_biUnion_le.trans ?_
        apply sum_le_sum
        intro T _hT
        refine card_biUnion_le.trans ?_
        apply sum_le_sum
        intro r _hr
        refine card_biUnion_le.trans ?_
        apply sum_le_sum
        intro K _hK
        split_ifs <;> simp
      · unfold supportEndpointExactBankExtensionUnion
        refine card_biUnion_le.trans ?_
        apply sum_le_sum
        intro r _hr
        refine card_biUnion_le.trans ?_
        apply sum_le_sum
        intro K _hK
        split_ifs <;> simp

end Erdos207
