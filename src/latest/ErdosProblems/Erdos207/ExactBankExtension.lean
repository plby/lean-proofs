/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteSpanCounting

/-!
# Exact absorber-bank classes in the well-spread count

After fixing the minimal-configuration order and its exact bank part, the
outside extension count is an ordinary bounded-span count rooted at the
union of the prescribed outside triangles and bank triangles.  Minimality
then supplies precisely the extra two or three vertices used in KSSS.
-/

namespace Erdos207

open Finset

/-- Outside parts with `j-2` triangles, a prescribed outside root `R`, and
an exact bank part `K`, completing to an Erdős configuration of order `r`. -/
noncomputable def exactBankOutsideExtensions
    {V : Type*} [Fintype V] [DecidableEq V]
    (r j : ℕ) (B R K : TripleSystemOn V) : ForbiddenFamilyOn V := by
  classical
  exact (univ : Finset (TripleSystemOn V)).filter fun S ↦
    S.card = j - 2 ∧ R ⊆ S ∧
      ∃ E : TripleSystemOn V,
        IsErdosConfigOn r E ∧ E \ B = S ∧ E ∩ B = K

@[simp]
lemma mem_exactBankOutsideExtensions_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K S : TripleSystemOn V} :
    S ∈ exactBankOutsideExtensions r j B R K ↔
      S.card = j - 2 ∧ R ⊆ S ∧
        ∃ E : TripleSystemOn V,
          IsErdosConfigOn r E ∧ E \ B = S ∧ E ∩ B = K := by
  classical
  simp [exactBankOutsideExtensions]

lemma exactBankOutsideExtensions_bank_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K S : TripleSystemOn V}
    (hS : S ∈ exactBankOutsideExtensions r j B R K) : K ⊆ B := by
  obtain ⟨_hScard, _hRS, E, _hE, _hEout, hEin⟩ :=
    mem_exactBankOutsideExtensions_iff.mp hS
  rw [← hEin]
  exact inter_subset_right

lemma exactBankOutsideExtensions_root_bank_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K S : TripleSystemOn V}
    (hS : S ∈ exactBankOutsideExtensions r j B R K) : Disjoint R K := by
  obtain ⟨_hScard, hRS, E, _hE, hEout, hEin⟩ :=
    mem_exactBankOutsideExtensions_iff.mp hS
  rw [Finset.disjoint_left]
  intro T hTR hTK
  have hTS : T ∈ S := hRS hTR
  have hTdiff : T ∈ E \ B := by
    rw [hEout]
    exact hTS
  have hTnotB : T ∉ B := (mem_sdiff.mp hTdiff).2
  exact hTnotB (by
    have : T ∈ E ∩ B := by
      rw [hEin]
      exact hTK
    exact (mem_inter.mp this).2)

lemma exactBankOutsideExtensions_bank_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K S : TripleSystemOn V}
    (hr : 2 ≤ r) (hj : 2 ≤ j) (hjr : j ≤ r)
    (hS : S ∈ exactBankOutsideExtensions r j B R K) :
    K.card = r - j := by
  obtain ⟨hScard, _hRS, E, hE, hEout, hEin⟩ :=
    mem_exactBankOutsideExtensions_iff.mp hS
  have hdecomp : E = S ∪ K := by
    calc
      E = (E \ B) ∪ (E ∩ B) := (sdiff_union_inter E B).symm
      _ = S ∪ K := by rw [hEout, hEin]
  have hdisjoint : Disjoint S K := by
    rw [Finset.disjoint_left]
    intro T hTS hTK
    have hTdiff : T ∈ E \ B := by rw [hEout]; exact hTS
    have hTinter : T ∈ E ∩ B := by rw [hEin]; exact hTK
    exact (mem_sdiff.mp hTdiff).2 (mem_inter.mp hTinter).2
  have hcard := card_union_of_disjoint hdisjoint
  rw [← hdecomp, hE.1.1, hScard] at hcard
  omega

lemma exactBankOutsideExtensions_root_union_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K S : TripleSystemOn V}
    (hS : S ∈ exactBankOutsideExtensions r j B R K) :
    (R ∪ K).card = R.card + K.card := by
  rw [card_union_of_disjoint
    (exactBankOutsideExtensions_root_bank_disjoint hS)]

/-- Every exact-bank outside extension comes from a minimal configuration
extending `R ∪ K`. -/
theorem exactBankOutsideExtensions_subset_image_erdosConfigExtensions
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K : TripleSystemOn V} (hr : 5 ≤ r) :
    exactBankOutsideExtensions r j B R K ⊆
      (erdosConfigExtensions r (R ∪ K)).image (fun z ↦ z.2 \ B) := by
  intro S hS
  obtain ⟨_hScard, hRS, E, hE, hEout, hEin⟩ :=
    mem_exactBankOutsideExtensions_iff.mp hS
  have hroot : R ∪ K ⊆ E := by
    intro T hT
    rcases mem_union.mp hT with hTR | hTK
    · have hTS : T ∈ S := hRS hTR
      have hTdiff : T ∈ E \ B := by rw [hEout]; exact hTS
      exact (mem_sdiff.mp hTdiff).1
    · have hTinter : T ∈ E ∩ B := by rw [hEin]; exact hTK
      exact (mem_inter.mp hTinter).1
  apply mem_image.mpr
  exact ⟨(r, E), mem_erdosConfigExtensions_iff.mpr
    ⟨hr, le_rfl, hE, hroot⟩, hEout⟩

/-- Explicit bounded-span count for one exact bank class. -/
theorem card_exactBankOutsideExtensions_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K : TripleSystemOn V} (hr : 5 ≤ r) :
    (exactBankOutsideExtensions r j B R K).card ≤
      2 ^ (r ^ 3) *
        ((r - (verticesOn (R ∪ K)).card + 1) *
          (((univ \ verticesOn (R ∪ K) : Finset V).card + 1) ^
            (r - (verticesOn (R ∪ K)).card))) := by
  calc
    (exactBankOutsideExtensions r j B R K).card ≤
        ((erdosConfigExtensions r (R ∪ K)).image
          (fun z ↦ z.2 \ B)).card :=
      card_le_card
        (exactBankOutsideExtensions_subset_image_erdosConfigExtensions hr)
    _ ≤ (erdosConfigExtensions r (R ∪ K)).card := card_image_le
    _ ≤ _ := card_erdosConfigExtensions_le r (R ∪ K)

/-- Minimality gives the weak `|root|+2` span exponent for every nonempty
exact root. -/
theorem exactBankOutsideExtensions_root_span_weak
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K S : TripleSystemOn V}
    (hr : 5 ≤ r) (hroot : 1 ≤ (R ∪ K).card)
    (hS : S ∈ exactBankOutsideExtensions r j B R K) :
    (R ∪ K).card + 2 ≤ (verticesOn (R ∪ K)).card := by
  obtain ⟨_hScard, hRS, E, hE, hEout, hEin⟩ :=
    mem_exactBankOutsideExtensions_iff.mp hS
  have hsub : R ∪ K ⊆ E := by
    intro T hT
    rcases mem_union.mp hT with hTR | hTK
    · have hTdiff : T ∈ E \ B := by rw [hEout]; exact hRS hTR
      exact (mem_sdiff.mp hTdiff).1
    · have hTinter : T ∈ E ∩ B := by rw [hEin]; exact hTK
      exact (mem_inter.mp hTinter).1
  apply IsErdosConfig.subset_span_weak hE hr hsub hroot
  exact (card_le_card hsub).trans_eq hE.1.1

/-- Away from the one-triangle and full-root endpoints, minimality gives the
sharper `|root|+3` exponent. -/
theorem exactBankOutsideExtensions_root_span
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K S : TripleSystemOn V}
    (hroot2 : 2 ≤ (R ∪ K).card)
    (hrootsmall : (R ∪ K).card ≤ r - 3)
    (hS : S ∈ exactBankOutsideExtensions r j B R K) :
    (R ∪ K).card + 3 ≤ (verticesOn (R ∪ K)).card := by
  obtain ⟨_hScard, hRS, E, hE, hEout, hEin⟩ :=
    mem_exactBankOutsideExtensions_iff.mp hS
  have hsub : R ∪ K ⊆ E := by
    intro T hT
    rcases mem_union.mp hT with hTR | hTK
    · have hTdiff : T ∈ E \ B := by rw [hEout]; exact hRS hTR
      exact (mem_sdiff.mp hTdiff).1
    · have hTinter : T ∈ E ∩ B := by rw [hEin]; exact hTK
      exact (mem_inter.mp hTinter).1
  exact IsErdosConfig.subset_span hE hsub hroot2 hrootsmall

end Erdos207
