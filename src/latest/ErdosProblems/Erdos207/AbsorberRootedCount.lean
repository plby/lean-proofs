/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PairTwoAwayAbsorberBound

/-! # Strong two-root counts for absorber-induced configuration families -/

namespace Erdos207

open Finset

noncomputable section

theorem familyExtensions_absorberInduced_subset_exact_cover
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (B R : TripleSystemOn V) :
    familyExtensions (absorberInducedConfigurationsOn q j B) R ⊆
      univ.biUnion (fun r : (Icc 5 q : Finset ℕ) ↦
        univ.biUnion (fun K : subsetsUpToCard B q ↦
          exactBankOutsideExtensions r.1 j B R K.1)) := by
  intro S hS
  obtain ⟨hSF, hRS⟩ := mem_familyExtensions_iff.mp hS
  obtain ⟨hcard, r, hr5, hrq, E, hE, hEout⟩ :=
    mem_absorberInducedConfigurationsOn_iff.mp hSF
  have hK : E ∩ B ∈ subsetsUpToCard B q := by
    apply mem_subsetsUpToCard_iff.mpr
    refine ⟨inter_subset_right, ?_⟩
    calc
      (E ∩ B).card ≤ E.card := card_le_card inter_subset_left
      _ = r - 2 := hE.1.1
      _ ≤ q := by omega
  apply mem_biUnion.mpr
  refine ⟨⟨r, mem_Icc.mpr ⟨hr5, hrq⟩⟩, mem_univ _, ?_⟩
  apply mem_biUnion.mpr
  refine ⟨⟨E ∩ B, hK⟩, mem_univ _, ?_⟩
  exact mem_exactBankOutsideExtensions_iff.mpr
    ⟨hcard, hRS, E, hE, hEout, rfl⟩

theorem card_exactBankOutsideExtensions_le_root_strong
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K : TripleSystemOn V}
    (hr : 5 ≤ r) (hR : 2 ≤ R.card) (hRsmall : R.card < j - 2) :
    (exactBankOutsideExtensions r j B R K).card ≤
      (2 ^ (r ^ 3) * (r + 1)) *
        (Fintype.card V + 1) ^ (j - R.card - 3) := by
  by_cases hne : (exactBankOutsideExtensions r j B R K).Nonempty
  · obtain ⟨S, hS⟩ := hne
    obtain ⟨hScard, _, E, hE, hEout, _⟩ :=
      mem_exactBankOutsideExtensions_iff.mp hS
    have hjr : j ≤ r := by
      have hsize : S.card ≤ E.card := by
        rw [← hEout]
        exact card_le_card sdiff_subset
      rw [hScard, hE.1.1] at hsize
      omega
    have hrootcard : (R ∪ K).card = R.card + (r - j) := by
      rw [exactBankOutsideExtensions_root_union_card hS,
        exactBankOutsideExtensions_bank_card (by omega) (by omega) hjr hS]
    have hne' : (familyExtensions
        (exactBankOutsideExtensions r j B R K) ∅).Nonempty := by
      simpa [familyExtensions] using (show
        (exactBankOutsideExtensions r j B R K).Nonempty from ⟨S, hS⟩)
    have hroot2 : 2 ≤ ((R ∪ ∅) ∪ K).card := by
      simpa only [union_empty, hrootcard] using
        (show 2 ≤ R.card + (r - j) by omega)
    have hrootsmall : ((R ∪ ∅) ∪ K).card ≤ r - 3 := by
      simp only [union_empty, hrootcard]
      omega
    have hb := card_familyExtensions_exactBankOutsideExtensions_le_strong
      hr hne' hroot2 hrootsmall
    have hexp : r - ((R ∪ K).card + 3) = j - R.card - 3 := by
      rw [hrootcard]
      omega
    simpa only [familyExtensions, empty_subset, filter_true,
      union_empty, hexp] using hb
  · rw [not_nonempty_iff_eq_empty.mp hne]
    simp

/-- The coefficient counts only bank subsets of cardinality at most `q`.
Thus it is polynomial, not exponential, in the bank cardinality. -/
theorem card_familyExtensions_absorberInduced_le_strong
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (B R : TripleSystemOn V)
    (hR : 2 ≤ R.card) (hRsmall : R.card < j - 2) :
    (familyExtensions (absorberInducedConfigurationsOn q j B) R).card ≤
      pairExactBankExtensionCoefficient q B *
        (Fintype.card V + 1) ^ (j - R.card - 3) := by
  calc
    (familyExtensions (absorberInducedConfigurationsOn q j B) R).card ≤
        (univ.biUnion (fun r : (Icc 5 q : Finset ℕ) ↦
          univ.biUnion (fun K : subsetsUpToCard B q ↦
            exactBankOutsideExtensions r.1 j B R K.1))).card :=
      card_le_card (familyExtensions_absorberInduced_subset_exact_cover q j B R)
    _ ≤ ∑ r : (Icc 5 q : Finset ℕ), ∑ K : subsetsUpToCard B q,
        (exactBankOutsideExtensions r.1 j B R K.1).card :=
      card_biUnion_le.trans (sum_le_sum fun _ _ ↦ card_biUnion_le)
    _ ≤ ∑ r : (Icc 5 q : Finset ℕ), ∑ _K : subsetsUpToCard B q,
        (2 ^ (r.1 ^ 3) * (r.1 + 1)) *
          (Fintype.card V + 1) ^ (j - R.card - 3) := by
      apply sum_le_sum
      intro r _
      apply sum_le_sum
      intro K _
      exact card_exactBankOutsideExtensions_le_root_strong
        (mem_Icc.mp r.2).1 hR hRsmall
    _ = _ := by simp only [pairExactBankExtensionCoefficient, sum_mul]

end

end Erdos207
