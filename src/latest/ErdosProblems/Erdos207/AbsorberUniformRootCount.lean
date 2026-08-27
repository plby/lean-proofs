/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberRootedCount
import ErdosProblems.Erdos207.VortexInducedCount

/-! # Uniform absorber root counts at every root size, including endpoints -/

namespace Erdos207

open Finset

noncomputable section

theorem card_exactBankOutsideExtensions_le_root_weak
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K : TripleSystemOn V}
    (hr : 5 ≤ r) (hR : 1 ≤ R.card) (hRsmall : R.card ≤ j - 2) :
    (exactBankOutsideExtensions r j B R K).card ≤
      (2 ^ (r ^ 3) * (r + 1)) *
        (Fintype.card V + 1) ^ (j - R.card - 2) := by
  by_cases hne : (exactBankOutsideExtensions r j B R K).Nonempty
  · obtain ⟨S, hS⟩ := hne
    have hjr : j ≤ r := exactBank_index_order_le (by omega) hS
    have hrootcard : (R ∪ K).card = R.card + (r - j) := by
      rw [exactBankOutsideExtensions_root_union_card hS,
        exactBankOutsideExtensions_bank_card (by omega) (by omega) hjr hS]
    have hne' : (familyExtensions
        (exactBankOutsideExtensions r j B R K) ∅).Nonempty := by
      simpa [familyExtensions] using (show
        (exactBankOutsideExtensions r j B R K).Nonempty from ⟨S, hS⟩)
    have hroot1 : 1 ≤ ((R ∪ ∅) ∪ K).card := by
      simp only [union_empty, hrootcard]
      omega
    have hb := card_familyExtensions_exactBankOutsideExtensions_le_weak hr hne' hroot1
    have hexp : r - ((R ∪ K).card + 2) = j - R.card - 2 := by
      rw [hrootcard]
      omega
    simpa only [familyExtensions, empty_subset, filter_true, union_empty, hexp] using hb
  · rw [not_nonempty_iff_eq_empty.mp hne]
    simp

theorem card_familyExtensions_absorberInduced_le_weak
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (B R : TripleSystemOn V)
    (hR : 1 ≤ R.card) (hRsmall : R.card ≤ j - 2) :
    (familyExtensions (absorberInducedConfigurationsOn q j B) R).card ≤
      pairExactBankExtensionCoefficient q B *
        (Fintype.card V + 1) ^ (j - R.card - 2) := by
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
          (Fintype.card V + 1) ^ (j - R.card - 2) := by
      apply sum_le_sum
      intro r _
      apply sum_le_sum
      intro K _
      exact card_exactBankOutsideExtensions_le_root_weak
        (mem_Icc.mp r.2).1 hR hRsmall
    _ = _ := by simp only [pairExactBankExtensionCoefficient, sum_mul]

theorem card_familyExtensions_absorberInduced_le_rootExponent
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (B R : TripleSystemOn V)
    (hR : 1 ≤ R.card) (hRsmall : R.card ≤ j - 2) :
    (familyExtensions (absorberInducedConfigurationsOn q j B) R).card ≤
      pairExactBankExtensionCoefficient q B *
        (Fintype.card V + 1) ^ (j - vortexRootExponent j R.card) := by
  by_cases hspecial : R.card = 1 ∨ R.card = j - 2
  · simpa only [vortexRootExponent, if_pos hspecial, Nat.sub_sub] using
      card_familyExtensions_absorberInduced_le_weak q j B R hR hRsmall
  · have hR2 : 2 ≤ R.card := by omega
    have hRlt : R.card < j - 2 := by omega
    simpa only [vortexRootExponent, if_neg hspecial, Nat.sub_sub] using
      card_familyExtensions_absorberInduced_le_strong q j B R hR2 hRlt

end

end Erdos207
