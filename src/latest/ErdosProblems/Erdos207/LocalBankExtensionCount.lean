/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ExactBankExtension

/-!
# Counting the local branch of absorber property A2

Once A2 fixes a local bank `L`, every local outside extension belongs to one
of only `q * 2^|L|` exact `(r,K)` classes.  Each class is controlled by the
bounded-span estimates from `ExactBankExtension`.
-/

namespace Erdos207

open Finset

/-- Union of all exact bank classes with order at most `q` and bank part
contained in a prescribed local bank `L`. -/
noncomputable def localExactBankExtensionUnion
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (B R L : TripleSystemOn V) : ForbiddenFamilyOn V := by
  classical
  exact (Icc 5 q).biUnion fun r ↦
    L.powerset.biUnion fun K ↦ exactBankOutsideExtensions r j B R K

@[simp]
lemma mem_localExactBankExtensionUnion_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {q j : ℕ} {B R L S : TripleSystemOn V} :
    S ∈ localExactBankExtensionUnion q j B R L ↔
      ∃ r, 5 ≤ r ∧ r ≤ q ∧
        ∃ K ⊆ L, S ∈ exactBankOutsideExtensions r j B R K := by
  classical
  simp [localExactBankExtensionUnion, and_assoc]

/-- Every extension in the A2-local branch lies in an exact class with bank
part contained in `L`. -/
theorem absorberInducedLocalExtensions_subset_exact_union
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (B R L : TripleSystemOn V) :
    absorberInducedLocalExtensions q j B R L ⊆
      localExactBankExtensionUnion q j B R L := by
  intro S hS
  obtain ⟨hSinduced, hRS, hlocal⟩ :=
    mem_absorberInducedLocalExtensions_iff.mp hS
  obtain ⟨hScard, r, hr5, hrq, E, hE, hEout⟩ :=
    mem_absorberInducedConfigurationsOn_iff.mp hSinduced
  let K := E ∩ B
  have hKL : K ⊆ L := hlocal r E hr5 hrq hE hEout
  apply mem_localExactBankExtensionUnion_iff.mpr
  refine ⟨r, hr5, hrq, K, hKL, ?_⟩
  apply mem_exactBankOutsideExtensions_iff.mpr
  exact ⟨hScard, hRS, E, hE, hEout, rfl⟩

/-- Exact sum bound for the local branch. -/
theorem card_absorberInducedLocalExtensions_le_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (B R L : TripleSystemOn V) :
    (absorberInducedLocalExtensions q j B R L).card ≤
      ∑ r ∈ Icc 5 q, ∑ K ∈ L.powerset,
        (exactBankOutsideExtensions r j B R K).card := by
  calc
    (absorberInducedLocalExtensions q j B R L).card ≤
        (localExactBankExtensionUnion q j B R L).card :=
      card_le_card
        (absorberInducedLocalExtensions_subset_exact_union q j B R L)
    _ ≤ ∑ r ∈ Icc 5 q,
        (L.powerset.biUnion fun K ↦
          exactBankOutsideExtensions r j B R K).card := card_biUnion_le
    _ ≤ ∑ r ∈ Icc 5 q, ∑ K ∈ L.powerset,
        (exactBankOutsideExtensions r j B R K).card := by
      apply sum_le_sum
      intro r _hr
      exact card_biUnion_le

/-- A2 splits every rooted indexed family into the explicit exact-bank sum
and the nonlocal support branch. -/
theorem exists_local_bank_card_absorberInducedExtensions_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M j : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B R : TripleSystemOn V}
    (hA2 : HasAbsorberLocalization q M H X B)
    (hRq : R.card ≤ q) :
    ∃ L : TripleSystemOn V, L ⊆ B ∧ L.card ≤ M ∧
      (absorberInducedExtensions q j B R).card ≤
        (∑ r ∈ Icc 5 q, ∑ K ∈ L.powerset,
          (exactBankOutsideExtensions r j B R K).card) +
        (absorberInducedSupportExtensions q j H X B R).card := by
  obtain ⟨L, hLB, hLM, hsplit⟩ :=
    card_absorberInducedExtensions_le_split hA2 hRq
  refine ⟨L, hLB, hLM, hsplit.trans ?_⟩
  exact Nat.add_le_add_right
    (card_absorberInducedLocalExtensions_le_sum q j B R L) _

end Erdos207
