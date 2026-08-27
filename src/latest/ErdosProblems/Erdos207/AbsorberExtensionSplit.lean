/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberWellSpread

/-!
# Uniform local/nonlocal split for absorber-induced extensions

This turns the logical A2 dichotomy into a literal partition suitable for
cardinality and weight estimates.
-/

namespace Erdos207

open Finset

/-- Indexed absorber-induced outside parts extending a prescribed root. -/
noncomputable def absorberInducedExtensions
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (B R : TripleSystemOn V) : ForbiddenFamilyOn V := by
  classical
  exact (absorberInducedConfigurationsOn q j B).filter fun S ↦ R ⊆ S

@[simp]
lemma mem_absorberInducedExtensions_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {q j : ℕ} {B R S : TripleSystemOn V} :
    S ∈ absorberInducedExtensions q j B R ↔
      S ∈ absorberInducedConfigurationsOn q j B ∧ R ⊆ S := by
  classical
  simp [absorberInducedExtensions]

/-- Extensions all of whose bank completions lie in the fixed local bank. -/
noncomputable def absorberInducedLocalExtensions
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (B R L : TripleSystemOn V) : ForbiddenFamilyOn V := by
  classical
  exact (absorberInducedExtensions q j B R).filter fun S ↦
    ∀ r E, 5 ≤ r → r ≤ q → IsErdosConfigOn r E →
      E \ B = S → E ∩ B ⊆ L

@[simp]
lemma mem_absorberInducedLocalExtensions_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {q j : ℕ} {B R L S : TripleSystemOn V} :
    S ∈ absorberInducedLocalExtensions q j B R L ↔
      S ∈ absorberInducedConfigurationsOn q j B ∧ R ⊆ S ∧
        ∀ r E, 5 ≤ r → r ≤ q → IsErdosConfigOn r E →
          E \ B = S → E ∩ B ⊆ L := by
  classical
  simp only [absorberInducedLocalExtensions, mem_filter,
    mem_absorberInducedExtensions_iff]
  tauto

/-- Nonlocal extensions carrying an additional outside triangle through a
non-flexible absorber vertex. -/
noncomputable def absorberInducedSupportExtensions
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (H : SimpleGraph V) (X : Finset V)
    (B R : TripleSystemOn V) : ForbiddenFamilyOn V := by
  classical
  exact (absorberInducedExtensions q j B R).filter fun S ↦
    ∃ r E T v, 5 ≤ r ∧ r ≤ q ∧ IsErdosConfigOn r E ∧
      E \ B = S ∧ T ∈ S ∧ T ∉ R ∧ v ∈ T.1 ∧
      v ∈ graphSupportFinset H ∧ v ∉ X

@[simp]
lemma mem_absorberInducedSupportExtensions_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {q j : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B R S : TripleSystemOn V} :
    S ∈ absorberInducedSupportExtensions q j H X B R ↔
      S ∈ absorberInducedConfigurationsOn q j B ∧ R ⊆ S ∧
        ∃ r E T v, 5 ≤ r ∧ r ≤ q ∧ IsErdosConfigOn r E ∧
          E \ B = S ∧ T ∈ S ∧ T ∉ R ∧ v ∈ T.1 ∧
          v ∈ graphSupportFinset H ∧ v ∉ X := by
  classical
  unfold absorberInducedSupportExtensions
  rw [mem_filter, mem_absorberInducedExtensions_iff]
  constructor
  · rintro ⟨⟨hS, hR⟩, hex⟩
    exact ⟨hS, hR, hex⟩
  · rintro ⟨hS, hR, hex⟩
    exact ⟨⟨hS, hR⟩, hex⟩

/-- A2 supplies one bounded local bank for which every rooted indexed
extension lies in the local or support branch. -/
theorem exists_local_bank_extension_split
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M j : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B R : TripleSystemOn V}
    (hA2 : HasAbsorberLocalization q M H X B)
    (hRq : R.card ≤ q) :
    ∃ L : TripleSystemOn V, L ⊆ B ∧ L.card ≤ M ∧
      absorberInducedExtensions q j B R ⊆
        absorberInducedLocalExtensions q j B R L ∪
          absorberInducedSupportExtensions q j H X B R := by
  obtain ⟨L, hLB, hLM, hsplit⟩ :=
    absorberInduced_extensions_local_or_meets_support hA2 hRq
  refine ⟨L, hLB, hLM, ?_⟩
  intro S hS
  obtain ⟨hSinduced, hRS⟩ :=
    mem_absorberInducedExtensions_iff.mp hS
  rcases hsplit S hSinduced hRS with hlocal | hsupport
  · exact mem_union.mpr (Or.inl
      (mem_absorberInducedLocalExtensions_iff.mpr
        ⟨hSinduced, hRS, hlocal⟩))
  · exact mem_union.mpr (Or.inr
      (mem_absorberInducedSupportExtensions_iff.mpr
        ⟨hSinduced, hRS, hsupport⟩))

/-- Cardinal form of the uniform extension split. -/
theorem card_absorberInducedExtensions_le_split
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M j : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B R : TripleSystemOn V}
    (hA2 : HasAbsorberLocalization q M H X B)
    (hRq : R.card ≤ q) :
    ∃ L : TripleSystemOn V, L ⊆ B ∧ L.card ≤ M ∧
      (absorberInducedExtensions q j B R).card ≤
        (absorberInducedLocalExtensions q j B R L).card +
          (absorberInducedSupportExtensions q j H X B R).card := by
  obtain ⟨L, hLB, hLM, hsub⟩ :=
    exists_local_bank_extension_split hA2 hRq
  refine ⟨L, hLB, hLM, ?_⟩
  exact (card_le_card hsub).trans
    (card_union_le
      (absorberInducedLocalExtensions q j B R L)
      (absorberInducedSupportExtensions q j H X B R))

end Erdos207
