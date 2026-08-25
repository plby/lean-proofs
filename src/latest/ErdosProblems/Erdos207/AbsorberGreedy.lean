/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberForbidden

/-!
# Constrained greedy process relative to an absorber bank

This specializes the finite greedy kernel to triangles outside the absorber
bank and records the extra containment invariant needed at completion.
-/

namespace Erdos207

open Finset

/-- The chosen and currently available triangles both remain in the original
ambient availability family. -/
def GreedyContainedIn {V : Type*} [DecidableEq V]
    (A : TripleSystemOn V) (S : GreedyStateOn V) : Prop :=
  S.chosen ⊆ A ∧ S.available ⊆ A

lemma legalAvailable_subset_right
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (C A : TripleSystemOn V) :
    legalAvailable F C A ⊆ A := by
  intro T hT
  exact (mem_legalAvailable_iff.mp hT).1

lemma AvoidsForbidden.mono
    {V : Type*} [DecidableEq V]
    {C D : TripleSystemOn V} {F : ForbiddenFamilyOn V}
    (hD : AvoidsForbidden D F) (hCD : C ⊆ D) : AvoidsForbidden C F := by
  intro E hEF hEC
  exact hD E hEF (hEC.trans hCD)

/-- Legality is antitone in the chosen family: a triangle legal after more
choices was already legal before them. -/
lemma IsLegalExtension.antitone_chosen
    {V : Type*} [DecidableEq V]
    {F : ForbiddenFamilyOn V} {C D : TripleSystemOn V} {T : TripleOn V}
    (hCD : C ⊆ D) (hT : IsLegalExtension F D T) :
    IsLegalExtension F C T := by
  refine ⟨fun hTC ↦ hT.1 (hCD hTC), ?_, ?_⟩
  · apply hT.2.1.mono
    intro U hU
    rw [mem_insert] at hU ⊢
    rcases hU with rfl | hUC
    · exact Or.inl rfl
    · exact Or.inr (hCD hUC)
  · apply hT.2.2.mono
    intro U hU
    rw [mem_insert] at hU ⊢
    rcases hU with rfl | hUC
    · exact Or.inl rfl
    · exact Or.inr (hCD hUC)

/-- The state's availability is exactly the set of ambient triangles still
legal over its chosen family. -/
def GreedyExactAvailable {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (A : TripleSystemOn V)
    (S : GreedyStateOn V) : Prop :=
  S.available = legalAvailable F S.chosen A

lemma GreedyExactAvailable.step
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A : TripleSystemOn V}
    {S : GreedyStateOn V} {T : TripleOn V}
    (hS : GreedyExactAvailable F A S) (hT : T ∈ S.available) :
    GreedyExactAvailable F A (greedyStep F S T) := by
  ext U
  simp only [greedyStep, mem_legalAvailable_iff, mem_erase]
  constructor
  · rintro ⟨⟨hUneT, hUold⟩, hUlegal⟩
    exact ⟨(mem_legalAvailable_iff.mp (hS ▸ hUold)).1, hUlegal⟩
  · rintro ⟨hUA, hUlegal⟩
    have hUneT : U ≠ T := by
      intro hUT
      subst U
      exact hUlegal.1 (mem_insert_self T S.chosen)
    have hUoldLegal := hUlegal.antitone_chosen (subset_insert T S.chosen)
    have hUold : U ∈ S.available := by
      rw [hS, mem_legalAvailable_iff]
      exact ⟨hUA, hUoldLegal⟩
    exact ⟨⟨hUneT, hUold⟩, hUlegal⟩

lemma GreedyContainedIn.step
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A : TripleSystemOn V}
    {S : GreedyStateOn V} {T : TripleOn V}
    (hS : GreedyContainedIn A S) (hT : T ∈ S.available) :
    GreedyContainedIn A (greedyStep F S T) := by
  constructor
  · intro U hU
    rw [greedyStep, mem_insert] at hU
    rcases hU with rfl | hUS
    · exact hS.2 hT
    · exact hS.1 hUS
  · exact (legalAvailable_subset_right F _ _).trans fun U hU ↦
      hS.2 (mem_erase.mp hU).2

/-- The ordinary legal-process invariant together with ambient containment. -/
def AbsorberGreedyInvariant {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (A : TripleSystemOn V)
    (S : GreedyStateOn V) : Prop :=
  GreedyInvariant F S ∧ GreedyContainedIn A S ∧
    GreedyExactAvailable F A S

lemma AbsorberGreedyInvariant.step
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A : TripleSystemOn V}
    {S : GreedyStateOn V} {T : TripleOn V}
    (hS : AbsorberGreedyInvariant F A S) (hT : T ∈ S.available) :
    AbsorberGreedyInvariant F A (greedyStep F S T) :=
  ⟨hS.1.step hT, hS.2.1.step hT, hS.2.2.step hT⟩

theorem absorberGreedyKernel_supported
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A : TripleSystemOn V}
    {S : GreedyStateOn V}
    (hS : AbsorberGreedyInvariant F A S) :
    FiniteLaw.SupportedOn (AbsorberGreedyInvariant F A)
      (greedyKernel F S) := by
  classical
  unfold greedyKernel
  split_ifs with hnonempty
  · let hne : Nonempty S.available :=
      ⟨⟨hnonempty.choose, hnonempty.choose_spec⟩⟩
    let next : S.available → GreedyStateOn V :=
      fun T ↦ greedyStep F S T.1
    have hu : FiniteLaw.SupportedOn (fun _ : S.available ↦ True)
        (@FiniteLaw.uniform S.available _ hne) :=
      FiniteLaw.uniform_supported _ fun _ ↦ trivial
    exact hu.map next fun T _ ↦ hS.step T.2
  · exact FiniteLaw.supportedOn_pure _ hS

theorem absorberGreedyProcessLaw_supported
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A : TripleSystemOn V}
    {fuel : ℕ} {S : GreedyStateOn V}
    (hS : AbsorberGreedyInvariant F A S) :
    FiniteLaw.SupportedOn (AbsorberGreedyInvariant F A)
      (greedyProcessLaw F fuel S) := by
  classical
  apply FiniteLaw.SupportedOn.iterateKernel
    (FiniteLaw.supportedOn_pure _ hS) (greedyKernel F)
  intro S' hS'
  exact absorberGreedyKernel_supported hS'

/-- Initialize with every ambient triangle that is legal over the empty
packing. -/
noncomputable def absorberGreedyInitialState
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (A : TripleSystemOn V) : GreedyStateOn V where
  chosen := ∅
  available := legalAvailable F ∅ A

lemma absorberGreedyInitialState_invariant
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (A : TripleSystemOn V)
    (hnonempty : ∀ S ∈ F, S.Nonempty) :
    AbsorberGreedyInvariant F A (absorberGreedyInitialState F A) := by
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro u v huv T hT
      have hnot : T ∉ (∅ : TripleSystemOn V) := by simp
      exact (hnot hT).elim
    · intro C hCF hCempty
      obtain ⟨T, hTC⟩ := hnonempty C hCF
      have hnot : T ∉ (∅ : TripleSystemOn V) := by simp
      exact hnot (hCempty hTC)
    · intro T hT
      exact (mem_legalAvailable_iff.mp hT).2
  · exact ⟨⟨empty_subset _, legalAvailable_subset_right F ∅ A⟩, rfl⟩

lemma absorberErdosForbidden_nonempty
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B S : TripleSystemOn V}
    (hS : S ∈ absorberErdosForbiddenConfigurationsOn q B) : S.Nonempty :=
  (mem_absorberErdosForbiddenConfigurationsOn_iff.mp hS).1

/-- The canonical finite law used for the initial constrained process. -/
noncomputable def absorberGreedyLaw
    {V : Type*} [Fintype V] [DecidableEq V]
    (q fuel : ℕ) (B A : TripleSystemOn V) : FiniteLaw (GreedyStateOn V) :=
  greedyProcessLaw (absorberErdosForbiddenConfigurationsOn q B) fuel
    (absorberGreedyInitialState
      (absorberErdosForbiddenConfigurationsOn q B) A)

theorem absorberGreedyLaw_supported
    {V : Type*} [Fintype V] [DecidableEq V]
    (q fuel : ℕ) (B A : TripleSystemOn V) :
    FiniteLaw.SupportedOn
      (AbsorberGreedyInvariant
        (absorberErdosForbiddenConfigurationsOn q B) A)
      (absorberGreedyLaw q fuel B A) := by
  apply absorberGreedyProcessLaw_supported
  exact absorberGreedyInitialState_invariant _ _ fun S hS ↦
    absorberErdosForbidden_nonempty hS

lemma greedyStep_available_card_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {T : TripleOn V}
    (hT : T ∈ S.available) :
    (greedyStep F S T).available.card < S.available.card := by
  calc
    (greedyStep F S T).available.card ≤ (S.available.erase T).card :=
      card_le_card (legalAvailable_subset_right F _ _)
    _ < S.available.card := card_erase_lt_of_mem hT

/-- One uniform greedy transition either stays at an already exhausted state
or strictly decreases the availability cardinality. -/
theorem greedyKernel_decreases
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) :
    FiniteLaw.SupportedOn
      (fun S' ↦ S.available = ∅ ∧ S' = S ∨
        S'.available.card < S.available.card)
      (greedyKernel F S) := by
  classical
  unfold greedyKernel
  split_ifs with hnonempty
  · let hne : Nonempty S.available :=
      ⟨⟨hnonempty.choose, hnonempty.choose_spec⟩⟩
    let next : S.available → GreedyStateOn V :=
      fun T ↦ greedyStep F S T.1
    have hu : FiniteLaw.SupportedOn (fun _ : S.available ↦ True)
        (@FiniteLaw.uniform S.available _ hne) :=
      FiniteLaw.uniform_supported _ fun _ ↦ trivial
    exact hu.map next fun T _ ↦ Or.inr (greedyStep_available_card_lt T.2)
  · have hempty : S.available = ∅ := not_nonempty_iff_eq_empty.mp hnonempty
    exact FiniteLaw.supportedOn_pure _ (Or.inl ⟨hempty, rfl⟩)

/-- Any law supported on states with at most `fuel` available triangles is
exhausted after `fuel` further uniform greedy transitions. -/
theorem iterateGreedyKernel_exhausts
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (fuel : ℕ) (L : FiniteLaw (GreedyStateOn V))
    (hL : FiniteLaw.SupportedOn
      (fun S ↦ S.available.card ≤ fuel) L) :
    FiniteLaw.SupportedOn (fun S ↦ S.available = ∅)
      (FiniteLaw.iterateKernel (greedyKernel F) fuel L) := by
  induction fuel generalizing L with
  | zero =>
      intro S hmass
      exact card_eq_zero.mp (Nat.le_zero.mp (hL S hmass))
  | succ fuel ih =>
      apply ih (FiniteLaw.bind L (greedyKernel F))
      refine FiniteLaw.SupportedOn.bind hL (greedyKernel F) ?_
      intro S hScard
      have hstep := greedyKernel_decreases F S
      intro S' hmass
      rcases hstep S' hmass with ⟨hempty, rfl⟩ | hlt
      · simp [hempty]
      · omega

/-- Running for the size of the original ambient family reaches a maximal
legal packing with probability one. -/
theorem absorberGreedyLaw_exhausted
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (B A : TripleSystemOn V) :
    FiniteLaw.SupportedOn
      (fun S ↦ AbsorberGreedyInvariant
          (absorberErdosForbiddenConfigurationsOn q B) A S ∧
        S.available = ∅)
      (absorberGreedyLaw q A.card B A) := by
  intro S hmass
  constructor
  · exact absorberGreedyLaw_supported q A.card B A S hmass
  · apply iterateGreedyKernel_exhausts
      (absorberErdosForbiddenConfigurationsOn q B) A.card
      (FiniteLaw.pure (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B) A))
    · apply FiniteLaw.supportedOn_pure
      have hsub := legalAvailable_subset_right
        (absorberErdosForbiddenConfigurationsOn q B) ∅ A
      exact card_le_card hsub
    · exact hmass

/-- Deterministic extraction of a maximal absorber-compatible packing from
the exhausted finite law. -/
theorem exists_maximal_absorberGreedyPacking
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (B A : TripleSystemOn V) :
    ∃ P : TripleSystemOn V,
      IsPackingOn P ∧
      AvoidsForbidden P (absorberErdosForbiddenConfigurationsOn q B) ∧
      P ⊆ A ∧ legalAvailable
        (absorberErdosForbiddenConfigurationsOn q B) P A = ∅ := by
  let L := absorberGreedyLaw q A.card B A
  have hex : ∃ S, 0 < L.mass S := by
    by_contra hnone
    push Not at hnone
    have hallzero : ∀ S, L.mass S = 0 := by
      intro S
      exact nonpos_iff_eq_zero.mp (hnone S)
    have hsum := L.sum_mass
    simp_rw [hallzero] at hsum
    norm_num at hsum
  obtain ⟨S, hmass⟩ := hex
  have hS := absorberGreedyLaw_exhausted q B A S hmass
  refine ⟨S.chosen, hS.1.1.1, hS.1.1.2.1, hS.1.2.1.1, ?_⟩
  rw [← hS.1.2.2]
  exact hS.2

end Erdos207
