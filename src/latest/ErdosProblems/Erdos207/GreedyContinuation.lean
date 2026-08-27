/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberGreedy
import ErdosProblems.Erdos207.StoppedGreedyJointInclusion

/-!
# Exhausting the constrained greedy process from an intermediate state

The first random phase ends at a nonempty legal availability family.  This
file records that the ordinary finite greedy kernel can always be continued
to a maximal legal extension while preserving the full invariant and every
previously selected triangle.
-/

namespace Erdos207

open Finset

noncomputable section

/-- Every trajectory of the continuation law contains the initial chosen
packing. -/
theorem iterateGreedyKernel_supported_chosen_superset
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (fuel : ℕ) (S : GreedyStateOn V) :
    (FiniteLaw.iterateKernel (greedyKernel F) fuel
      (FiniteLaw.pure S)).SupportedOn
        (fun S' ↦ S.chosen ⊆ S'.chosen) := by
  apply (FiniteLaw.supportedOn_pure
    (fun S' : GreedyStateOn V ↦ S.chosen ⊆ S'.chosen)
      Subset.rfl).iterateKernel
  intro S' hSS'
  intro S'' hmass
  exact hSS'.trans
    ((greedyKernel_monotone_singleInsertion F S') S'' hmass).1

/-- In `fuel` single-insertion steps, at most `fuel` triangles can be added
to the initial chosen family. -/
theorem iterateGreedyKernel_supported_newChosen_card_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (fuel : ℕ) (S : GreedyStateOn V) :
    (FiniteLaw.iterateKernel (greedyKernel F) fuel
      (FiniteLaw.pure S)).SupportedOn
        (fun S' ↦ S.chosen ⊆ S'.chosen ∧
          (S'.chosen \ S.chosen).card ≤ fuel) := by
  induction fuel with
  | zero =>
      exact FiniteLaw.supportedOn_pure _ ⟨Subset.rfl, by simp⟩
  | succ fuel ih =>
      rw [FiniteLaw.iterateKernel_succ_right]
      refine ih.bind (Q := fun S' ↦ S.chosen ⊆ S'.chosen ∧
        (S'.chosen \ S.chosen).card ≤ fuel + 1) (greedyKernel F) ?_
      intro S' hS'
      intro S'' hmass
      have hstep := (greedyKernel_monotone_singleInsertion F S') S'' hmass
      refine ⟨hS'.1.trans hstep.1, ?_⟩
      have hdiff : S''.chosen \ S.chosen ⊆
          (S'.chosen \ S.chosen) ∪ (S''.chosen \ S'.chosen) := by
        intro T hT
        have hT' := mem_sdiff.mp hT
        by_cases hTS' : T ∈ S'.chosen
        · exact mem_union_left _ (mem_sdiff.mpr ⟨hTS', hT'.2⟩)
        · exact mem_union_right _ (mem_sdiff.mpr ⟨hT'.1, hTS'⟩)
      calc
        (S''.chosen \ S.chosen).card ≤
            ((S'.chosen \ S.chosen) ∪
              (S''.chosen \ S'.chosen)).card := card_le_card hdiff
        _ ≤ (S'.chosen \ S.chosen).card +
            (S''.chosen \ S'.chosen).card := card_union_le _ _
        _ ≤ fuel + 1 := Nat.add_le_add hS'.2 hstep.2

/-- Consequently a continuation can enlarge any fixed selected vertex star
by at most its fuel. -/
theorem iterateGreedyKernel_supported_triplesThrough_card_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (fuel : ℕ) (S : GreedyStateOn V) (v : V) :
    (FiniteLaw.iterateKernel (greedyKernel F) fuel
      (FiniteLaw.pure S)).SupportedOn
        (fun S' ↦ (triplesThrough S'.chosen v).card ≤
          (triplesThrough S.chosen v).card + fuel) := by
  intro S' hmass
  have hnew := iterateGreedyKernel_supported_newChosen_card_le
    F fuel S S' hmass
  have hsubset : triplesThrough S'.chosen v ⊆
      triplesThrough S.chosen v ∪ (S'.chosen \ S.chosen) := by
    intro T hT
    have hT' := mem_filter.mp hT
    by_cases hTS : T ∈ S.chosen
    · exact mem_union_left _ (mem_filter.mpr ⟨hTS, hT'.2⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hT'.1, hTS⟩)
  calc
    (triplesThrough S'.chosen v).card ≤
        (triplesThrough S.chosen v ∪
          (S'.chosen \ S.chosen)).card := card_le_card hsubset
    _ ≤ (triplesThrough S.chosen v).card +
        (S'.chosen \ S.chosen).card := card_union_le _ _
    _ ≤ (triplesThrough S.chosen v).card + fuel := by omega

/-- Starting from an absorber-greedy invariant state and running for the
current availability cardinality yields only invariant, exhausted extensions
of that state. -/
theorem absorberGreedyContinuationLaw_supported
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A : TripleSystemOn V}
    (S : GreedyStateOn V) (hS : AbsorberGreedyInvariant F A S) :
    (FiniteLaw.iterateKernel (greedyKernel F) S.available.card
      (FiniteLaw.pure S)).SupportedOn
        (fun S' ↦ AbsorberGreedyInvariant F A S' ∧
          S.chosen ⊆ S'.chosen ∧ S'.available = ∅) := by
  let L := FiniteLaw.iterateKernel (greedyKernel F) S.available.card
    (FiniteLaw.pure S)
  have hInv : L.SupportedOn (AbsorberGreedyInvariant F A) := by
    apply (FiniteLaw.supportedOn_pure
      (AbsorberGreedyInvariant F A) hS).iterateKernel
    intro S' hS'
    exact absorberGreedyKernel_supported hS'
  have hsubset : L.SupportedOn (fun S' ↦ S.chosen ⊆ S'.chosen) := by
    exact iterateGreedyKernel_supported_chosen_superset
      F S.available.card S
  have hexhausted : L.SupportedOn (fun S' ↦ S'.available = ∅) := by
    apply iterateGreedyKernel_exhausts F S.available.card
      (FiniteLaw.pure S)
    exact FiniteLaw.supportedOn_pure _ (le_refl S.available.card)
  intro S' hmass
  exact ⟨hInv S' hmass, hsubset S' hmass, hexhausted S' hmass⟩

/-- Deterministic extraction of a maximal legal packing extending an
arbitrary intermediate absorber-greedy state. -/
theorem exists_maximal_absorberGreedyExtension
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A : TripleSystemOn V}
    (S : GreedyStateOn V) (hS : AbsorberGreedyInvariant F A S) :
    ∃ P : TripleSystemOn V,
      S.chosen ⊆ P ∧ IsPackingOn P ∧ AvoidsForbidden P F ∧ P ⊆ A ∧
        legalAvailable F P A = ∅ := by
  let L := FiniteLaw.iterateKernel (greedyKernel F) S.available.card
    (FiniteLaw.pure S)
  have hex : ∃ S', 0 < L.mass S' := by
    by_contra hnone
    push Not at hnone
    have hallzero : ∀ S', L.mass S' = 0 := by
      intro S'
      exact nonpos_iff_eq_zero.mp (hnone S')
    have hsum := L.sum_mass
    simp_rw [hallzero] at hsum
    norm_num at hsum
  obtain ⟨S', hmass⟩ := hex
  have hS' := absorberGreedyContinuationLaw_supported S hS S' hmass
  refine ⟨S'.chosen, hS'.2.1, hS'.1.1.1, hS'.1.1.2.1,
    hS'.1.2.1.1, ?_⟩
  rw [← hS'.1.2.2]
  exact hS'.2.2

end

end Erdos207
