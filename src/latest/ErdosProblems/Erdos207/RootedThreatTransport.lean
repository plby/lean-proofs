/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyContinuation
import ErdosProblems.Erdos207.RootedThreatWeight

/-!
# Transporting rooted-threat bounds across a monotone continuation

An active rooted witness after enlarging a chosen family was either already
active before the enlargement, or its remainder contains a newly selected
triangle.  This elementary split gives a deterministic transport bound once
the number of witnesses using any fixed triangle is bounded.
-/

namespace Erdos207

open Finset

noncomputable section

/-- Rooted witnesses whose selected remainder uses a prescribed triangle. -/
noncomputable def rootedThreatWitnessesUsing
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (u v : V) (T : TripleOn V) :
    Finset (RootedThreatWitness V F u v) := by
  classical
  exact univ.filter fun z ↦ T ∈ rootedThreatRemainder z

@[simp]
lemma mem_rootedThreatWitnessesUsing_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {u v : V} {T : TripleOn V}
    {z : RootedThreatWitness V F u v} :
    z ∈ rootedThreatWitnessesUsing F u v T ↔
      T ∈ rootedThreatRemainder z := by
  classical
  simp [rootedThreatWitnessesUsing]

/-- Active rooted witnesses after an enlargement split into old witnesses
and witnesses using one of the newly selected triangles. -/
theorem activeRootedThreatWitnesses_subset_old_union_new
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {P P' : TripleSystemOn V} {u v : V}
    (hPP' : P ⊆ P') :
    activeRootedThreatWitnesses F P' u v ⊆
      activeRootedThreatWitnesses F P u v ∪
        (P' \ P).biUnion (rootedThreatWitnessesUsing F u v) := by
  intro z hz
  have hremP' := mem_activeRootedThreatWitnesses_iff.mp hz
  by_cases hremP : rootedThreatRemainder z ⊆ P
  · exact mem_union_left _ (mem_activeRootedThreatWitnesses_iff.mpr hremP)
  · obtain ⟨T, hTrem, hTnotP⟩ := not_subset.mp hremP
    have hTnew : T ∈ P' \ P := mem_sdiff.mpr ⟨hremP' hTrem, hTnotP⟩
    exact mem_union_right _ (mem_biUnion.mpr
      ⟨T, hTnew, mem_rootedThreatWitnessesUsing_iff.mpr hTrem⟩)

/-- An active witness is encoded by its rooted active configuration and its
designated missing triangle. -/
def activeRootedThreatWitnessEmbedding
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V) (u v : V) :
    {z : RootedThreatWitness V F u v //
      z ∈ activeRootedThreatWitnesses F P u v} ↪
      Σ S : rootedActiveForbiddenConfigurations F P u v, S.1 :=
  { toFun := fun z ↦
      ⟨⟨z.1.1.1, mem_rootedActiveForbiddenConfigurations_iff.mpr
        ⟨z.1.2.1, z.1.1.2, z.1.2.2.1, z.1.2.2.2.1,
          z.1.2.2.2.2, mem_activeRootedThreatWitnesses_iff.mp z.2⟩⟩,
        ⟨z.1.1.2, z.1.2.2.1⟩⟩
    inj' := by
      intro z w hzw
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext (congrArg (fun x ↦ x.1.1) hzw)
        (congrArg (fun x ↦ x.2.1) hzw) }

/-- If forbidden members have size at most `k`, each rooted active
configuration accounts for at most `k` active rooted witnesses. -/
theorem card_activeRootedThreatWitnesses_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V) (u v : V) (k : ℕ)
    (hcard : ∀ S ∈ F, S.card ≤ k) :
    (activeRootedThreatWitnesses F P u v).card ≤
      (rootedActiveForbiddenConfigurations F P u v).card * k := by
  calc
    (activeRootedThreatWitnesses F P u v).card =
        Fintype.card {z : RootedThreatWitness V F u v //
          z ∈ activeRootedThreatWitnesses F P u v} :=
      (Fintype.card_coe _).symm
    _ ≤ Fintype.card
        (Σ S : rootedActiveForbiddenConfigurations F P u v, S.1) :=
      Fintype.card_le_of_embedding
        (activeRootedThreatWitnessEmbedding F P u v)
    _ = ∑ S : rootedActiveForbiddenConfigurations F P u v,
        S.1.card := by simp
    _ ≤ ∑ _S : rootedActiveForbiddenConfigurations F P u v, k := by
      apply sum_le_sum
      intro S _hS
      exact hcard S.1 (mem_rootedActiveForbiddenConfigurations_iff.mp S.2).1
    _ = (rootedActiveForbiddenConfigurations F P u v).card * k := by simp

/-- Cardinal transport across an arbitrary monotone enlargement. -/
theorem card_rootedActiveForbiddenConfigurations_le_of_enlargement
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {P P' : TripleSystemOn V} {u v : V}
    (k K : ℕ) (hcard : ∀ S ∈ F, S.card ≤ k)
    (husing : ∀ T : TripleOn V,
      (rootedThreatWitnessesUsing F u v T).card ≤ K)
    (hPP' : P ⊆ P') :
    (rootedActiveForbiddenConfigurations F P' u v).card ≤
      (rootedActiveForbiddenConfigurations F P u v).card * k +
        (P' \ P).card * K := by
  calc
    (rootedActiveForbiddenConfigurations F P' u v).card ≤
        (activeRootedThreatWitnesses F P' u v).card :=
      card_rootedActiveForbiddenConfigurations_le_witnesses
    _ ≤ (activeRootedThreatWitnesses F P u v ∪
          (P' \ P).biUnion
            (rootedThreatWitnessesUsing F u v)).card :=
      card_le_card (activeRootedThreatWitnesses_subset_old_union_new hPP')
    _ ≤ (activeRootedThreatWitnesses F P u v).card +
          ((P' \ P).biUnion
            (rootedThreatWitnessesUsing F u v)).card := card_union_le _ _
    _ ≤ (activeRootedThreatWitnesses F P u v).card +
          ∑ T ∈ P' \ P,
            (rootedThreatWitnessesUsing F u v T).card := by
      exact Nat.add_le_add_left card_biUnion_le _
    _ ≤ (rootedActiveForbiddenConfigurations F P u v).card * k +
          ∑ _T ∈ P' \ P, K := by
      exact Nat.add_le_add
        (card_activeRootedThreatWitnesses_le F P u v k hcard)
        (sum_le_sum fun T _hT ↦ husing T)
    _ = (rootedActiveForbiddenConfigurations F P u v).card * k +
          (P' \ P).card * K := by simp

/-- Supported continuation version: after `fuel` greedy steps, the rooted
active count is at most the old count times `k`, plus `fuel * K`. -/
theorem iterateGreedyKernel_supported_rootedActive_card_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (fuel : ℕ) (S : GreedyStateOn V)
    (u v : V) (k K : ℕ) (hcard : ∀ C ∈ F, C.card ≤ k)
    (husing : ∀ T : TripleOn V,
      (rootedThreatWitnessesUsing F u v T).card ≤ K) :
    (FiniteLaw.iterateKernel (greedyKernel F) fuel
      (FiniteLaw.pure S)).SupportedOn
        (fun S' ↦
          (rootedActiveForbiddenConfigurations F S'.chosen u v).card ≤
            (rootedActiveForbiddenConfigurations F S.chosen u v).card * k +
              fuel * K) := by
  intro S' hmass
  have hnew := iterateGreedyKernel_supported_newChosen_card_le
    F fuel S S' hmass
  exact (card_rootedActiveForbiddenConfigurations_le_of_enlargement
    k K hcard husing hnew.1).trans (by
      exact Nat.add_le_add_left (Nat.mul_le_mul_right K hnew.2) _)

end

end Erdos207
