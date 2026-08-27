/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SampledRelevantLinkCover

/-! # Candidate-filtered global reservoirs and the source-correct robust iterator -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

def candidateFilteredLinkBits
    {O V : Type*} [DecidableEq V] (K : O → BipartiteLink V)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop)
    (omega : SimultaneousLinkPair O V K → Bool) (x : SimultaneousLinkPair O V K) : Bool :=
  if r x.1 x.2.1 x.2.2 then omega x else false

theorem candidateFilteredLinkBits_true_iff
    {O V : Type*} [DecidableEq V] (K : O → BipartiteLink V)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop)
    (omega : SimultaneousLinkPair O V K → Bool) (x : SimultaneousLinkPair O V K) :
    candidateFilteredLinkBits K r omega x = true ↔ r x.1 x.2.1 x.2.2 ∧ omega x = true := by
  unfold candidateFilteredLinkBits
  split_ifs <;> simp_all

theorem simultaneousLinkSelectedPairs_candidateFiltered
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (K : O → BipartiteLink V)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop) [∀ o, DecidableRel (r o)]
    (omega : SimultaneousLinkPair O V K → Bool) (o : O) :
    simultaneousLinkSelectedPairs K (candidateFilteredLinkBits K r omega) o =
      sampledCandidatePairs (r o) (simultaneousLinkSelectedPairs K omega o) := by
  ext ab
  simp only [mem_simultaneousLinkSelectedPairs_iff, candidateFilteredLinkBits_true_iff,
    sampledCandidatePairs, mem_filter]
  tauto

theorem simultaneousLinkReservoir_candidateFiltered_subset
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o) (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U) (hright : ∀ o, (K o).right ⊆ U)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop)
    (omega : SimultaneousLinkPair O V K → Bool) :
    simultaneousLinkReservoir U center K hcenter hout hleft hright (candidateFilteredLinkBits K r omega) ⊆
      simultaneousLinkReservoir U center K hcenter hout hleft hright omega := by
  apply map_subset_map.mpr
  intro x hx
  apply FiniteLaw.mem_selectedByBits_iff.mpr
  exact ((candidateFilteredLinkBits_true_iff K r omega x).mp (FiniteLaw.mem_selectedByBits_iff.mp hx)).2

theorem simultaneousLinkReservoir_candidateFiltered_subset_available
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o) (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U) (hright : ∀ o, (K o).right ⊆ U)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop)
    (available : TripleSystemOn V)
    (havailable : ∀ o a b, r o a b → simultaneousLinkPairTriple K ⟨o, (a, b)⟩ ∈ available)
    (omega : SimultaneousLinkPair O V K → Bool) :
    simultaneousLinkReservoir U center K hcenter hout hleft hright (candidateFilteredLinkBits K r omega) ⊆ available := by
  intro T hT
  obtain ⟨x, hx, rfl⟩ := mem_map.mp hT
  exact havailable x.1 x.2.1 x.2.2
    (((candidateFilteredLinkBits_true_iff K r omega x).mp (FiniteLaw.mem_selectedByBits_iff.mp hx)).1)

theorem simultaneousLinkReservoir_candidateFiltered_probability_subset_le
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o) (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U) (hright : ∀ o, (K o).right ⊆ U)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1) (Q : TripleSystemOn V) :
    (FiniteLaw.independentBits (fun _ : SimultaneousLinkPair O V K ↦ sigma) (fun _ ↦ hsigma)).probability
      (fun omega ↦ Q ⊆ simultaneousLinkReservoir U center K hcenter hout hleft hright
        (candidateFilteredLinkBits K r omega)) ≤ sigma ^ Q.card := by
  apply le_trans _ (simultaneousLinkReservoir_probability_subset_le U center K hcenter hout hleft hright sigma hsigma Q)
  apply FiniteLaw.probability_mono
  intro omega hQ
  exact hQ.trans (simultaneousLinkReservoir_candidateFiltered_subset U center K hcenter hout hleft hright r omega)

theorem exists_simultaneousLinkCover_of_sampled_candidate_degrees
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o) (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U) (hright : ∀ o, (K o).right ⊆ U)
    (F : ForbiddenFamilyOn V) (available P : TripleSystemOn V)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop) [∀ o, DecidableRel (r o)]
    (Delta : ℕ) (omega : SimultaneousLinkPair O V K → Bool)
    (hrobust : ∀ o, IsTwoSidedRobustMatchingSample (r o) Delta (simultaneousLinkSelectedPairs K omega o))
    (hPpacking : IsPackingOn P) (hPavoid : AvoidsForbidden P F)
    (havailable : ∀ o a b, r o a b → simultaneousLinkPairTriple K ⟨o, (a, b)⟩ ∈ available)
    (hbad : ∀ (S : Finset O) (P' : TripleSystemOn V), P ⊆ P' →
      P' ⊆ P ∪ (available ∩ simultaneousLinkReservoir U center K hcenter hout hleft hright
        (candidateFilteredLinkBits K r omega)) →
      IsPackingOn P' → AvoidsForbidden P' F → IsProcessedSimultaneousLinkFamily K S (P' \ P) →
      ∀ o, o ∉ S →
        (∀ a, (deletedNeighbors (bipartiteLinkRelevantBadPair
          (fun a b ↦ (a, b) ∈ sampledCandidatePairs (r o) (simultaneousLinkSelectedPairs K omega o)) F P'
          (sampledCandidatePairs (r o) (simultaneousLinkSelectedPairs K omega o))) a).card ≤ Delta) ∧
        (∀ b, (deletedNeighbors (transposeRelation (bipartiteLinkRelevantBadPair
          (fun a b ↦ (a, b) ∈ sampledCandidatePairs (r o) (simultaneousLinkSelectedPairs K omega o)) F P'
          (sampledCandidatePairs (r o) (simultaneousLinkSelectedPairs K omega o)))) b).card ≤ Delta)) :
    ∃ M : TripleSystemOn V,
      M ⊆ simultaneousLinkReservoir U center K hcenter hout hleft hright (candidateFilteredLinkBits K r omega) ∧
        IsSimultaneousLinkCover F available P K M := by
  apply exists_simultaneousLinkCover_of_robust_samples U center K hcenter hout hleft hright F available P
    (fun o a b ↦ (a, b) ∈ sampledCandidatePairs (r o) (simultaneousLinkSelectedPairs K omega o))
    Delta (candidateFilteredLinkBits K r omega)
  · intro o
    rw [simultaneousLinkSelectedPairs_candidateFiltered]
    exact (hrobust o).sampled_candidates
  · exact hPpacking
  · exact hPavoid
  · intro o a b hab
    exact havailable o a b (mem_filter.mp hab).2
  · intro S P' hPP' hsub hpck hav hprocessed o ho
    simpa only [simultaneousLinkSelectedPairs_candidateFiltered] using hbad S P' hPP' hsub hpck hav hprocessed o ho

end

end Erdos207
