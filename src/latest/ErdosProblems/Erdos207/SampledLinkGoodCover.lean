/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SampledLinkCollisionControl
import ErdosProblems.Erdos207.SampledLinkForbiddenDegree
import ErdosProblems.Erdos207.SimultaneousLinkCoverLaw

/-! # Fixed sampled collision and forbidden counts discharge every sweep state -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

def IsSampledLinkCollisionGood
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (K : O → BipartiteLink V)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop) [∀ o, DecidableRel (r o)]
    (cap : ℕ) (omega : SimultaneousLinkPair O V K → Bool) : Prop :=
  ∀ o, (∀ a : ↥(K o).left,
    (sampledLinkCollisions K r (fun b ↦ ⟨o,(a,b)⟩) (univ.filter (r o a)) omega).card ≤ cap) ∧
    (∀ b : ↥(K o).right,
      (sampledLinkCollisions K r (fun a ↦ ⟨o,(a,b)⟩) (univ.filter (fun a ↦ r o a b)) omega).card ≤ cap)

def IsSampledLinkForbiddenGood
    {O V : Type*} [DecidableEq V]
    (K : O → BipartiteLink V) (F : ForbiddenFamilyOn V)
    (I D Q : TripleSystemOn V) (cap : ℕ) : Prop :=
  ∀ o, (∀ a : ↥(K o).left,
    (sourceLinkForbiddenSamples F I D Q s((K o).center,(K o).leftEmbedding a)).card ≤ cap) ∧
    (∀ b : ↥(K o).right,
      (sourceLinkForbiddenSamples F I D Q s((K o).center,(K o).rightEmbedding b)).card ≤ cap)

theorem exists_simultaneousLinkCover_of_sampled_counts
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o) (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U) (hright : ∀ o, (K o).right ⊆ U)
    (F : ForbiddenFamilyOn V) (available I D : TripleSystemOn V)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop) [∀ o, DecidableRel (r o)]
    (Delta collisionCap forbiddenCap : ℕ) (omega : SimultaneousLinkPair O V K → Bool)
    (hrobust : ∀ o, IsTwoSidedRobustMatchingSample (r o) Delta (simultaneousLinkSelectedPairs K omega o))
    (hpacking : IsPackingOn (I ∪ D)) (havoid : AvoidsForbidden (I ∪ D) F)
    (havailable : ∀ o a b, r o a b → simultaneousLinkPairTriple K ⟨o,(a,b)⟩ ∈ available)
    (hsafe : ∀ o a b, r o a b → TriangleAvoidsGraph (coveredGraph (I ∪ D))
      (simultaneousLinkPairTriple K ⟨o,(a,b)⟩))
    (hcollision : IsSampledLinkCollisionGood K r collisionCap omega)
    (hforbidden : IsSampledLinkForbiddenGood K F I D
      (simultaneousLinkReservoir U center K hcenter hout hleft hright (candidateFilteredLinkBits K r omega)) forbiddenCap)
    (hcap : collisionCap + forbiddenCap ≤ Delta) :
    ∃ M : TripleSystemOn V,
      M ⊆ simultaneousLinkReservoir U center K hcenter hout hleft hright (candidateFilteredLinkBits K r omega) ∧
        IsSimultaneousLinkCover F available (I ∪ D) K M := by
  let Q := simultaneousLinkReservoir U center K hcenter hout hleft hright (candidateFilteredLinkBits K r omega)
  apply exists_simultaneousLinkCover_of_sampled_candidate_degrees U center K hcenter hout hleft hright
    F available (I ∪ D) r Delta omega hrobust hpacking havoid havailable
  intro S P' _hbase hsub _hpacking _havoid hprocessed o ho
  have hPsub : P' ⊆ (I ∪ D) ∪ Q := hsub.trans (union_subset subset_union_left
    (inter_subset_right.trans subset_union_right))
  let R := sampledCandidatePairs (r o) (simultaneousLinkSelectedPairs K omega o)
  have hR : bipartiteLinkReservoir (K o) R ⊆ Q := by
    rw [show R = simultaneousLinkSelectedPairs K (candidateFilteredLinkBits K r omega) o by
      exact (simultaneousLinkSelectedPairs_candidateFiltered K r omega o).symm]
    exact bipartiteLinkReservoir_simultaneous_subset U center K hcenter hout hleft hright _ o
  constructor
  · intro a
    have hb := sampledLinkBadPair_left_card_le F I D P' Q (K o) R hPsub hR a
    have hc := card_le_card (sampled_pair_conflict_left_subset_collisions U center K hcenter hout hleft hright
      r omega (I ∪ D) P' S hPsub hprocessed hsafe o ho a)
    apply hb.trans
    simpa only [R, Q] using
      (Nat.add_le_add (hc.trans ((hcollision o).1 a)) ((hforbidden o).1 a)).trans hcap
  · intro b
    have hb := sampledLinkBadPair_right_card_le F I D P' Q (K o) R hPsub hR b
    have hc := card_le_card (sampled_pair_conflict_right_subset_collisions U center K hcenter hout hleft hright
      r omega (I ∪ D) P' S hPsub hprocessed hsafe o ho b)
    apply hb.trans
    simpa only [R, Q] using
      (Nat.add_le_add (hc.trans ((hcollision o).2 b)) ((hforbidden o).2 b)).trans hcap

def IsSampledCandidateLinkGood
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o) (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U) (hright : ∀ o, (K o).right ⊆ U)
    (F : ForbiddenFamilyOn V) (I D : TripleSystemOn V)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop) [∀ o, DecidableRel (r o)]
    (Delta collisionCap forbiddenCap : ℕ) (omega : SimultaneousLinkPair O V K → Bool) : Prop :=
  (∀ o, IsTwoSidedRobustMatchingSample (r o) Delta (simultaneousLinkSelectedPairs K omega o)) ∧
    IsSampledLinkCollisionGood K r collisionCap omega ∧
      IsSampledLinkForbiddenGood K F I D
        (simultaneousLinkReservoir U center K hcenter hout hleft hright (candidateFilteredLinkBits K r omega)) forbiddenCap

theorem exists_simultaneousLinkCoverLaw_of_sampled_good
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o) (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U) (hright : ∀ o, (K o).right ⊆ U)
    (F : ForbiddenFamilyOn V) (available I D : TripleSystemOn V)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop) [∀ o, DecidableRel (r o)]
    (Delta collisionCap forbiddenCap : ℕ) (sigma : ℝ≥0) (hsigma : sigma ≤ 1)
    (hpacking : IsPackingOn (I ∪ D)) (havoid : AvoidsForbidden (I ∪ D) F)
    (havailable : ∀ o a b, r o a b → simultaneousLinkPairTriple K ⟨o,(a,b)⟩ ∈ available)
    (hsafe : ∀ o a b, r o a b → TriangleAvoidsGraph (coveredGraph (I ∪ D))
      (simultaneousLinkPairTriple K ⟨o,(a,b)⟩))
    (hcap : collisionCap + forbiddenCap ≤ Delta)
    (hgood : 0 < (FiniteLaw.independentBits
      (fun _ : SimultaneousLinkPair O V K ↦ sigma) (fun _ ↦ hsigma)).probability
        (IsSampledCandidateLinkGood U center K hcenter hout hleft hright F I D r Delta collisionCap forbiddenCap)) :
    ∃ law : FiniteLaw (TripleSystemOn V),
      law.SupportedOn (IsSimultaneousLinkCover F available (I ∪ D) K) ∧
      ∀ Q : TripleSystemOn V, law.probability (fun M ↦ Q ⊆ M) ≤
        (sigma / (FiniteLaw.independentBits
          (fun _ : SimultaneousLinkPair O V K ↦ sigma) (fun _ ↦ hsigma)).probability
            (IsSampledCandidateLinkGood U center K hcenter hout hleft hright F I D r Delta collisionCap forbiddenCap)) ^ Q.card := by
  apply exists_simultaneousLinkCoverLaw_of_good_reservoir_pow U center K hcenter hout hleft hright
    F available (I ∪ D) sigma hsigma
    (IsSampledCandidateLinkGood U center K hcenter hout hleft hright F I D r Delta collisionCap forbiddenCap) hgood
  intro omega homega
  obtain ⟨M, hM, hcover⟩ := exists_simultaneousLinkCover_of_sampled_counts U center K hcenter hout hleft hright
    F available I D r Delta collisionCap forbiddenCap omega homega.1 hpacking havoid havailable hsafe
    homega.2.1 homega.2.2 hcap
  exact ⟨M, hM.trans (simultaneousLinkReservoir_candidateFiltered_subset U center K hcenter hout hleft hright r omega), hcover⟩

end

end Erdos207
