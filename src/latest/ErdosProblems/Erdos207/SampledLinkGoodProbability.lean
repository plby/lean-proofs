/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SampledLinkCollisionTail
import ErdosProblems.Erdos207.RawSampledLinkCoverLaw
import ErdosProblems.Erdos207.SharpRobustHallSampling

/-! # The actual sampled good-event failure and totalized cover law -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem independentBits_not_sampledCandidateLinkGood_le
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o) (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U) (hright : ∀ o, (K o).right ⊆ U)
    (F : ForbiddenFamilyOn V) (I D : TripleSystemOn V)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop) [∀ o, DecidableRel (r o)]
    (Delta collisionCap forbiddenCap degree overlap s : ℕ) (sigma : ℝ≥0) (hsigma : sigma ≤ 1)
    (hbalanced : ∀ o, (K o).left.card = (K o).right.card)
    (hdegL : ∀ o (a : ↥(K o).left), (univ.filter (r o a)).card ≤ degree)
    (hdegR : ∀ o (b : ↥(K o).right), (univ.filter (fun a ↦ r o a b)).card ≤ degree)
    (hoverlap : ∀ x : SimultaneousLinkPair O V K, (otherLinkCoordinates K r x).card ≤ overlap)
    (hs : 2 * s ≤ collisionCap + 1) (forbiddenError : ℝ≥0)
    (hforbidden : (FiniteLaw.independentBits
      (fun _ : SimultaneousLinkPair O V K ↦ sigma) (fun _ ↦ hsigma)).probability
        (fun omega ↦ ¬ IsSampledLinkForbiddenGood K F I D
          (simultaneousLinkReservoir U center K hcenter hout hleft hright (candidateFilteredLinkBits K r omega)) forbiddenCap) ≤ forbiddenError) :
    (FiniteLaw.independentBits (fun _ : SimultaneousLinkPair O V K ↦ sigma) (fun _ ↦ hsigma)).probability
      (fun omega ↦ ¬ IsSampledCandidateLinkGood U center K hcenter hout hleft hright F I D r Delta collisionCap forbiddenCap omega) ≤
      (∑ o : O, ∑ h : OrientedSmallHallObstruction ↥(K o).left ↥(K o).right,
        (1 - sigma / 2) ^ (orientedSmallHallCandidates (r o) h).card /
          (1 / 2 : ℝ≥0) ^ (Delta * orientedSmallHallSize h)) +
      (∑ o, ((K o).left.card + (K o).right.card : ℝ≥0) *
        (2 * (degree : ℝ≥0) * overlap * sigma ^ 2 / (collisionCap + 1)) ^ s) + forbiddenError := by
  let L := FiniteLaw.independentBits (fun _ : SimultaneousLinkPair O V K ↦ sigma) (fun _ ↦ hsigma)
  let H := fun omega ↦ ∀ o, IsTwoSidedRobustMatchingSample (r o) Delta (simultaneousLinkSelectedPairs K omega o)
  let C := IsSampledLinkCollisionGood K r collisionCap
  let B := fun omega ↦ IsSampledLinkForbiddenGood K F I D
    (simultaneousLinkReservoir U center K hcenter hout hleft hright (candidateFilteredLinkBits K r omega)) forbiddenCap
  calc
    _ ≤ L.probability (fun omega ↦ (¬ H omega ∨ ¬ C omega) ∨ ¬ B omega) := by
      apply L.probability_mono
      intro omega hbad
      change ¬ (H omega ∧ C omega ∧ B omega) at hbad
      tauto
    _ ≤ (L.probability (fun omega ↦ ¬ H omega) + L.probability (fun omega ↦ ¬ C omega)) +
        L.probability (fun omega ↦ ¬ B omega) :=
      (L.probability_or_le _ _).trans (add_le_add (L.probability_or_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add
      (independentBits_probability_not_all_twoSidedRobust_le_sharp K r Delta hbalanced sigma hsigma)
      (independentBits_not_sampledLinkCollisionGood_le K r sigma hsigma degree overlap collisionCap s hdegL hdegR hoverlap hs)) hforbidden

theorem exists_rawSampledLinkCoverLaw_with_failure_bound
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o) (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U) (hright : ∀ o, (K o).right ⊆ U)
    (F : ForbiddenFamilyOn V) (available I D : TripleSystemOn V)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop) [∀ o, DecidableRel (r o)]
    (Delta collisionCap forbiddenCap degree overlap s : ℕ) (sigma : ℝ≥0) (hsigma : sigma ≤ 1)
    (hpacking : IsPackingOn (I ∪ D)) (havoid : AvoidsForbidden (I ∪ D) F)
    (havailable : ∀ o a b, r o a b → simultaneousLinkPairTriple K ⟨o,(a,b)⟩ ∈ available)
    (hsafe : ∀ o a b, r o a b → TriangleAvoidsGraph (coveredGraph (I ∪ D))
      (simultaneousLinkPairTriple K ⟨o,(a,b)⟩))
    (hcap : collisionCap + forbiddenCap ≤ Delta)
    (hbalanced : ∀ o, (K o).left.card = (K o).right.card)
    (hdegL : ∀ o (a : ↥(K o).left), (univ.filter (r o a)).card ≤ degree)
    (hdegR : ∀ o (b : ↥(K o).right), (univ.filter (fun a ↦ r o a b)).card ≤ degree)
    (hoverlap : ∀ x : SimultaneousLinkPair O V K, (otherLinkCoordinates K r x).card ≤ overlap)
    (hs : 2 * s ≤ collisionCap + 1) (forbiddenError : ℝ≥0)
    (hforbidden : (FiniteLaw.independentBits
      (fun _ : SimultaneousLinkPair O V K ↦ sigma) (fun _ ↦ hsigma)).probability
        (fun omega ↦ ¬ IsSampledLinkForbiddenGood K F I D
          (simultaneousLinkReservoir U center K hcenter hout hleft hright (candidateFilteredLinkBits K r omega)) forbiddenCap) ≤ forbiddenError) :
    ∃ law : FiniteLaw (TripleSystemOn V),
      law.SupportedOn (IsSafeLinkSubfamily F available (I ∪ D)) ∧
      (∀ Q : TripleSystemOn V, law.probability (fun M ↦ Q ⊆ M) ≤ sigma ^ Q.card) ∧
      law.probability (fun M ↦ ¬ ∀ o, CoversBipartiteLink (K o) M) ≤
        (∑ o : O, ∑ h : OrientedSmallHallObstruction ↥(K o).left ↥(K o).right,
          (1 - sigma / 2) ^ (orientedSmallHallCandidates (r o) h).card /
            (1 / 2 : ℝ≥0) ^ (Delta * orientedSmallHallSize h)) +
        (∑ o, ((K o).left.card + (K o).right.card : ℝ≥0) *
          (2 * (degree : ℝ≥0) * overlap * sigma ^ 2 / (collisionCap + 1)) ^ s) + forbiddenError := by
  obtain ⟨law, hstruct, hpoint, hfail⟩ := exists_rawSampledLinkCoverLaw U center K hcenter hout hleft hright
    F available I D r Delta collisionCap forbiddenCap sigma hsigma hpacking havoid havailable hsafe hcap
  refine ⟨law, hstruct, hpoint, hfail.trans ?_⟩
  exact independentBits_not_sampledCandidateLinkGood_le U center K hcenter hout hleft hright F I D r
    Delta collisionCap forbiddenCap degree overlap s sigma hsigma hbalanced hdegL hdegR hoverlap hs forbiddenError hforbidden

end

end Erdos207
