/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SampledLinkGoodProbability
import ErdosProblems.Erdos207.SharpHallGeometricTail

/-!
# Retaining the sampled reservoir beside the selected link cover

The output space does not depend on the chosen links. Its first component
retains the actual reservoir, so forbidden failure can be averaged over
the prior law before applying the source marked moment.
-/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

structure IsSampledLinkJointOutcome
    {O V : Type*} [Fintype V] [DecidableEq V] (F : ForbiddenFamilyOn V)
    (available P : TripleSystemOn V) (K : O → BipartiteLink V)
    (z : TripleSystemOn V × TripleSystemOn V) : Prop where
  selected_subset : z.2 ⊆ z.1
  reservoir_available : z.1 ⊆ available
  reservoir_pair_safe : ∀ T ∈ z.1, TriangleAvoidsGraph (coveredGraph P) T
  selected_safe : IsSafeLinkSubfamily F available P z.2
  reservoir_family : IsSimultaneousLinkFamily K z.1
  selected_family : IsSimultaneousLinkFamily K z.2

theorem exists_rawSampledLinkJointLaw
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
    (hcap : collisionCap+forbiddenCap ≤ Delta)
    (hbalanced : ∀ o, (K o).left.card = (K o).right.card)
    (hdegL : ∀ o (a : ↥(K o).left), (univ.filter (r o a)).card ≤ degree)
    (hdegR : ∀ o (b : ↥(K o).right), (univ.filter (fun a ↦ r o a b)).card ≤ degree)
    (hoverlap : ∀ x : SimultaneousLinkPair O V K, (otherLinkCoordinates K r x).card ≤ overlap)
    (hs : 2*s ≤ collisionCap+1) :
    ∃ law : FiniteLaw (TripleSystemOn V × TripleSystemOn V),
      law.SupportedOn (IsSampledLinkJointOutcome F available (I ∪ D) K) ∧
      (∀ Q : TripleSystemOn V, law.probability (fun z ↦ Q ⊆ z.1) ≤ sigma^Q.card) ∧
      law.probability (fun z ↦ ¬ ∀ o, CoversBipartiteLink (K o) z.2) ≤
        (∑ o : O, ∑ h : OrientedSmallHallObstruction ↥(K o).left ↥(K o).right,
          (1-sigma/2)^(orientedSmallHallCandidates (r o) h).card /
            (1/2 : ℝ≥0)^(Delta*orientedSmallHallSize h)) +
        (∑ o, ((K o).left.card+(K o).right.card : ℝ≥0)*
          (2*(degree : ℝ≥0)*overlap*sigma^2/(collisionCap+1))^s) +
        law.probability (fun z ↦ ¬ IsSampledLinkForbiddenGood K F I D z.1 forbiddenCap) := by
  obtain ⟨selected, hselected⟩ := exists_rawSampledLinkSelector U center K hcenter hout hleft hright
    F available I D r Delta collisionCap forbiddenCap hpacking havoid havailable hsafe hcap
  let L := FiniteLaw.independentBits (fun _ : SimultaneousLinkPair O V K ↦ sigma) (fun _ ↦ hsigma)
  let reservoir := fun omega ↦ simultaneousLinkReservoir U center K hcenter hout hleft hright
    (candidateFilteredLinkBits K r omega)
  let output := fun omega ↦ (reservoir omega, selected omega)
  refine ⟨L.map output, ?_, ?_, ?_⟩
  · have htrivial : L.SupportedOn (fun _ ↦ True) := fun _ _ ↦ trivial
    apply htrivial.map (Q := IsSampledLinkJointOutcome F available (I ∪ D) K) output
    intro omega _
    have hfamily := simultaneousLinkReservoir_isSimultaneousLinkFamily U center K hcenter hout hleft hright
      (candidateFilteredLinkBits K r omega)
    refine ⟨(hselected omega).1,
      simultaneousLinkReservoir_candidateFiltered_subset_available U center K hcenter hout hleft hright r
        available havailable omega, ?_, (hselected omega).2.1, hfamily, hfamily.mono (hselected omega).1⟩
    intro T hT
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hT
    exact hsafe x.1 x.2.1 x.2.2
      ((candidateFilteredLinkBits_true_iff K r omega x).mp (FiniteLaw.mem_selectedByBits_iff.mp hx)).1
  · intro Q
    rw [FiniteLaw.probability_map]
    exact simultaneousLinkReservoir_candidateFiltered_probability_subset_le
      U center K hcenter hout hleft hright r sigma hsigma Q
  · simp only [FiniteLaw.probability_map, output]
    apply le_trans _ (independentBits_not_sampledCandidateLinkGood_le U center K hcenter hout hleft hright
      F I D r Delta collisionCap forbiddenCap degree overlap s sigma hsigma hbalanced hdegL hdegR hoverlap hs
      (L.probability (fun omega ↦ ¬ IsSampledLinkForbiddenGood K F I D (reservoir omega) forbiddenCap)) le_rfl)
    exact L.probability_mono (fun omega hnot hg ↦ hnot ((hselected omega).2.2 hg))

theorem exists_rawSampledLinkJointLaw_geometric
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o) (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U) (hright : ∀ o, (K o).right ⊆ U)
    (F : ForbiddenFamilyOn V) (available I D : TripleSystemOn V)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop) [∀ o, DecidableRel (r o)]
    (Delta collisionCap forbiddenCap degree overlap s t N : ℕ) (c : O → ℕ)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1)
    (hpacking : IsPackingOn (I ∪ D)) (havoid : AvoidsForbidden (I ∪ D) F)
    (havailable : ∀ o a b, r o a b → simultaneousLinkPairTriple K ⟨o,(a,b)⟩ ∈ available)
    (hsafe : ∀ o a b, r o a b → TriangleAvoidsGraph (coveredGraph (I ∪ D))
      (simultaneousLinkPairTriple K ⟨o,(a,b)⟩))
    (hcap : collisionCap+forbiddenCap ≤ Delta)
    (hbalanced : ∀ o, (K o).left.card = (K o).right.card)
    (hsize : ∀ o, (K o).left.card ≤ N ∧ (K o).right.card ≤ N)
    (hdegL : ∀ o (a : ↥(K o).left), (univ.filter (r o a)).card ≤ degree)
    (hdegR : ∀ o (b : ↥(K o).right), (univ.filter (fun a ↦ r o a b)).card ≤ degree)
    (hoverlap : ∀ x : SimultaneousLinkPair O V K, (otherLinkCoordinates K r x).card ≤ overlap)
    (hs : 2*s ≤ collisionCap+1)
    (hcandidate : ∀ o (h : OrientedSmallHallObstruction ↥(K o).left ↥(K o).right),
      c o*orientedSmallHallSize h ≤ (orientedSmallHallCandidates (r o) h).card)
    (hbudget : ∀ o, (Delta+t : ℝ≥0) ≤ sigma*c o/2)
    (hsmall : 2*(N+1 : ℝ≥0)^2*(1/2 : ℝ≥0)^t ≤ 1/2) :
    ∃ law : FiniteLaw (TripleSystemOn V × TripleSystemOn V),
      law.SupportedOn (IsSampledLinkJointOutcome F available (I ∪ D) K) ∧
      (∀ Q : TripleSystemOn V, law.probability (fun z ↦ Q ⊆ z.1) ≤ sigma^Q.card) ∧
      law.probability (fun z ↦ ¬ ∀ o, CoversBipartiteLink (K o) z.2) ≤
        8*(Fintype.card O : ℝ≥0)*(N+1 : ℝ≥0)^2*(1/2 : ℝ≥0)^t +
        (∑ o, ((K o).left.card+(K o).right.card : ℝ≥0)*
          (2*(degree : ℝ≥0)*overlap*sigma^2/(collisionCap+1))^s) +
        law.probability (fun z ↦ ¬ IsSampledLinkForbiddenGood K F I D z.1 forbiddenCap) := by
  obtain ⟨law, hstruct, hpoint, hfail⟩ := exists_rawSampledLinkJointLaw U center K hcenter hout hleft hright
    F available I D r Delta collisionCap forbiddenCap degree overlap s sigma hsigma hpacking havoid
    havailable hsafe hcap hbalanced hdegL hdegR hoverlap hs
  refine ⟨law, hstruct, hpoint, hfail.trans ?_⟩
  exact add_le_add (add_le_add
    (simultaneous_sharpHall_sum_le_geometric K r hbalanced sigma hsigma c Delta t N hsize hcandidate hbudget hsmall)
    le_rfl) le_rfl

theorem FiniteLaw.sampledLinkJoint_selected_probability_le
    {O V : Type*} [Fintype V] [DecidableEq V]
    (L : FiniteLaw (TripleSystemOn V × TripleSystemOn V))
    {F : ForbiddenFamilyOn V} {A P : TripleSystemOn V} {K : O → BipartiteLink V}
    (hstruct : L.SupportedOn (IsSampledLinkJointOutcome F A P K)) (sigma : ℝ≥0)
    (hpoint : ∀ Q : TripleSystemOn V, L.probability (fun z ↦ Q ⊆ z.1) ≤ sigma^Q.card)
    (Q : TripleSystemOn V) : L.probability (fun z ↦ Q ⊆ z.2) ≤ sigma^Q.card := by
  apply le_trans _ (hpoint Q)
  exact L.probability_mono_of_supported hstruct (fun z hz hQ ↦ hQ.trans hz.selected_subset)

end

end Erdos207
