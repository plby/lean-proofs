/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SharpSimultaneousRobustLinkCoverLaw
import ErdosProblems.Erdos207.ProcessedSimultaneousLinkControls
import ErdosProblems.Erdos207.SupportedLinkCoverKernel

/-!
# Structural residual-link readiness with exact Hall tails

Unlike the block-sampling interface, the exact binomial tail needs no
auxiliary group size.  The residual links only need to be balanced; the
desired quantitative strength is stated directly by the sharp tail sum.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem hasSimultaneousLinkCoverFamilyLaw_of_structural_sharp
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    (F : ForbiddenFamilyOn V) (available : TripleSystemOn V)
    (U : Finset V)
    (K : {x : V // x ∉ U} → BipartiteLink V)
    {I D R : TripleSystemOn V}
    (hstate : IsIntermediateLinkState G U available I D R K)
    (hcenter : ∀ o, (K o).center = outsideVertexEmbedding U o)
    (hout : ∀ o, outsideVertexEmbedding U o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U)
    (hright : ∀ o, (K o).right ⊆ U)
    (htri : ConsistsOfTriangles G available)
    (hold : G ≤ leaveGraph (I ∪ D))
    (Delta degreeCutoff rootCutoff familyCutoff : ℕ)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1)
    (kappa : ℝ≥0) (momentOrder : ℕ)
    (hfamily : ∀ C ∈ F, C.card ≤ familyCutoff)
    (hkappa : ∀ e : DistinctPair V,
      HasExtensionBound
        (fun z : RootedThreatWitness V F e.1.1 e.1.2 ↦
          relativeRootedThreatRemainder (I ∪ (D ∪ R)) z)
        (fun _ ↦ sigma) kappa)
    (hsmall :
      (∑ o : {x : V // x ∉ U},
        ∑ h : OrientedSmallHallObstruction
            ↥(K o).left ↥(K o).right,
          (1 - sigma / 2) ^
              (orientedSmallHallCandidates
                (linkAvailableRelation (K o) available) h).card /
            (1 / 2 : ℝ≥0) ^ (Delta * orientedSmallHallSize h)) +
        (Fintype.card (DistinctPair V) : ℝ≥0) *
          ((((2 : ℝ≥0) ^ (momentOrder * (familyCutoff - 1)) * kappa) ^
              momentOrder) /
            (rootCutoff + 1 : ℝ≥0) ^ momentOrder) < 1)
    (hPpacking : IsPackingOn (I ∪ (D ∪ R)))
    (hPavoid : AvoidsForbidden (I ∪ (D ∪ R)) F)
    (sideMax : ℕ)
    (hstageDegree : ∀ v : V, (G.neighborSet v).ncard ≤ sideMax)
    (hdegreeCutoff : sideMax + sideMax ≤ degreeCutoff)
    (hdeletionScalar : degreeCutoff + rootCutoff * familyCutoff ≤ Delta) :
    HasSimultaneousLinkCoverFamilyLaw F available (I ∪ (D ∪ R)) K
      (sigma /
        (FiniteLaw.independentBits
          (fun _ : SimultaneousLinkPair {x : V // x ∉ U} V K ↦ sigma)
          (fun _ ↦ hsigma)).probability
            (IsSimultaneousRobustLinkGood F (I ∪ (D ∪ R)) U
              (outsideVertexEmbedding U) K hcenter hout hleft hright
              (fun o ↦ linkAvailableRelation (K o) available)
              Delta rootCutoff)) := by
  apply exists_simultaneousRobustLinkCoverFamilyLaw_sharp
    F available (I ∪ (D ∪ R)) (I ∪ D) U (outsideVertexEmbedding U) K
      hcenter hout hleft hright
      (fun o ↦ linkAvailableRelation (K o) available)
      Delta degreeCutoff rootCutoff familyCutoff
      (fun o ↦ (hstate.1 o).2.2) sigma hsigma kappa momentOrder hfamily
      hkappa hsmall hPpacking hPavoid
  · intro o a b hab
    exact hab
  · intro o a b hab
    exact htri.triangleAvoids_coveredGraph_of_le_leave hold hab
  · intro bits S P' hbase hPsub _hpacking _havoid hprocessed o ho
    apply processedSimultaneousLink_stateControls hcenter hout hleft hright
      htri hold hstate.1
    · intro T hT
      rcases mem_union.mp (hPsub hT) with hTbase | hTnew
      · exact mem_union_left available hTbase
      · exact mem_union_right (I ∪ (D ∪ R)) (mem_inter.mp hTnew).1
    · exact hprocessed
    · intro o a
      have hG := hstageDegree a.1
      exact (Nat.add_le_add
        ((htri.coveredGraph_degree_le_neighborSet_ncard hstate.2.1 a.1).trans hG)
        hG).trans hdegreeCutoff
    · intro o b
      have hG := hstageDegree b.1
      exact (Nat.add_le_add
        ((htri.coveredGraph_degree_le_neighborSet_ncard hstate.2.1 b.1).trans hG)
        hG).trans hdegreeCutoff
    · exact ho
  · exact hdeletionScalar

theorem FiniteLaw.SupportedOn.hasSimultaneousLinkCoverFamilyLaw_of_structural_sharp_supported
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {law : FiniteLaw Omega}
    (F : ForbiddenFamilyOn V)
    (G : Omega → SimpleGraph V)
    (available I D R : Omega → TripleSystemOn V)
    (U : Finset V)
    (K : (omega : Omega) → {x : V // x ∉ U} → BipartiteLink V)
    (hstate : law.SupportedOn fun omega ↦
      IsIntermediateLinkState (G omega) U (available omega)
        (I omega) (D omega) (R omega) (K omega))
    (hcenter : ∀ omega o,
      (K omega o).center = outsideVertexEmbedding U o)
    (hout : ∀ omega o, outsideVertexEmbedding U o ∉ U)
    (hleft : ∀ omega o, (K omega o).left ⊆ U)
    (hright : ∀ omega o, (K omega o).right ⊆ U)
    (htri : law.SupportedOn fun omega ↦
      ConsistsOfTriangles (G omega) (available omega))
    (hold : law.SupportedOn fun omega ↦
      G omega ≤ leaveGraph (I omega ∪ D omega))
    (Delta degreeCutoff rootCutoff familyCutoff : ℕ)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1)
    (kappa : ℝ≥0) (momentOrder : ℕ)
    (hfamily : ∀ C ∈ F, C.card ≤ familyCutoff)
    (hkappa : ∀ omega, 0 < law.mass omega → ∀ e : DistinctPair V,
      HasExtensionBound
        (fun z : RootedThreatWitness V F e.1.1 e.1.2 ↦
          relativeRootedThreatRemainder
            (I omega ∪ (D omega ∪ R omega)) z)
        (fun _ ↦ sigma) kappa)
    (hsmall : ∀ omega, 0 < law.mass omega →
      (∑ o : {x : V // x ∉ U},
        ∑ h : OrientedSmallHallObstruction
            ↥(K omega o).left ↥(K omega o).right,
          (1 - sigma / 2) ^
              (orientedSmallHallCandidates
                (linkAvailableRelation (K omega o) (available omega)) h).card /
            (1 / 2 : ℝ≥0) ^ (Delta * orientedSmallHallSize h)) +
        (Fintype.card (DistinctPair V) : ℝ≥0) *
          ((((2 : ℝ≥0) ^ (momentOrder * (familyCutoff - 1)) * kappa) ^
              momentOrder) /
            (rootCutoff + 1 : ℝ≥0) ^ momentOrder) < 1)
    (hPpacking : law.SupportedOn fun omega ↦
      IsPackingOn (I omega ∪ (D omega ∪ R omega)))
    (hPavoid : law.SupportedOn fun omega ↦
      AvoidsForbidden (I omega ∪ (D omega ∪ R omega)) F)
    (sideMax : ℕ)
    (hstageDegree : ∀ omega, 0 < law.mass omega →
      ∀ v : V, ((G omega).neighborSet v).ncard ≤ sideMax)
    (hdegreeCutoff : sideMax + sideMax ≤ degreeCutoff)
    (hdeletionScalar : degreeCutoff + rootCutoff * familyCutoff ≤ Delta)
    (alpha : ℝ≥0)
    (hnormalizer : ∀ omega, 0 < law.mass omega →
      sigma /
          (FiniteLaw.independentBits
            (fun _ : SimultaneousLinkPair
                {x : V // x ∉ U} V (K omega) ↦ sigma)
            (fun _ ↦ hsigma)).probability
              (IsSimultaneousRobustLinkGood F
                (I omega ∪ (D omega ∪ R omega)) U
                (outsideVertexEmbedding U) (K omega)
                (hcenter omega) (hout omega) (hleft omega) (hright omega)
                (fun o ↦ linkAvailableRelation (K omega o)
                  (available omega)) Delta rootCutoff) ≤ alpha) :
    law.SupportedOn fun omega ↦
      HasSimultaneousLinkCoverFamilyLaw F (available omega)
        (I omega ∪ (D omega ∪ R omega)) (K omega) alpha := by
  intro omega hmass
  have hexact := hasSimultaneousLinkCoverFamilyLaw_of_structural_sharp
    F (available omega) U (K omega) (hstate omega hmass)
      (hcenter omega) (hout omega) (hleft omega) (hright omega)
      (htri omega hmass) (hold omega hmass) Delta degreeCutoff rootCutoff
      familyCutoff sigma hsigma kappa momentOrder hfamily
      (hkappa omega hmass) (hsmall omega hmass)
      (hPpacking omega hmass) (hPavoid omega hmass) sideMax
      (hstageDegree omega hmass) hdegreeCutoff hdeletionScalar
  exact hexact.mono (hnormalizer omega hmass)

end

end Erdos207
