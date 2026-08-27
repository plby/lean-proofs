/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SharpTypicalRobustLinkReadiness
import ErdosProblems.Erdos207.SupportedRobustFinalStage

/-! # Terminal extraction using the exact Hall-tail link law -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem exists_ksssOutsidePacking_of_supportedRobustFinalStage_sharp
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V} {law : FiniteLaw Omega}
    {G : Omega → SimpleGraph V}
    {A I D R : Omega → TripleSystemOn V}
    {K : (omega : Omega) → {x : V // x ∉ X} → BipartiteLink V}
    {alpha : ℝ≥0}
    (hA : law.SupportedOn fun omega ↦
      A omega ⊆ outsideAvailableTriangles H B)
    (hselected : law.SupportedOn fun omega ↦
      I omega ∪ D omega ⊆ outsideAvailableTriangles H B)
    (hcover : law.SupportedOn fun omega ↦
      CoversOriginalGraph
        (graphDifference (SimpleGraph.completeGraph V) H)
        (G omega) (I omega) (D omega))
    (hstate : law.SupportedOn fun omega ↦
      IsIntermediateLinkState (G omega) X (A omega) (I omega) (D omega)
        (R omega) (K omega))
    (hcenter : ∀ omega o,
      (K omega o).center = outsideVertexEmbedding X o)
    (hout : ∀ omega o, outsideVertexEmbedding X o ∉ X)
    (hleft : ∀ omega o, (K omega o).left ⊆ X)
    (hright : ∀ omega o, (K omega o).right ⊆ X)
    (htri : law.SupportedOn fun omega ↦
      ConsistsOfTriangles (G omega) (A omega))
    (hold : law.SupportedOn fun omega ↦
      G omega ≤ leaveGraph (I omega ∪ D omega))
    (Delta degreeCutoff rootCutoff familyCutoff : ℕ)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1)
    (kappa : ℝ≥0) (momentOrder : ℕ)
    (hfamily : ∀ C ∈ absorberErdosForbiddenConfigurationsOn q B,
      C.card ≤ familyCutoff)
    (hkappa : ∀ omega, 0 < law.mass omega → ∀ e : DistinctPair V,
      HasExtensionBound
        (fun z : RootedThreatWitness V
            (absorberErdosForbiddenConfigurationsOn q B) e.1.1 e.1.2 ↦
          relativeRootedThreatRemainder
            (I omega ∪ (D omega ∪ R omega)) z)
        (fun _ ↦ sigma) kappa)
    (hsmall : ∀ omega, 0 < law.mass omega →
      (∑ o : {x : V // x ∉ X},
        ∑ h : OrientedSmallHallObstruction
            ↥(K omega o).left ↥(K omega o).right,
          (1 - sigma / 2) ^
              (orientedSmallHallCandidates
                (linkAvailableRelation (K omega o) (A omega)) h).card /
            (1 / 2 : ℝ≥0) ^ (Delta * orientedSmallHallSize h)) +
        (Fintype.card (DistinctPair V) : ℝ≥0) *
          ((((2 : ℝ≥0) ^ (momentOrder * (familyCutoff - 1)) * kappa) ^
              momentOrder) /
            (rootCutoff + 1 : ℝ≥0) ^ momentOrder) < 1)
    (hPpacking : law.SupportedOn fun omega ↦
      IsPackingOn (I omega ∪ (D omega ∪ R omega)))
    (hPavoid : law.SupportedOn fun omega ↦
      AvoidsForbidden (I omega ∪ (D omega ∪ R omega))
        (absorberErdosForbiddenConfigurationsOn q B))
    (sideMax : ℕ)
    (hstageDegree : ∀ omega, 0 < law.mass omega →
      ∀ v : V, ((G omega).neighborSet v).ncard ≤ sideMax)
    (hdegreeCutoff : sideMax + sideMax ≤ degreeCutoff)
    (hdeletionScalar : degreeCutoff + rootCutoff * familyCutoff ≤ Delta)
    (hnormalizer : ∀ omega, 0 < law.mass omega →
      sigma /
          (FiniteLaw.independentBits
            (fun _ : SimultaneousLinkPair
                {x : V // x ∉ X} V (K omega) ↦ sigma)
            (fun _ ↦ hsigma)).probability
              (IsSimultaneousRobustLinkGood
                (absorberErdosForbiddenConfigurationsOn q B)
                (I omega ∪ (D omega ∪ R omega)) X
                (outsideVertexEmbedding X) (K omega)
                (hcenter omega) (hout omega) (hleft omega) (hright omega)
                (fun o ↦ linkAvailableRelation (K omega o) (A omega))
                Delta rootCutoff) ≤ alpha) :
    ∃ P : TripleSystemOn V, HasKSSSOutsidePacking q H X B P := by
  have hready :=
    hstate.hasSimultaneousLinkCoverFamilyLaw_of_structural_sharp_supported
      (absorberErdosForbiddenConfigurationsOn q B) G A I D R X K
      hcenter hout hleft hright htri hold Delta degreeCutoff rootCutoff
      familyCutoff sigma hsigma kappa momentOrder hfamily hkappa hsmall
      hPpacking hPavoid sideMax hstageDegree hdegreeCutoff hdeletionScalar
      alpha hnormalizer
  exact exists_ksssOutsidePacking_of_supportedRobustFinalStage_available_subset
    hA hselected hcover hstate hready

end

end Erdos207
