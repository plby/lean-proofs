/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SupportedRobustFinalStage
import ErdosProblems.Erdos207.TypicalRobustLinkStarReadiness

/-!
# Terminal robust-link stage with raw-reservoir star caps

This terminal specialization uses the quantitatively sharp star-capped
readiness theorem and then extracts the exact KSSS outside packing.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

theorem exists_ksssOutsidePacking_of_supportedTypicalRobustStarFinalStage
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V} {law : FiniteLaw Omega}
    {G : Omega → SimpleGraph V}
    {A I D R : Omega → TripleSystemOn V}
    {K : (omega : Omega) → {x : V // x ∉ X} → BipartiteLink V}
    {alpha : ℝ≥0}
    (caps : Omega → V → ℕ)
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
    (d degreeMax codegree : ℕ)
    (hbounds : law.SupportedOn fun omega ↦
      ∀ o, HasLinkDegreeCodegreeBounds (A omega) (K omega o)
        d degreeMax codegree)
    (Delta groupSize density candidate cutoff degreeCutoff rootCutoff
      familyCutoff : ℕ)
    (hdensityLe : density ≤ d)
    (hmixing : ∀ omega, 0 < law.mass omega → ∀ o,
      0 < (K omega o).right.card → ∀ s : ℕ,
        cutoff < s → s ≤ (K omega o).right.card →
          (K omega o).right.card * (degreeMax + codegree * s) <
            s * (d - density) ^ 2)
    (hdegreeScalar : Delta * groupSize + groupSize ≤ d - cutoff)
    (hd : 2 ≤ d) (hdensityScalar : 3 * candidate ≤ density)
    (hcandidateScalar : Delta * groupSize + groupSize ≤ candidate)
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
      (Fintype.card
          (SimultaneousHallGroupIndex {x : V // x ∉ X} V (K omega)
            Delta) : ℝ≥0) * (1 - sigma) ^ groupSize +
        (Fintype.card (DistinctPair V) : ℝ≥0) *
          ((((2 : ℝ≥0) ^ (momentOrder * (familyCutoff - 1)) * kappa) ^
              momentOrder) /
            (rootCutoff + 1 : ℝ≥0) ^ momentOrder) +
        ∑ v : V,
          ((ambientTriplesThrough v).powersetCard (caps omega v)).card *
            sigma ^ caps omega v < 1)
    (hPpacking : law.SupportedOn fun omega ↦
      IsPackingOn (I omega ∪ (D omega ∪ R omega)))
    (hPavoid : law.SupportedOn fun omega ↦
      AvoidsForbidden (I omega ∪ (D omega ∪ R omega))
        (absorberErdosForbiddenConfigurationsOn q B))
    (hdegreeBudget : ∀ omega, 0 < law.mass omega → ∀ v : V,
      2 * ((triplesThrough (R omega) v).card + caps omega v) ≤
        degreeCutoff)
    (hdeletionScalar :
      degreeCutoff + rootCutoff * familyCutoff ≤ Delta)
    (hnormalizer : ∀ omega, 0 < law.mass omega →
      sigma /
          (FiniteLaw.independentBits
            (fun _ : SimultaneousLinkPair
                {x : V // x ∉ X} V (K omega) ↦ sigma)
            (fun _ ↦ hsigma)).probability
              (IsSimultaneousRobustLinkStarGood
                (absorberErdosForbiddenConfigurationsOn q B)
                (I omega ∪ (D omega ∪ R omega)) X
                (outsideVertexEmbedding X) (K omega)
                (hcenter omega) (hout omega) (hleft omega)
                (hright omega)
                (fun o ↦ linkAvailableRelation (K omega o) (A omega))
                Delta rootCutoff (caps omega)) ≤ alpha) :
    ∃ P : TripleSystemOn V, HasKSSSOutsidePacking q H X B P := by
  let P : Omega → TripleSystemOn V := fun omega ↦
    I omega ∪ (D omega ∪ R omega)
  have hready :=
    hstate.hasSimultaneousLinkCoverFamilyLaw_of_typical_structural_starCapped
      (absorberErdosForbiddenConfigurationsOn q B) G A I D R X K caps
      hcenter hout hleft hright htri hold d degreeMax codegree hbounds
      Delta groupSize density candidate cutoff degreeCutoff rootCutoff
      familyCutoff hdensityLe hmixing hdegreeScalar hd hdensityScalar
      hcandidateScalar sigma hsigma kappa momentOrder hfamily hkappa hsmall
      (by simpa only [P] using hPpacking)
      (by simpa only [P] using hPavoid) hdegreeBudget hdeletionScalar alpha
      hnormalizer
  exact exists_ksssOutsidePacking_of_supportedRobustFinalStage_available_subset
    hA hselected hcover hstate (by simpa only [P] using hready)

end

end Erdos207
