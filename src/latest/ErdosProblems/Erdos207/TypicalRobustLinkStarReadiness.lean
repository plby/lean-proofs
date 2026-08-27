/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ProcessedSimultaneousLinkControls
import ErdosProblems.Erdos207.SimultaneousRobustLinkStarCoverLaw
import ErdosProblems.Erdos207.SupportedLinkCoverKernel
import ErdosProblems.Erdos207.SupportedTypicalResidualLinks

/-!
# Typical robust-link readiness with raw-reservoir star caps

This is the quantitatively sharp readiness route for the terminal link
sweep.  It conditions the raw simultaneous reservoir on vertex-star caps
and uses those caps, rather than the full stage-graph degree, to control
pair-conflict deletions during the sequential matching construction.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- Typical residual links plus robust/rooted/star scalar estimates give a
simultaneous cover law. -/
theorem hasSimultaneousLinkCoverFamilyLaw_of_typicalResidualLinks_starCapped
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    (F : ForbiddenFamilyOn V) (available P Pbase : TripleSystemOn V)
    (U : Finset V)
    (K : {x : V // x ∉ U} → BipartiteLink V)
    {I D R : TripleSystemOn V}
    (hstate : IsIntermediateLinkState G U available I D R K)
    (hcenter : ∀ o, (K o).center = outsideVertexEmbedding U o)
    (hout : ∀ o, outsideVertexEmbedding U o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U)
    (hright : ∀ o, (K o).right ⊆ U)
    (d degreeMax codegree : ℕ)
    (hbounds : ∀ o, HasLinkDegreeCodegreeBounds available (K o)
      d degreeMax codegree)
    (Delta groupSize density candidate cutoff degreeCutoff rootCutoff
      familyCutoff : ℕ)
    (caps : V → ℕ)
    (hdensityLe : density ≤ d)
    (hmixing : ∀ o, 0 < (K o).right.card → ∀ s : ℕ,
      cutoff < s → s ≤ (K o).right.card →
        (K o).right.card * (degreeMax + codegree * s) <
          s * (d - density) ^ 2)
    (hdegreeScalar : Delta * groupSize + groupSize ≤ d - cutoff)
    (hd : 2 ≤ d) (hdensityScalar : 3 * candidate ≤ density)
    (hcandidateScalar : Delta * groupSize + groupSize ≤ candidate)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1)
    (kappa : ℝ≥0) (momentOrder : ℕ)
    (hfamily : ∀ C ∈ F, C.card ≤ familyCutoff)
    (hkappa : ∀ e : DistinctPair V,
      HasExtensionBound
        (fun z : RootedThreatWitness V F e.1.1 e.1.2 ↦
          relativeRootedThreatRemainder P z)
        (fun _ ↦ sigma) kappa)
    (hsmall :
      (Fintype.card
          (SimultaneousHallGroupIndex {x : V // x ∉ U} V K Delta) :
            ℝ≥0) * (1 - sigma) ^ groupSize +
        (Fintype.card (DistinctPair V) : ℝ≥0) *
          ((((2 : ℝ≥0) ^ (momentOrder * (familyCutoff - 1)) * kappa) ^
              momentOrder) /
            (rootCutoff + 1 : ℝ≥0) ^ momentOrder) +
        ∑ v : V, ((ambientTriplesThrough v).powersetCard (caps v)).card *
          sigma ^ caps v < 1)
    (hPpacking : IsPackingOn P) (hPavoid : AvoidsForbidden P F)
    (hbaseSafe : ∀ T ∈ available,
      TriangleAvoidsGraph (coveredGraph Pbase) T)
    (hstateControls :
      ∀ (omega : SimultaneousLinkPair {x : V // x ∉ U} V K → Bool),
      LinkStarCapsGood caps
        (simultaneousLinkReservoir U (outsideVertexEmbedding U) K hcenter
          hout hleft hright omega) →
      ∀ (S : Finset {x : V // x ∉ U}) (P' : TripleSystemOn V),
      P ⊆ P' →
      P' ⊆ P ∪ (available ∩ simultaneousLinkReservoir U
        (outsideVertexEmbedding U) K hcenter hout hleft hright omega) →
      IsPackingOn P' → AvoidsForbidden P' F →
      IsProcessedSimultaneousLinkFamily K S (P' \ P) →
      ∀ o, o ∉ S →
        (∀ a : ↑(K o).left, (leaveGraph P').Adj (K o).center a.1) ∧
        (∀ b : ↑(K o).right, (leaveGraph P').Adj (K o).center b.1) ∧
        (∀ a : ↑(K o).left,
          (coveredGraph (P' \ Pbase)).degree a.1 ≤ degreeCutoff) ∧
        (∀ b : ↑(K o).right,
          (coveredGraph (P' \ Pbase)).degree b.1 ≤ degreeCutoff))
    (hdeletionScalar : degreeCutoff + rootCutoff * familyCutoff ≤ Delta) :
    HasSimultaneousLinkCoverFamilyLaw F available P K
      (sigma /
        (FiniteLaw.independentBits
          (fun _ : SimultaneousLinkPair {x : V // x ∉ U} V K ↦ sigma)
          (fun _ ↦ hsigma)).probability
            (IsSimultaneousRobustLinkStarGood F P U
              (outsideVertexEmbedding U) K hcenter hout hleft hright
              (fun o ↦ linkAvailableRelation (K o) available)
              Delta rootCutoff caps)) := by
  have hcandidates : ∀ o,
      ∀ obstruction : OrientedSmallHallObstruction
        ↑(K o).left ↑(K o).right,
        (Delta * orientedSmallHallSize obstruction + 1) * groupSize ≤
          (orientedSmallHallCandidates
            (linkAvailableRelation (K o) available) obstruction).card := by
    intro o
    exact (hbounds o).orientedSmallHallCandidateBound_of_uniform
      Delta groupSize density candidate cutoff (hstate.1 o).2.2
      hdensityLe (hmixing o) hdegreeScalar hd hdensityScalar
      hcandidateScalar
  apply exists_simultaneousRobustLinkStarCoverFamilyLaw
    F available P Pbase U (outsideVertexEmbedding U) K hcenter hout hleft
      hright (fun o ↦ linkAvailableRelation (K o) available)
      Delta groupSize degreeCutoff rootCutoff familyCutoff caps hcandidates
      (fun o ↦ (hstate.1 o).2.2) sigma hsigma kappa momentOrder hfamily
      hkappa hsmall hPpacking hPavoid
  · intro o a b hab
    exact hab
  · intro o a b hab
    exact hbaseSafe _ hab
  · exact hstateControls
  · exact hdeletionScalar

/-- Historical leave structure and a star budget discharge all dynamic
state controls for the star-capped robust sweep. -/
theorem hasSimultaneousLinkCoverFamilyLaw_of_typicalResidualLinks_structural_starCapped
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
    (d degreeMax codegree : ℕ)
    (hbounds : ∀ o, HasLinkDegreeCodegreeBounds available (K o)
      d degreeMax codegree)
    (Delta groupSize density candidate cutoff degreeCutoff rootCutoff
      familyCutoff : ℕ)
    (caps : V → ℕ)
    (hdensityLe : density ≤ d)
    (hmixing : ∀ o, 0 < (K o).right.card → ∀ s : ℕ,
      cutoff < s → s ≤ (K o).right.card →
        (K o).right.card * (degreeMax + codegree * s) <
          s * (d - density) ^ 2)
    (hdegreeScalar : Delta * groupSize + groupSize ≤ d - cutoff)
    (hd : 2 ≤ d) (hdensityScalar : 3 * candidate ≤ density)
    (hcandidateScalar : Delta * groupSize + groupSize ≤ candidate)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1)
    (kappa : ℝ≥0) (momentOrder : ℕ)
    (hfamily : ∀ C ∈ F, C.card ≤ familyCutoff)
    (hkappa : ∀ e : DistinctPair V,
      HasExtensionBound
        (fun z : RootedThreatWitness V F e.1.1 e.1.2 ↦
          relativeRootedThreatRemainder (I ∪ (D ∪ R)) z)
        (fun _ ↦ sigma) kappa)
    (hsmall :
      (Fintype.card
          (SimultaneousHallGroupIndex {x : V // x ∉ U} V K Delta) :
            ℝ≥0) * (1 - sigma) ^ groupSize +
        (Fintype.card (DistinctPair V) : ℝ≥0) *
          ((((2 : ℝ≥0) ^ (momentOrder * (familyCutoff - 1)) * kappa) ^
              momentOrder) /
            (rootCutoff + 1 : ℝ≥0) ^ momentOrder) +
        ∑ v : V, ((ambientTriplesThrough v).powersetCard (caps v)).card *
          sigma ^ caps v < 1)
    (hPpacking : IsPackingOn (I ∪ (D ∪ R)))
    (hPavoid : AvoidsForbidden (I ∪ (D ∪ R)) F)
    (hdegreeBudget : ∀ v : V,
      2 * ((triplesThrough R v).card + caps v) ≤ degreeCutoff)
    (hdeletionScalar : degreeCutoff + rootCutoff * familyCutoff ≤ Delta) :
    HasSimultaneousLinkCoverFamilyLaw F available (I ∪ (D ∪ R)) K
      (sigma /
        (FiniteLaw.independentBits
          (fun _ : SimultaneousLinkPair {x : V // x ∉ U} V K ↦ sigma)
          (fun _ ↦ hsigma)).probability
            (IsSimultaneousRobustLinkStarGood F (I ∪ (D ∪ R)) U
              (outsideVertexEmbedding U) K hcenter hout hleft hright
              (fun o ↦ linkAvailableRelation (K o) available)
              Delta rootCutoff caps)) := by
  apply hasSimultaneousLinkCoverFamilyLaw_of_typicalResidualLinks_starCapped
    F available (I ∪ (D ∪ R)) (I ∪ D) U K hstate hcenter hout
      hleft hright d degreeMax codegree hbounds Delta groupSize density
      candidate cutoff degreeCutoff rootCutoff familyCutoff caps hdensityLe
      hmixing hdegreeScalar hd hdensityScalar hcandidateScalar sigma hsigma
      kappa momentOrder hfamily hkappa hsmall hPpacking hPavoid
  · intro T hTA
    exact htri.triangleAvoids_coveredGraph_of_le_leave hold hTA
  · intro bits hstar S P' hbase hPsub hpacking _havoid hprocessed o ho
    have hleave := processedSimultaneousLink_leave_sides hcenter hout hleft
      hright hold hstate.1 hprocessed ho
    have hPsub' : P' ⊆ (I ∪ D) ∪
        (R ∪ simultaneousLinkReservoir U (outsideVertexEmbedding U) K
          hcenter hout hleft hright bits) := by
      intro T hT
      rcases mem_union.mp (hPsub hT) with hTP | hTnew
      · rcases mem_union.mp hTP with hTI | hTDR
        · exact mem_union_left _ (mem_union_left D hTI)
        · rcases mem_union.mp hTDR with hTD | hTR
          · exact mem_union_left _ (mem_union_right I hTD)
          · exact mem_union_right _ (mem_union_left _ hTR)
      · exact mem_union_right _ (mem_union_right _ (mem_inter.mp hTnew).2)
    refine ⟨hleave.1, hleave.2, ?_, ?_⟩
    · intro a
      exact (coveredGraph_sdiff_historical_degree_le_of_reservoir_starCap
        (Pbase := I ∪ D) (R := R)
        (reservoir := simultaneousLinkReservoir U
          (outsideVertexEmbedding U) K hcenter hout hleft hright bits)
        (P' := P') hPsub' hpacking caps hstar a.1).trans
          (hdegreeBudget a.1)
    · intro b
      exact (coveredGraph_sdiff_historical_degree_le_of_reservoir_starCap
        (Pbase := I ∪ D) (R := R)
        (reservoir := simultaneousLinkReservoir U
          (outsideVertexEmbedding U) K hcenter hout hleft hright bits)
        (P' := P') hPsub' hpacking caps hstar b.1).trans
          (hdegreeBudget b.1)
  · exact hdeletionScalar

/-- Supportwise star-capped structural readiness, with a uniform enlarged
C4 factor for totalizing the link kernel. -/
theorem FiniteLaw.SupportedOn.hasSimultaneousLinkCoverFamilyLaw_of_typical_structural_starCapped
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {law : FiniteLaw Omega}
    (F : ForbiddenFamilyOn V)
    (G : Omega → SimpleGraph V)
    (available I D R : Omega → TripleSystemOn V)
    (U : Finset V)
    (K : (omega : Omega) → {x : V // x ∉ U} → BipartiteLink V)
    (caps : Omega → V → ℕ)
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
    (d degreeMax codegree : ℕ)
    (hbounds : law.SupportedOn fun omega ↦
      ∀ o, HasLinkDegreeCodegreeBounds (available omega) (K omega o)
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
    (hfamily : ∀ C ∈ F, C.card ≤ familyCutoff)
    (hkappa : ∀ omega, 0 < law.mass omega → ∀ e : DistinctPair V,
      HasExtensionBound
        (fun z : RootedThreatWitness V F e.1.1 e.1.2 ↦
          relativeRootedThreatRemainder
            (I omega ∪ (D omega ∪ R omega)) z)
        (fun _ ↦ sigma) kappa)
    (hsmall : ∀ omega, 0 < law.mass omega →
      (Fintype.card
          (SimultaneousHallGroupIndex {x : V // x ∉ U} V (K omega)
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
      AvoidsForbidden (I omega ∪ (D omega ∪ R omega)) F)
    (hdegreeBudget : ∀ omega, 0 < law.mass omega → ∀ v : V,
      2 * ((triplesThrough (R omega) v).card + caps omega v) ≤
        degreeCutoff)
    (hdeletionScalar : degreeCutoff + rootCutoff * familyCutoff ≤ Delta)
    (alpha : ℝ≥0)
    (hnormalizer : ∀ omega, 0 < law.mass omega →
      sigma /
          (FiniteLaw.independentBits
            (fun _ : SimultaneousLinkPair
                {x : V // x ∉ U} V (K omega) ↦ sigma)
            (fun _ ↦ hsigma)).probability
              (IsSimultaneousRobustLinkStarGood F
                (I omega ∪ (D omega ∪ R omega)) U
                (outsideVertexEmbedding U) (K omega)
                (hcenter omega) (hout omega) (hleft omega) (hright omega)
                (fun o ↦ linkAvailableRelation (K omega o)
                  (available omega)) Delta rootCutoff (caps omega)) ≤ alpha) :
    law.SupportedOn fun omega ↦
      HasSimultaneousLinkCoverFamilyLaw F (available omega)
        (I omega ∪ (D omega ∪ R omega)) (K omega) alpha := by
  intro omega hmass
  have hexact :=
    hasSimultaneousLinkCoverFamilyLaw_of_typicalResidualLinks_structural_starCapped
      F (available omega) U (K omega) (hstate omega hmass)
      (hcenter omega) (hout omega) (hleft omega) (hright omega)
      (htri omega hmass) (hold omega hmass) d degreeMax codegree
      (hbounds omega hmass) Delta groupSize density candidate cutoff
      degreeCutoff rootCutoff familyCutoff (caps omega) hdensityLe
      (hmixing omega hmass) hdegreeScalar hd hdensityScalar
      hcandidateScalar sigma hsigma kappa momentOrder hfamily
      (hkappa omega hmass) (hsmall omega hmass)
      (hPpacking omega hmass) (hPavoid omega hmass)
      (hdegreeBudget omega hmass) hdeletionScalar
  exact hexact.mono (hnormalizer omega hmass)

end

end Erdos207
