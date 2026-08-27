/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SupportedTypicalResidualLinks
import ErdosProblems.Erdos207.SupportedLinkCoverKernel
import ErdosProblems.Erdos207.ProcessedSimultaneousLinkControls

/-!
# Typical residual links are ready for the robust simultaneous law

This file packages the scalar robust-Hall calculation for the rechosen
degree/codegree-typical residual links.  The remaining hypotheses are exactly
the rooted-moment and dynamic deletion estimates of the KSSS link stage.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- On a graph supported inside `U`, the ambient neighbor set is exactly the
finite neighbor set obtained by filtering through `U`. -/
lemma neighborSet_ncard_eq_neighborsIn_card_of_supported
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V}
    (hsupport : GraphSupportedOn G (U : Set V)) (v : V) :
    (G.neighborSet v).ncard = (neighborsIn G U v).card := by
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have heq : G.neighborFinset v = neighborsIn G U v := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, mem_neighborsIn_iff]
    constructor
    · intro hvw
      exact ⟨(hsupport hvw).2, hvw⟩
    · exact fun hw ↦ hw.2
  calc
    (G.neighborSet v).ncard = G.degree v := by
      rw [← G.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard]
    _ = (G.neighborFinset v).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
    _ = (neighborsIn G U v).card := congrArg Finset.card heq

/-- The same-level upper window in iteration typicality automatically bounds
the full ambient degree when the stage graph is supported on that level. -/
theorem IsIterationTypical.neighborSet_ncard_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell + 1)}
    {G : SimpleGraph V} {A : TripleSystemOn V}
    {p eta xi : ℝ≥0} {h : ℕ} (htyp : IsIterationTypical W k G A p eta xi h)
    (i : Fin ell) (hki : k.val ≤ i.val)
    (hsupport : GraphSupportedOn G (W.U i.castSucc : Set V))
    (sideMax : ℕ)
    (hside : (1 + xi) * (p * (W.U i.castSucc).card) ≤
      (sideMax : ℝ≥0)) :
    ∀ v : V, (G.neighborSet v).ncard ≤ sideMax := by
  intro v
  rw [neighborSet_ncard_eq_neighborsIn_card_of_supported hsupport]
  by_cases hv : v ∈ W.U i.castSucc
  · have hupper := (htyp.1 i hki).1 v hv |>.2
    exact_mod_cast hupper.trans hside
  · have hempty : neighborsIn G (W.U i.castSucc) v = ∅ := by
      ext w
      constructor
      · intro hw
        exact (hv (hsupport (mem_neighborsIn_iff.mp hw).2).1).elim
      · intro hw
        simpa using hw
    simp only [hempty, card_empty, zero_le]

/-- Typical balanced residual links, the scalar Hall inequalities, and the
rooted/deletion controls supply the support-level readiness proposition used
by the totalized simultaneous-link kernel. -/
theorem hasSimultaneousLinkCoverFamilyLaw_of_typicalResidualLinks
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
          (SimultaneousHallGroupIndex {x : V // x ∉ U} V K Delta) : ℝ≥0) *
          (1 - sigma) ^ groupSize +
        (Fintype.card (DistinctPair V) : ℝ≥0) *
          ((((2 : ℝ≥0) ^ (momentOrder * (familyCutoff - 1)) * kappa) ^
              momentOrder) /
            (rootCutoff + 1 : ℝ≥0) ^ momentOrder) < 1)
    (hPpacking : IsPackingOn P) (hPavoid : AvoidsForbidden P F)
    (hbaseSafe : ∀ T ∈ available,
      TriangleAvoidsGraph (coveredGraph Pbase) T)
    (hstateControls :
      ∀ (omega : SimultaneousLinkPair {x : V // x ∉ U} V K → Bool),
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
            (IsSimultaneousRobustLinkGood F P U
              (outsideVertexEmbedding U) K hcenter hout hleft hright
              (fun o ↦ linkAvailableRelation (K o) available)
              Delta rootCutoff)) := by
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
  apply hasSimultaneousLinkCoverFamilyLaw_of_robust F available P Pbase U
    (outsideVertexEmbedding U) K hcenter hout hleft hright
    (fun o ↦ linkAvailableRelation (K o) available)
    Delta groupSize degreeCutoff rootCutoff familyCutoff hcandidates
    (fun o ↦ (hstate.1 o).2.2) sigma hsigma kappa momentOrder hfamily
    hkappa hsmall hPpacking hPavoid
  · intro o a b hab
    exact hab
  · intro o a b hab
    exact hbaseSafe _ hab
  · exact hstateControls
  · exact hdeletionScalar

/-- In a genuine intermediate master state, the historical leave condition
and fixed reserve/stage degree budgets automatically supply the dynamic
controls required by the processed-center robust sweep. -/
theorem hasSimultaneousLinkCoverFamilyLaw_of_typicalResidualLinks_structural
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
          (SimultaneousHallGroupIndex {x : V // x ∉ U} V K Delta) : ℝ≥0) *
          (1 - sigma) ^ groupSize +
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
  apply hasSimultaneousLinkCoverFamilyLaw_of_typicalResidualLinks
    F available (I ∪ (D ∪ R)) (I ∪ D) U K hstate hcenter hout
      hleft hright d degreeMax codegree hbounds Delta groupSize density
      candidate cutoff degreeCutoff rootCutoff familyCutoff hdensityLe
      hmixing hdegreeScalar hd hdensityScalar hcandidateScalar sigma
      hsigma kappa momentOrder hfamily hkappa hsmall hPpacking hPavoid
  · intro T hTA
    exact htri.triangleAvoids_coveredGraph_of_le_leave hold hTA
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

/-- Apply the typical-link robust readiness theorem at every positive-mass
state, then enlarge its state-dependent conditioning factor to one uniform
factor suitable for a totalized kernel. -/
theorem FiniteLaw.SupportedOn.hasSimultaneousLinkCoverFamilyLaw_of_typical
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {law : FiniteLaw Omega}
    (F : ForbiddenFamilyOn V)
    (available P Pbase : Omega → TripleSystemOn V)
    (U : Finset V)
    (K : (omega : Omega) → {x : V // x ∉ U} → BipartiteLink V)
    (d degreeMax codegree : ℕ)
    (hstate : law.SupportedOn fun omega ↦
      ∃ G : SimpleGraph V, ∃ I D R : TripleSystemOn V,
        IsIntermediateLinkState G U (available omega) I D R (K omega))
    (hcenter : ∀ omega o,
      (K omega o).center = outsideVertexEmbedding U o)
    (hout : ∀ omega o, outsideVertexEmbedding U o ∉ U)
    (hleft : ∀ omega o, (K omega o).left ⊆ U)
    (hright : ∀ omega o, (K omega o).right ⊆ U)
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
          relativeRootedThreatRemainder (P omega) z)
        (fun _ ↦ sigma) kappa)
    (hsmall : ∀ omega, 0 < law.mass omega →
      (Fintype.card
          (SimultaneousHallGroupIndex {x : V // x ∉ U} V (K omega)
            Delta) : ℝ≥0) *
          (1 - sigma) ^ groupSize +
        (Fintype.card (DistinctPair V) : ℝ≥0) *
          ((((2 : ℝ≥0) ^ (momentOrder * (familyCutoff - 1)) * kappa) ^
              momentOrder) /
            (rootCutoff + 1 : ℝ≥0) ^ momentOrder) < 1)
    (hPpacking : law.SupportedOn fun omega ↦ IsPackingOn (P omega))
    (hPavoid : law.SupportedOn fun omega ↦ AvoidsForbidden (P omega) F)
    (hbaseSafe : law.SupportedOn fun omega ↦ ∀ T ∈ available omega,
      TriangleAvoidsGraph (coveredGraph (Pbase omega)) T)
    (hstateControls : ∀ omega, 0 < law.mass omega →
      ∀ (bits : SimultaneousLinkPair
          {x : V // x ∉ U} V (K omega) → Bool),
      ∀ (S : Finset {x : V // x ∉ U}) (P' : TripleSystemOn V),
      P omega ⊆ P' →
      P' ⊆ P omega ∪ (available omega ∩ simultaneousLinkReservoir U
        (outsideVertexEmbedding U) (K omega) (hcenter omega)
          (hout omega) (hleft omega) (hright omega) bits) →
      IsPackingOn P' → AvoidsForbidden P' F →
      IsProcessedSimultaneousLinkFamily (K omega) S (P' \ P omega) →
      ∀ o, o ∉ S →
        (∀ a : ↑(K omega o).left,
          (leaveGraph P').Adj (K omega o).center a.1) ∧
        (∀ b : ↑(K omega o).right,
          (leaveGraph P').Adj (K omega o).center b.1) ∧
        (∀ a : ↑(K omega o).left,
          (coveredGraph (P' \ Pbase omega)).degree a.1 ≤ degreeCutoff) ∧
        (∀ b : ↑(K omega o).right,
          (coveredGraph (P' \ Pbase omega)).degree b.1 ≤ degreeCutoff))
    (hdeletionScalar : degreeCutoff + rootCutoff * familyCutoff ≤ Delta)
    (alpha : ℝ≥0)
    (hnormalizer : ∀ omega, 0 < law.mass omega →
      sigma /
          (FiniteLaw.independentBits
            (fun _ : SimultaneousLinkPair
                {x : V // x ∉ U} V (K omega) ↦ sigma)
            (fun _ ↦ hsigma)).probability
              (IsSimultaneousRobustLinkGood F (P omega) U
                (outsideVertexEmbedding U) (K omega)
                (hcenter omega) (hout omega)
                (hleft omega) (hright omega)
                (fun o ↦ linkAvailableRelation (K omega o)
                  (available omega)) Delta rootCutoff) ≤ alpha) :
    law.SupportedOn fun omega ↦
      HasSimultaneousLinkCoverFamilyLaw F (available omega) (P omega)
        (K omega) alpha := by
  intro omega hmass
  obtain ⟨G, I, D, R, hs⟩ := hstate omega hmass
  have hexact := hasSimultaneousLinkCoverFamilyLaw_of_typicalResidualLinks
    F (available omega) (P omega) (Pbase omega) U (K omega) hs
    (hcenter omega) (hout omega) (hleft omega)
    (hright omega) d degreeMax codegree (hbounds omega hmass)
    Delta groupSize density candidate cutoff degreeCutoff rootCutoff
    familyCutoff hdensityLe (hmixing omega hmass) hdegreeScalar hd
    hdensityScalar hcandidateScalar sigma hsigma kappa momentOrder hfamily
    (hkappa omega hmass) (hsmall omega hmass) (hPpacking omega hmass)
    (hPavoid omega hmass) (hbaseSafe omega hmass)
    (hstateControls omega hmass) hdeletionScalar
  exact hexact.mono (hnormalizer omega hmass)

/-- Supportwise intermediate states satisfying only their structural leave
conditions and fixed reserve/stage degree budgets are ready for the robust
simultaneous link kernel. -/
theorem FiniteLaw.SupportedOn.hasSimultaneousLinkCoverFamilyLaw_of_typical_structural
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
            Delta) : ℝ≥0) *
          (1 - sigma) ^ groupSize +
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
                (hcenter omega) (hout omega)
                (hleft omega) (hright omega)
                (fun o ↦ linkAvailableRelation (K omega o)
                  (available omega)) Delta rootCutoff) ≤ alpha) :
    law.SupportedOn fun omega ↦
      HasSimultaneousLinkCoverFamilyLaw F (available omega)
        (I omega ∪ (D omega ∪ R omega)) (K omega) alpha := by
  intro omega hmass
  have hexact :=
    hasSimultaneousLinkCoverFamilyLaw_of_typicalResidualLinks_structural
      F (available omega) U (K omega) (hstate omega hmass)
      (hcenter omega) (hout omega) (hleft omega) (hright omega)
      (htri omega hmass) (hold omega hmass)
      d degreeMax codegree (hbounds omega hmass) Delta groupSize density
      candidate cutoff degreeCutoff rootCutoff familyCutoff hdensityLe
      (hmixing omega hmass) hdegreeScalar hd hdensityScalar
      hcandidateScalar sigma hsigma kappa momentOrder hfamily
      (hkappa omega hmass) (hsmall omega hmass)
      (hPpacking omega hmass) (hPavoid omega hmass)
      sideMax (hstageDegree omega hmass) hdegreeCutoff hdeletionScalar
  exact hexact.mono (hnormalizer omega hmass)

end

end Erdos207
