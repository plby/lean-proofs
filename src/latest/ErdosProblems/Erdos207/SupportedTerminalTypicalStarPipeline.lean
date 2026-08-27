/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SupportedTypicalResidualLinks
import ErdosProblems.Erdos207.SupportedTypicalRobustStarFinalStage
import ErdosProblems.Erdos207.TypicalRobustLinkReadiness

/-!
# Terminal typical-link pipeline with raw-reservoir star caps

The arbitrary balanced residual bipartitions are reselected with the usual
degree/codegree guarantees.  The terminal robust sweep is then run under
raw-reservoir vertex-star caps, yielding the exact outside packing without
charging the deletion budget for the full stage degree.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

theorem exists_ksssOutsidePacking_of_supportedIntermediateTypical_starCapped
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {law : FiniteLaw Omega} {W : Vortex V ell}
    {k : Fin (ell + 1)} (i : Fin ell) (hki : k.val ≤ i.val)
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V}
    {G : Omega → SimpleGraph V}
    {A I D R : Omega → TripleSystemOn V}
    {reserve : Omega → Finset (Sym2 V)}
    {Kold : (omega : Omega) →
      {x : V // x ∉ W.U i.succ} → BipartiteLink V}
    {p eta xi : ℝ≥0} {h : ℕ}
    (caps : Omega → V → ℕ)
    (hX : X = W.U i.succ)
    (hA : law.SupportedOn fun omega ↦
      A omega ⊆ outsideAvailableTriangles H B)
    (hselected : law.SupportedOn fun omega ↦
      I omega ∪ D omega ⊆ outsideAvailableTriangles H B)
    (hcover : law.SupportedOn fun omega ↦
      CoversOriginalGraph
        (graphDifference (SimpleGraph.completeGraph V) H)
        (G omega) (I omega) (D omega))
    (htyp : law.SupportedOn fun omega ↦
      IsIterationTypical W k (G omega) (A omega) p eta xi h)
    (htri : law.SupportedOn fun omega ↦
      ConsistsOfTriangles (G omega) (A omega))
    (hold : law.SupportedOn fun omega ↦
      G omega ≤ leaveGraph (I omega ∪ D omega))
    (hGsupp : law.SupportedOn fun omega ↦
      GraphSupportedOn (G omega) (W.U i.castSucc : Set V))
    (hstateOld : law.SupportedOn fun omega ↦
      IsIntermediateLinkState (G omega) (W.U i.succ) (A omega)
          (I omega) (D omega) (R omega) (Kold omega) ∧
        (∀ o, (Kold omega o).center =
          outsideVertexEmbedding (W.U i.succ) o) ∧
        (∀ o, outsideVertexEmbedding (W.U i.succ) o ∉ W.U i.succ) ∧
        (∀ o, (Kold omega o).left ⊆ W.U i.succ) ∧
        (∀ o, (Kold omega o).right ⊆ W.U i.succ) ∧
        (∀ o, (Kold omega o).SpokesIn (reserve omega)))
    (hpacking : law.SupportedOn fun omega ↦
      IsPackingOn (I omega ∪ (D omega ∪ R omega)))
    (havoid : law.SupportedOn fun omega ↦
      AvoidsForbidden (I omega ∪ (D omega ∪ R omega))
        (absorberErdosForbiddenConfigurationsOn q B))
    (m d degreeMax codegree loss : ℕ)
    (hh : 3 ≤ h)
    (hlower : (m + loss + 1 : ℝ≥0) ≤
      (1 - xi) * (p ^ 2 * eta * (W.U i.succ).card))
    (hupper : (1 + xi) *
      (p ^ 2 * eta * (W.U i.succ).card) ≤ (degreeMax : ℝ≥0))
    (hcodegree : (1 + xi) *
      (p ^ 3 * eta ^ 2 * (W.U i.succ).card) ≤ (codegree : ℝ≥0))
    (hbisection : ∀ omega, 0 < law.mass omega →
      ∀ o : {x : V // x ∉ W.U i.succ},
      ((@residualNeighbors V _ _ (G omega)
          (Classical.decRel (G omega).Adj) (R omega) o.1).card : ℝ≥0) *
        (2 * (2 : ℝ≥0) ^ d * (3 / 4 : ℝ≥0) ^ (m - 2 * d)) < 1)
    (Delta groupSize density candidate cutoff degreeCutoff rootCutoff
      familyCutoff : ℕ)
    (hdensityLe : density ≤ d)
    (hmixing : ∀ omega, 0 < law.mass omega →
      ∀ o : {x : V // x ∉ W.U i.succ},
      let K := supportedReserveTypicalResidualLinks G (W.U i.succ)
        reserve A I D R d degreeMax codegree omega
      0 < (K o).right.card → ∀ s : ℕ,
        cutoff < s → s ≤ (K o).right.card →
          (K o).right.card * (degreeMax + codegree * s) <
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
      let K := supportedReserveTypicalResidualLinks G (W.U i.succ)
        reserve A I D R d degreeMax codegree omega
      (Fintype.card
          (SimultaneousHallGroupIndex
            {x : V // x ∉ W.U i.succ} V K Delta) : ℝ≥0) *
          (1 - sigma) ^ groupSize +
        (Fintype.card (DistinctPair V) : ℝ≥0) *
          ((((2 : ℝ≥0) ^ (momentOrder * (familyCutoff - 1)) * kappa) ^
              momentOrder) /
            (rootCutoff + 1 : ℝ≥0) ^ momentOrder) +
        ∑ v : V,
          ((ambientTriplesThrough v).powersetCard (caps omega v)).card *
            sigma ^ caps omega v < 1)
    (sideMax : ℕ)
    (hstageTarget : (1 + xi) *
      (p * (W.U i.castSucc).card) ≤ (sideMax : ℝ≥0))
    (hsideLoss : sideMax ≤ loss)
    (hdegreeBudget : ∀ omega, 0 < law.mass omega → ∀ v : V,
      2 * ((triplesThrough (R omega) v).card + caps omega v) ≤
        degreeCutoff)
    (hdeletionScalar : degreeCutoff + rootCutoff * familyCutoff ≤ Delta)
    (alpha : ℝ≥0)
    (hnormalizer : ∀ omega, 0 < law.mass omega →
      let K := supportedReserveTypicalResidualLinks G (W.U i.succ)
        reserve A I D R d degreeMax codegree omega
      sigma /
          (FiniteLaw.independentBits
            (fun _ : SimultaneousLinkPair
                {x : V // x ∉ W.U i.succ} V K ↦ sigma)
            (fun _ ↦ hsigma)).probability
              (IsSimultaneousRobustLinkStarGood
                (absorberErdosForbiddenConfigurationsOn q B)
                (I omega ∪ (D omega ∪ R omega)) (W.U i.succ)
                (outsideVertexEmbedding (W.U i.succ)) K
                (fun o ↦
                  (supportedReserveTypicalResidualLinks_global G
                    (W.U i.succ) reserve A I D R d degreeMax codegree
                    omega).1 o)
                (fun o ↦ o.2)
                (fun o ↦
                  (supportedReserveTypicalResidualLinks_global G
                    (W.U i.succ) reserve A I D R d degreeMax codegree
                    omega).2.2.1 o)
                (fun o ↦
                  (supportedReserveTypicalResidualLinks_global G
                    (W.U i.succ) reserve A I D R d degreeMax codegree
                    omega).2.2.2.1 o)
                (fun o ↦ linkAvailableRelation (K o) (A omega))
                Delta rootCutoff (caps omega)) ≤ alpha) :
    ∃ P : TripleSystemOn V, HasKSSSOutsidePacking q H X B P := by
  let U := W.U i.succ
  let K := supportedReserveTypicalResidualLinks G U reserve A I D R
    d degreeMax codegree
  have hstageDegree : ∀ omega, 0 < law.mass omega →
      ∀ v : V, ((G omega).neighborSet v).ncard ≤ sideMax := by
    intro omega hmass
    exact (htyp omega hmass).neighborSet_ncard_le i hki
      (hGsupp omega hmass) sideMax hstageTarget
  have hcovered : law.SupportedOn fun omega ↦
      ∀ o : {x : V // x ∉ W.U i.succ},
        (coveredGraph (R omega)).degree o.1 ≤ loss := by
    intro omega hmass o
    exact ((htri omega hmass).coveredGraph_degree_le_neighborSet_ncard
      (hstateOld omega hmass).1.2.1 o.1).trans
        ((hstageDegree omega hmass o.1).trans hsideLoss)
  have hreadyOld := htyp.reserveSupportedTypicalResidualLinks_of_typical
    i hki U (by rfl) reserve Kold htri hGsupp hstateOld
      m d degreeMax codegree loss hcovered hh hlower hupper hcodegree
      hbisection
  have hprops := hreadyOld.supportedReserveTypicalResidualLinks
    G U reserve A I D R d degreeMax codegree
  subst X
  exact exists_ksssOutsidePacking_of_supportedTypicalRobustStarFinalStage
    (q := q) (H := H) (X := U) (B := B) (law := law) (G := G)
    (A := A) (I := I) (D := D) (R := R) (K := K) (alpha := alpha)
    caps hA hselected hcover
    (fun omega hmass ↦ (hprops omega hmass).1)
    (fun omega o ↦
      (supportedReserveTypicalResidualLinks_global G U reserve A I D R
        d degreeMax codegree omega).1 o)
    (fun _ o ↦ o.2)
    (fun omega o ↦
      (supportedReserveTypicalResidualLinks_global G U reserve A I D R
        d degreeMax codegree omega).2.2.1 o)
    (fun omega o ↦
      (supportedReserveTypicalResidualLinks_global G U reserve A I D R
        d degreeMax codegree omega).2.2.2.1 o)
    htri hold d degreeMax codegree
    (fun omega hmass ↦ (hprops omega hmass).2.2.2.2.2.2)
    Delta groupSize density candidate cutoff degreeCutoff rootCutoff
    familyCutoff hdensityLe (by simpa only [K, U] using hmixing)
    hdegreeScalar hd hdensityScalar hcandidateScalar sigma hsigma kappa
    momentOrder hfamily hkappa (by simpa only [K, U] using hsmall)
    hpacking havoid hdegreeBudget hdeletionScalar
    (by simpa only [K, U] using hnormalizer)

end

end Erdos207
