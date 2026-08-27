/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SharpSupportedRobustFinalStage
import ErdosProblems.Erdos207.SupportedTerminalResidualReady

/-! # Terminal extraction from ready residual links with exact Hall tails -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem exists_ksssOutsidePacking_of_supportedResidualLinksReady_sharp
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {law : FiniteLaw Omega} {W : Vortex V ell} (i : Fin ell)
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V}
    {G : Omega → SimpleGraph V}
    {A I D R : Omega → TripleSystemOn V}
    {reserve : Omega → Finset (Sym2 V)}
    (d degreeMax codegree : ℕ)
    (hX : X = W.U i.succ)
    (hA : law.SupportedOn fun omega ↦
      A omega ⊆ outsideAvailableTriangles H B)
    (hselected : law.SupportedOn fun omega ↦
      I omega ∪ D omega ⊆ outsideAvailableTriangles H B)
    (hcover : law.SupportedOn fun omega ↦
      CoversOriginalGraph
        (graphDifference (SimpleGraph.completeGraph V) H)
        (G omega) (I omega) (D omega))
    (hready : law.SupportedOn fun omega ↦
      HasReserveSupportedTypicalResidualLinks
        (G omega) (W.U i.succ) (reserve omega) (A omega)
        (I omega) (D omega) (R omega) d degreeMax codegree)
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
      let K := supportedReserveTypicalResidualLinks G (W.U i.succ)
        reserve A I D R d degreeMax codegree omega
      (∑ o : {x : V // x ∉ W.U i.succ},
        ∑ h : OrientedSmallHallObstruction
            ↥(K o).left ↥(K o).right,
          (1 - sigma / 2) ^
              (orientedSmallHallCandidates
                (linkAvailableRelation (K o) (A omega)) h).card /
            (1 / 2 : ℝ≥0) ^ (Delta * orientedSmallHallSize h)) +
        (Fintype.card (DistinctPair V) : ℝ≥0) *
          ((((2 : ℝ≥0) ^ (momentOrder * (familyCutoff - 1)) * kappa) ^
              momentOrder) /
            (rootCutoff + 1 : ℝ≥0) ^ momentOrder) < 1)
    (hpacking : law.SupportedOn fun omega ↦
      IsPackingOn (I omega ∪ (D omega ∪ R omega)))
    (havoid : law.SupportedOn fun omega ↦
      AvoidsForbidden (I omega ∪ (D omega ∪ R omega))
        (absorberErdosForbiddenConfigurationsOn q B))
    (sideMax : ℕ)
    (hstageDegree : ∀ omega, 0 < law.mass omega →
      ∀ v : V, ((G omega).neighborSet v).ncard ≤ sideMax)
    (hdegreeCutoff : sideMax + sideMax ≤ degreeCutoff)
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
              (IsSimultaneousRobustLinkGood
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
                Delta rootCutoff) ≤ alpha) :
    ∃ P : TripleSystemOn V, HasKSSSOutsidePacking q H X B P := by
  let U := W.U i.succ
  let K := supportedReserveTypicalResidualLinks G U reserve A I D R
    d degreeMax codegree
  have hprops := hready.supportedReserveTypicalResidualLinks
    G U reserve A I D R d degreeMax codegree
  subst X
  apply exists_ksssOutsidePacking_of_supportedRobustFinalStage_sharp
    (q := q) (H := H) (X := U) (B := B) (law := law) (G := G)
    (A := A) (I := I) (D := D) (R := R) (K := K) (alpha := alpha)
    hA hselected hcover
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
    htri hold Delta degreeCutoff rootCutoff familyCutoff sigma hsigma
    kappa momentOrder hfamily hkappa
    (by simpa only [K, U] using hsmall) hpacking havoid sideMax
    hstageDegree hdegreeCutoff hdeletionScalar
    (by simpa only [K, U] using hnormalizer)

end

end Erdos207
