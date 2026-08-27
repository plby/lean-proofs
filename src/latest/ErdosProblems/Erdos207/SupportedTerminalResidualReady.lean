/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SupportedTerminalTypicalPipeline

/-!
# Terminal extraction from supportwise-ready residual links

This interface separates the residual-link rechoice (including its localized
loss estimate) from the robust simultaneous matching and final master-cover
extraction.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Once the totalized typical residual links are known to be genuine on the
support of the intermediate law, the remaining robust-Hall and deletion
scalars give the exact outside packing. -/
theorem exists_ksssOutsidePacking_of_supportedResidualLinksReady
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
  exact exists_ksssOutsidePacking_of_supportedTypicalRobustFinalStage
    (q := q) (H := H) (X := U) (B := B) (law := law) (G := G)
    (A := A) (I := I) (D := D) (R := R) (K := K) (alpha := alpha)
    (hA := hA) (hselected := hselected) (hcover := hcover)
    (hstate := fun omega hmass ↦ (hprops omega hmass).1)
    (hcenter := fun omega o ↦
      (supportedReserveTypicalResidualLinks_global G U reserve A I D R
        d degreeMax codegree omega).1 o)
    (hout := fun _ o ↦ o.2)
    (hleft := fun omega o ↦
      (supportedReserveTypicalResidualLinks_global G U reserve A I D R
        d degreeMax codegree omega).2.2.1 o)
    (hright := fun omega o ↦
      (supportedReserveTypicalResidualLinks_global G U reserve A I D R
        d degreeMax codegree omega).2.2.2.1 o)
    (htri := htri) (hold := hold) d degreeMax codegree
    (fun omega hmass ↦ (hprops omega hmass).2.2.2.2.2.2)
    Delta groupSize density candidate cutoff degreeCutoff rootCutoff
    familyCutoff hdensityLe (by simpa only [K, U] using hmixing)
    hdegreeScalar hd hdensityScalar hcandidateScalar sigma hsigma kappa
    momentOrder hfamily hkappa (by simpa only [K, U] using hsmall)
    hpacking havoid sideMax hstageDegree hdegreeCutoff hdeletionScalar
    (by simpa only [K, U] using hnormalizer)

end

end Erdos207
