/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveProtectedAugmentedReserveLaw
import ErdosProblems.Erdos207.PreliminaryResidualInternalFixedReserveComposition
import ErdosProblems.Erdos207.ReserveProtectedPreliminaryGeometry

/-!
# Reserve-protected preliminary/internal composition

This file is the law-level form of the KSSS ordering: expose the crossing
reserve, run the preliminary process without using any sampled reserve edge,
then use those exact same bits to cover the residual internal edges.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- A reserve-protected preliminary kernel followed by the fixed-reserve raw
internal kernel preserves the augmented-reserve strong law. -/
theorem IsReserveStronglyWellDistributed.jointBind_reserveProtectedPreliminary_fixedInternal
    {Omega Xi V : Type*} [Fintype Omega] [Fintype Xi] [Fintype V]
    [DecidableEq Omega] [DecidableEq Xi] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {Kpre : Omega → FiniteLaw Xi}
    {W : Vortex V ell} {level mid final : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V} {A P : Omega → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool}
    {p reserveDensity C b pMid reserveDensityMid CMid bMid
      pFinal CFinal bFinal alpha eta epsilonPre : ℝ≥0}
    (i : Fin ell)
    (hstrong : IsReserveStronglyWellDistributed L W level P
      (fun _ ↦ ∅) (fun omega ↦
        reserveEdges (G omega) (W.U i.succ) (bits omega))
      p reserveDensity C b)
    (Mstar : Omega → Xi → TripleSystemOn V)
    (hpreliminary : ∀ omega, 0 < L.mass omega → ∀ Q E,
      (Kpre omega).probability (fun xi ↦
        Q ⊆ Mstar omega xi ∧
        E ⊆ preliminaryResidualCrossingEdges (G omega) (W.U i.succ)
          (Mstar omega xi) \
            reserveEdges (G omega) (W.U i.succ) (bits omega)) ≤
        alpha ^ Q.card * eta ^ E.card + epsilonPre)
    (hnonempty : ∀ j, (W.U j).Nonempty)
    (hlevelMid : level ≤ mid) (hCCMid : C ≤ CMid)
    (hCMid : 1 ≤ CMid) (hpMid : p ≤ pMid) (hpOne : p ≤ 1)
    (hreserveMono : reserveDensity ≤ reserveDensityMid)
    (hreserveOne : reserveDensity ≤ 1)
    (halpha : alpha ≤ 1) (hetaOne : eta ≤ 1)
    (hetaReserve : eta ≤ reserveDensityMid)
    (hbOne : b ≤ 1) (herrorPre : b + 2 * epsilonPre ≤ bMid)
    (hnewPre : ∀ Q : TripleOn V,
      alpha ≤ pMid /
        ((W.U (W.truncatedLevel mid Q)).card : ℝ≥0))
    (Good : Omega × Xi → Prop)
    (hgoodSupport : (L.jointBind Kpre).SupportedOn Good)
    (htri : ∀ z, Good z → ConsistsOfTriangles (G z.1) (A z.1))
    (hold : ∀ z, Good z → G z.1 ≤ leaveGraph (P z.1))
    (hMprotected : ∀ z, Good z → Mstar z.1 z.2 ⊆
      reserveProtectedAvailable
        (reserveEdges (G z.1) (W.U i.succ) (bits z.1)) (A z.1))
    (hpacking : ∀ z, Good z →
      IsPackingOn (P z.1 ∪ Mstar z.1 z.2))
    (havoid : ∀ z, Good z →
      AvoidsForbidden (P z.1 ∪ Mstar z.1 z.2) F)
    (a D d R q : ℕ) (hD : 0 < D)
    (hsupply : ∀ z, Good z → ∀ e ∈
      internalOuterEdges (G z.1) (W.U i.succ),
      a + D ≤ (activeReserveWedgeVertices (G z.1) (W.U i.succ)
        (iterationExtensionVertices (A z.1)
          (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ))
        e.out.1 e.out.2 (bits z.1)).card)
    (hfamily : ∀ S ∈ F, S.card ≤ q)
    (hincidence : ∀ z, Good z → ∀ v : V,
      (scheduledEdgesAt
        (preliminaryResidualInternalEdges (G z.1) (W.U i.succ)
          (P z.1 ∪ Mstar z.1 z.2)) v).card ≤ d)
    (hscalar : 4 * d + R * q ≤ a)
    (hmidFinal : mid ≤ final) (hCFinal : 2 * CMid ≤ CFinal)
    (hCFinalOne : 1 ≤ CFinal) (hpFinal : pMid ≤ pFinal)
    (hfactor : (D : ℝ≥0)⁻¹ ≤ 1) (hbFinal : bMid ≤ bFinal)
    (hnewInternal : ∀ T : TripleOn V,
      (D : ℝ≥0)⁻¹ ≤
        pFinal / ((W.U (W.truncatedLevel final T)).card : ℝ≥0)) :
    let LP := L.jointBind Kpre
    let P0 : Omega × Xi → TripleSystemOn V := fun z ↦
      P z.1 ∪ Mstar z.1 z.2
    let Aint : Omega × Xi → TripleSystemOn V := fun z ↦
      pairSafeAvailable (A z.1) (P0 z)
    let Gpre : Omega × Xi → SimpleGraph V := fun z ↦ G z.1
    let bitsPre : Omega × Xi → Sym2 V → Bool := fun z ↦ bits z.1
    let Kint := rawResidualInternalKernel W i F Gpre Aint P0 bitsPre D
    let reservePre : Omega × Xi → Finset (Sym2 V) := fun z ↦
      preliminaryAugmentedReserve (G z.1) (W.U i.succ)
        (reserveEdges (G z.1) (W.U i.succ) (bits z.1))
        (Mstar z.1 z.2)
    IsReserveStronglyWellDistributed (LP.jointBind Kint) W final
        (jointInitial (jointInitial P))
        (jointLater (jointLater (fun _ ↦ ∅) Mstar)
          (rawResidualInternalAdded P0))
        (fun z ↦ reservePre z.1) pFinal reserveDensityMid
        (2 * CFinal) bFinal ∧
      (LP.jointBind Kint).SupportedOn (fun z ↦
        Good z.1 ∧
          RawResidualInternalOutcomeGood W i F Gpre Aint P0 bitsPre
            D R z.1 z.2) := by
  dsimp only
  let LP := L.jointBind Kpre
  let P0 : Omega × Xi → TripleSystemOn V := fun z ↦
    P z.1 ∪ Mstar z.1 z.2
  let Aint : Omega × Xi → TripleSystemOn V := fun z ↦
    pairSafeAvailable (A z.1) (P0 z)
  let Gpre : Omega × Xi → SimpleGraph V := fun z ↦ G z.1
  let bitsPre : Omega × Xi → Sym2 V → Bool := fun z ↦ bits z.1
  let reservePre : Omega × Xi → Finset (Sym2 V) := fun z ↦
    preliminaryAugmentedReserve (G z.1) (W.U i.succ)
      (reserveEdges (G z.1) (W.U i.succ) (bits z.1))
      (Mstar z.1 z.2)
  have hpreStrong : IsReserveStronglyWellDistributed LP W mid
      (jointInitial P) (jointLater (fun _ ↦ ∅) Mstar) reservePre
      pMid reserveDensityMid (2 * CMid) bMid := by
    exact hstrong.jointBind_preliminaryAugmentedReserve_sdiff_of_numeric_supported
      Mstar hpreliminary hnonempty hlevelMid hCCMid hCMid hpMid hpOne
      hreserveMono hreserveOne halpha hetaOne hetaReserve hbOne herrorPre
      hnewPre
  have htriInt : ∀ z, Good z →
      ConsistsOfTriangles (Gpre z) (Aint z) := by
    intro z hz
    exact (htri z hz).pairSafeAvailable
  have hinitialInt : ∀ z, Good z → ∀ T ∈ Aint z,
      TriangleAvoidsGraph (coveredGraph (P0 z)) T := by
    intro z _hz T hT
    exact pairSafeAvailable_triangleAvoids (A z.1) (P0 z) T hT
  have hsupplyInt : ∀ z, Good z →
      let E := preliminaryResidualInternalEdges
        (Gpre z) (W.U i.succ) (P0 z)
      ∀ e ∈ E,
        a + D ≤ (activeReserveWedgeVertices (Gpre z) (W.U i.succ)
          (residualInternalExtensionSet W i (Aint z) e)
          e.out.1 e.out.2 (bitsPre z)).card := by
    intro z hz
    dsimp only [Gpre, P0]
    intro e he
    have heInternal : e ∈ internalOuterEdges (G z.1) (W.U i.succ) :=
      preliminaryResidualInternalEdges_subset_internalOuterEdges
        (G z.1) (W.U i.succ) (P0 z) he
    have hbase := hsupply z hz e heInternal
    have hmono := card_activeReserveWedgeVertices_pairSafe_ge
      (A := A z.1) (P := P z.1) (M := Mstar z.1 z.2)
      (bits := bits z.1) he (hold z hz) (hMprotected z hz)
    exact hbase.trans (by
      simpa only [Gpre, Aint, P0, bitsPre, residualInternalExtensionSet]
        using hmono)
  have hkernel := rawResidualInternalKernel_of_fixedReserveSupply
    Good htriInt i (fun z hz ↦ hpacking z hz)
      (fun z hz ↦ havoid z hz) hinitialInt bitsPre
      a D d R q hD hsupplyInt hfamily
      (fun z hz v ↦ by
        simpa only [Gpre, P0] using hincidence z hz v)
      hscalar
  let Kint := rawResidualInternalKernel W i F Gpre Aint P0 bitsPre D
  have hcomposed := hpreStrong.jointBind_rawResidualInternalKernel_of_fixedReserve
    Good hgoodSupport hkernel.1 hkernel.2 hnonempty hmidFinal hCFinal
      hCFinalOne hpFinal hfactor hbFinal hnewInternal
  simpa only [LP, P0, Aint, Gpre, bitsPre, Kint, reservePre] using hcomposed

end

end Erdos207
