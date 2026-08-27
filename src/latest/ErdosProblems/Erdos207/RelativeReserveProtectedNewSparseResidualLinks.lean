/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RelativeReserveProtectedNewSparseRooted
import ErdosProblems.Erdos207.RelativeReserveProtectedSparseResidualLinks

/-! # Actual residual-link bounds for the corrected sparse rooted output -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem RelativeReserveProtectedNewRootedOutput.internalDifferenceLoss
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell n : ℕ}
    {law : FiniteLaw (RelativeReserveProtectedCorrelatedSample Omega V n)}
    {W : Vortex V ell} {next : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V} {i : Fin ell}
    {G : Omega → SimpleGraph V} {A I D : Omega → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool} {d Dint R : ℕ}
    {p reserveDensity C b : ℝ≥0}
    (hout : RelativeReserveProtectedNewRootedOutput law W next F i
      G A I D bits d Dint R p reserveDensity C b) :
    law.SupportedOn fun z ↦
      ∀ o : {x : V // x ∉ W.U i.succ},
        ((coveredGraph
          (relativeReserveProtectedInternalDifference I D z)).neighborFinset
            o.1 ∩ W.U i.succ).card ≤ d := by
  intro z hz o
  let U := W.U i.succ
  let P₀ := relativeReserveProtectedP0 I D (z.1, z.2.1)
  let Q := z.2.2.chosen
  have hraw := hout.outcome z hz
  have hP₀Q : P₀ ⊆ Q := hraw.1.1.initial_subset
  have hpackingAll := (hout.structural z hz).2.2.1
  have hpackingQ : IsPackingOn Q := by
    have h := hpackingAll
    rw [hout.accumulate z hz] at h
    exact h
  let E := preliminaryResidualInternalEdges (G z.1) U P₀
  have houter : ∀ e ∈ E, e.out.1 ∉ U ∧ e.out.2 ∉ U := by
    intro e he
    exact (mem_internalOuterEdges_iff.mp
      (preliminaryResidualInternalEdges_subset_internalOuterEdges
        (G z.1) U P₀ he)).2
  apply card_coveredNeighborsIn_newInternalAdded_le_scheduledIncidence
    (P₀ := P₀) (Q := Q) (E := E)
  · exact hP₀Q
  · exact hpackingQ
  · exact houter
  · simpa only [E, P₀, U, Q, relativeReserveProtectedP0,
      relativeReserveProtectedAint] using hraw.2.2.1
  · simpa only [E, P₀, U] using hout.incidence z hz
  · exact o.2

theorem RelativeReserveProtectedNewSparseRootedOutput.actualResidualLinkBounds
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell n : ℕ}
    {law : FiniteLaw (RelativeReserveProtectedCorrelatedSample Omega V n)}
    {W : Vortex V ell} {next : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V} {i : Fin ell}
    {G : Omega → SimpleGraph V} {A I D : Omega → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool} {dInc Dint R : ℕ}
    {caps : V → ℕ} {dCross mLink DLink CLink : ℕ}
    {p reserveDensity C b : ℝ≥0}
    (hout : RelativeReserveProtectedNewSparseRootedOutput law W next F i
      G A I D bits dInc Dint R caps dCross mLink DLink CLink
      p reserveDensity C b)
    (m : ℕ) (hm : m + dInc ≤ mLink) :
    law.SupportedOn fun z ↦
      ∀ o : {x : V // x ∉ W.U i.succ},
        (∀ x ∈ @residualNeighbors V _ _ (G z.1)
            (Classical.decRel (G z.1).Adj)
            (relativeReserveProtectedTotal I D z.1 z.2) o.1,
          m ≤ (ambientLinkNeighborsIn o.1 (A z.1)
            (@residualNeighbors V _ _ (G z.1)
              (Classical.decRel (G z.1).Adj)
              (relativeReserveProtectedTotal I D z.1 z.2) o.1) x).card) ∧
        (∀ x ∈ @residualNeighbors V _ _ (G z.1)
            (Classical.decRel (G z.1).Adj)
            (relativeReserveProtectedTotal I D z.1 z.2) o.1,
          (ambientLinkNeighborsIn o.1 (A z.1)
            (@residualNeighbors V _ _ (G z.1)
              (Classical.decRel (G z.1).Adj)
              (relativeReserveProtectedTotal I D z.1 z.2) o.1) x).card ≤
            DLink + dCross) ∧
        ∀ x ∈ @residualNeighbors V _ _ (G z.1)
            (Classical.decRel (G z.1).Adj)
            (relativeReserveProtectedTotal I D z.1 z.2) o.1,
          ∀ y ∈ @residualNeighbors V _ _ (G z.1)
            (Classical.decRel (G z.1).Adj)
            (relativeReserveProtectedTotal I D z.1 z.2) o.1,
          x ≠ y →
          (ambientLinkCommonNeighborsIn o.1 (A z.1)
            (@residualNeighbors V _ _ (G z.1)
              (Classical.decRel (G z.1).Adj)
              (relativeReserveProtectedTotal I D z.1 z.2) o.1)
            x y).card ≤ CLink + dCross := by
  intro z hz o
  letI : DecidableRel (G z.1).Adj := Classical.decRel (G z.1).Adj
  let U := W.U i.succ
  let sampled := reserveEdges (G z.1) U (bits z.1)
  let pre := relativeReserveProtectedPreliminaryAdded I D z.1 z.2.1
  let addedInt := relativeReserveProtectedInternalDifference I D z
  let Rtotal := relativeReserveProtectedTotal I D z.1 z.2
  have hlinks := hout.links z hz
  have hresInner : residualNeighbors (G z.1) Rtotal o.1 ⊆ U := by
    intro x hx
    rw [← hlinks.1.1 o |>.2.1] at hx
    rcases mem_union.mp hx with hx | hx
    · exact hlinks.2.2.2.1 o hx
    · exact hlinks.2.2.2.2.1 o hx
  have hpreR : pre ⊆ Rtotal := by
    intro T hT
    change T ∈ relativeReserveProtectedTotal I D z.1 z.2
    rw [relativeReserveProtectedTotal_eq_preliminary_union_internalDifference]
    exact mem_union_left _ hT
  have hextra :
      (protectedResidualSpokeVertices (G z.1) U sampled pre o.1).card ≤
        dCross := by
    have hGPleave : reserveProtectedOuterGraph (G z.1) U sampled ≤
        leaveGraph (I z.1 ∪ D z.1) :=
      (reserveProtectedOuterGraph_le (G z.1) U sampled).trans
        (hout.structural z hz).2.1
    have hinc := hout.residualOuterIncidence z hz o.1
    rw [preliminaryResidualOuterEdges_sdiff_eq_of_le_leaveGraph
      hGPleave] at hinc
    exact (protectedResidualSpokeVertices_card_le_incidence
      (G z.1) U sampled pre o.1 o.2).trans (by
        simpa only [pre, relativeReserveProtectedPreliminaryAdded] using hinc)
  have hloss :
      ((coveredGraph addedInt).neighborFinset o.1 ∩ U).card ≤ dInc := by
    simpa only [addedInt, U] using hout.internalDifferenceLoss z hz o
  have hsample := hout.sampledLinkBounds z hz o.1 o.2
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hxU := hresInner hx
    have hox : (G z.1).Adj o.1 x := (mem_residualNeighbors_iff.mp hx).1
    apply ambientLinkNeighborsIn_residual_card_lower
      (Apre := A z.1) (P := pre) (Q := addedInt)
      (sampled := sampled)
    · exact (hout.structural z hz).1
    · simpa only [pre, sampled, U] using hout.preliminaryProtected z hz
    · simpa only [Rtotal, pre, addedInt] using
        relativeReserveProtectedTotal_eq_preliminary_union_internalDifference
          I D z
    · exact hm.trans (hsample.1 x hxU hox).1
    · exact hloss
  · intro x hx
    have hxU := hresInner hx
    have hox : (G z.1).Adj o.1 x := (mem_residualNeighbors_iff.mp hx).1
    exact ambientLinkNeighborsIn_residual_card_le o.2 hpreR hresInner
      (hsample.1 x hxU hox).2 hextra
  · intro x hx y hy hxy
    have hxU := hresInner hx
    have hyU := hresInner hy
    have hox : (G z.1).Adj o.1 x := (mem_residualNeighbors_iff.mp hx).1
    have hoy : (G z.1).Adj o.1 y := (mem_residualNeighbors_iff.mp hy).1
    exact ambientLinkCommonNeighborsIn_residual_card_le o.2 hpreR hresInner
      (hsample.2 x hxU hox y hyU hoy hxy) hextra

theorem RelativeReserveProtectedNewSparseRootedOutput.exists_typicalResidualLinks
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell n : ℕ}
    {law : FiniteLaw (RelativeReserveProtectedCorrelatedSample Omega V n)}
    {W : Vortex V ell} {next : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V} {i : Fin ell}
    {G : Omega → SimpleGraph V} {A I D : Omega → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool} {dInc Dint Rroot : ℕ}
    {caps : V → ℕ} {dCross mLink DLink CLink : ℕ}
    {p reserveDensity C b : ℝ≥0}
    (hout : RelativeReserveProtectedNewSparseRootedOutput law W next F i
      G A I D bits dInc Dint Rroot caps dCross mLink DLink CLink
      p reserveDensity C b)
    (m dLink : ℕ) (hm : m + dInc ≤ mLink)
    (hbisection : ∀ z, 0 < law.mass z →
      ∀ o : {x : V // x ∉ W.U i.succ},
      ((@residualNeighbors V _ _ (G z.1)
          (Classical.decRel (G z.1).Adj)
          (relativeReserveProtectedTotal I D z.1 z.2) o.1).card : ℝ≥0) *
        (2 * (2 : ℝ≥0) ^ dLink * (3 / 4 : ℝ≥0) ^
          (m - 2 * dLink)) < 1) :
    law.SupportedOn fun z ↦
      ∃ Knew : {x : V // x ∉ W.U i.succ} → BipartiteLink V,
        IsIntermediateLinkState (G z.1) (W.U i.succ) (A z.1)
          (I z.1) (D z.1)
          (relativeReserveProtectedTotal I D z.1 z.2) Knew ∧
        (∀ o, (Knew o).center = outsideVertexEmbedding (W.U i.succ) o) ∧
        (∀ o, outsideVertexEmbedding (W.U i.succ) o ∉ W.U i.succ) ∧
        (∀ o, (Knew o).left ⊆ W.U i.succ) ∧
        (∀ o, (Knew o).right ⊆ W.U i.succ) ∧
        (∀ o, (Knew o).SpokesIn
          (relativeReserveProtectedRootedReserve W i G bits I D z)) ∧
        ∀ o, HasLinkDegreeCodegreeBounds (A z.1) (Knew o)
          dLink (DLink + dCross) (CLink + dCross) := by
  intro z hz
  have hb := hout.actualResidualLinkBounds m hm z hz
  have hold := hout.links z hz
  exact exists_reserveSupportedTypicalResidualLinks_of_bounds
    (relativeReserveProtectedRootedLinks W i F G A I D bits z)
    hold.1 hold.2.2.2.1 hold.2.2.2.2.1 hold.2.2.2.2.2
    m dLink (DLink + dCross) (CLink + dCross)
    (fun o ↦ (hb o).1) (fun o ↦ (hb o).2.1)
    (fun o ↦ (hb o).2.2) (hbisection z hz)

end

end Erdos207
