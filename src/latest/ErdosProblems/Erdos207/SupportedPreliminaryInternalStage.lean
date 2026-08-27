/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SupportedConditionedPreliminaryKernel
import ErdosProblems.Erdos207.PreliminaryAugmentedReserveNumeric
import ErdosProblems.Erdos207.ConditionedExistingReserveInternalUpdate
import ErdosProblems.Erdos207.PreliminaryInternalResidualLinks

/-!
# Support-aware preliminary and internal stage composition

This file binds a support-restricted preliminary kernel to an existing
reserve-aware master law, conditions on readiness of the sharp internal-edge
kernel, and constructs the canonical residual links.  It is the complete
first two-thirds of one KSSS master step.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- A support-sensitive preliminary update followed by conditioned sharp
internal cover yields both the reserve-aware law required by the link step
and all residual-link structural certificates. -/
theorem IsReserveStronglyWellDistributed.bind_supportedPreliminary_internal_residualLinks
    {Omega Xi V : Type*} [Fintype Omega] [Fintype Xi] [Fintype V]
    [DecidableEq Omega] [DecidableEq Xi] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {Kpre : Omega → FiniteLaw Xi}
    {W : Vortex V ell} {k mid final : Fin (ell + 1)}
    {G : Omega → SimpleGraph V} {U : Finset V}
    {A Iold Dold : Omega → TripleSystemOn V}
    {sampled : Omega → Finset (Sym2 V)}
    {bits : Omega → Sym2 V → Bool}
    {p reserveDensity C b pMid reserveDensityMid CMid bMid
      pFinal CFinal bFinal alpha eta epsilonPre epsilonInt : ℝ≥0}
    (hstrong : IsReserveStronglyWellDistributed L W k Iold Dold sampled
      p reserveDensity C b)
    (addedPre : Omega → Xi → TripleSystemOn V)
    (hpreliminary : ∀ omega, 0 < L.mass omega → ∀ Q E,
      (Kpre omega).probability (fun xi ↦
        Q ⊆ addedPre omega xi ∧
        E ⊆ preliminaryResidualCrossingEdges (G omega) U
          (addedPre omega xi)) ≤
        alpha ^ Q.card * eta ^ E.card + epsilonPre)
    (hnonempty : ∀ j, (W.U j).Nonempty)
    (hkMid : k ≤ mid) (hCCMid : C ≤ CMid) (hCMid : 1 ≤ CMid)
    (hpMid : p ≤ pMid) (hpOne : p ≤ 1)
    (hreserveMono : reserveDensity ≤ reserveDensityMid)
    (hreserveOne : reserveDensity ≤ 1)
    (halpha : alpha ≤ 1) (hetaOne : eta ≤ 1)
    (hetaReserve : eta ≤ reserveDensityMid)
    (hbOne : b ≤ 1) (herrorPre : b + 2 * epsilonPre ≤ bMid)
    (hnewPre : ∀ Q : TripleOn V,
      alpha ≤ pMid /
        ((W.U (W.truncatedLevel mid Q)).card : ℝ≥0))
    (F : ForbiddenFamilyOn V) (i : Fin ell)
    (hU : U = W.U i.succ)
    (a Dint horizon : ℕ) (hDint : 0 < Dint)
    (hbadInternal :
      (L.jointBind Kpre).probability (fun z ↦
        ¬ InternalOuterKernelReady W i F (G z.1) (A z.1)
          (Iold z.1 ∪ (Dold z.1 ∪ addedPre z.1 z.2))
          (bits z.1) a Dint) ≤ epsilonInt)
    (hepsilonInt : epsilonInt < 1)
    (horizonBound : ∀ z : Omega × Xi,
      (internalOuterEdges (G z.1) (W.U i.succ)).card ≤ horizon)
    (hMidFinal : mid ≤ final)
    (hCFinal : (2 * CMid) / (1 - epsilonInt) ≤ CFinal)
    (hCFinalOne : 1 ≤ CFinal) (hpFinal : pMid ≤ pFinal)
    (hfactor : (Dint : ℝ≥0)⁻¹ ≤ 1) (hbFinal : bMid ≤ bFinal)
    (hnewInternal : ∀ Q : TripleOn V,
      (Dint : ℝ≥0)⁻¹ ≤ pFinal /
        ((W.U (W.truncatedLevel final Q)).card : ℝ≥0))
    (hbase : (L.jointBind Kpre).SupportedOn fun z ↦
      (∀ v, Even ((neighborsIn (G z.1) univ v).card)) ∧
      G z.1 ≤ leaveGraph (Iold z.1 ∪ Dold z.1) ∧
      ConsistsOfTriangles (G z.1) (A z.1) ∧
      addedPre z.1 z.2 ⊆ A z.1 ∧
      Disjoint (Iold z.1) (Dold z.1 ∪ addedPre z.1 z.2) ∧
      IsPackingOn
        (Iold z.1 ∪ (Dold z.1 ∪ addedPre z.1 z.2)))
    (hbaseAvoid : (L.jointBind Kpre).SupportedOn fun z ↦
      AvoidsForbidden
        (Iold z.1 ∪ (Dold z.1 ∪ addedPre z.1 z.2)) F) :
    let LP := L.jointBind Kpre
    let Ready : Omega × Xi → Prop := fun z ↦
      InternalOuterKernelReady W i F (G z.1) (A z.1)
        (Iold z.1 ∪ (Dold z.1 ∪ addedPre z.1 z.2))
        (bits z.1) a Dint
    ∃ hpos : 0 < LP.probability Ready,
      let Lc := LP.conditionOn Ready hpos
      let P0 : Omega × Xi → TripleSystemOn V := fun z ↦
        Iold z.1 ∪ (Dold z.1 ∪ addedPre z.1 z.2)
      let Kint : Omega × Xi → FiniteLaw (InternalEdgeGreedyStateOn V) :=
        supportedInternalOuterEdgeKernel W i F
          (fun z ↦ G z.1) (fun z ↦ A z.1) P0 (fun z ↦ bits z.1)
          a Dint
      let Lint := Lc.jointBind Kint
      let reservePre : Omega × Xi → Finset (Sym2 V) := fun z ↦
        preliminaryAugmentedReserve (G z.1) U (sampled z.1)
          (addedPre z.1 z.2)
      let R : (Omega × Xi) × InternalEdgeGreedyStateOn V →
          TripleSystemOn V := fun z ↦
        internalStageFamily (Iold z.1.1) (Dold z.1.1)
          (addedPre z.1.1 z.1.2) z.2.chosen
      let links := internalOutcomeResidualLinks
        (fun z : (Omega × Xi) × InternalEdgeGreedyStateOn V ↦ G z.1.1)
        U (fun z ↦ reservePre z.1) F
        (fun z ↦ A z.1.1) (fun z ↦ Iold z.1.1)
        (fun z ↦ Dold z.1.1) (fun z ↦ addedPre z.1.1 z.1.2)
        (fun z ↦ z.2.chosen)
      IsReserveStronglyWellDistributed Lint W final
          (fun z ↦ Iold z.1.1)
          (fun z ↦ Dold z.1.1 ∪ R z)
          (fun z ↦ reservePre z.1) pFinal reserveDensityMid
          (2 * CFinal) bFinal ∧
        Lint.SupportedOn (fun z ↦
          IsIntermediateLinkState (G z.1.1) U (A z.1.1)
              (Iold z.1.1) (Dold z.1.1) (R z) (links z) ∧
            (∀ o, (links z o).center = outsideVertexEmbedding U o) ∧
            (∀ o, outsideVertexEmbedding U o ∉ U) ∧
            (∀ o, (links z o).left ⊆ U) ∧
            (∀ o, (links z o).right ⊆ U) ∧
            (∀ o, (links z o).SpokesIn (reservePre z.1))) ∧
        Lint.SupportedOn (fun z ↦
          ConsistsOfTriangles (G z.1.1) (A z.1.1) ∧
            G z.1.1 ≤ leaveGraph (Iold z.1.1 ∪ Dold z.1.1) ∧
            IsPackingOn
              (Iold z.1.1 ∪ (Dold z.1.1 ∪ R z)) ∧
            AvoidsForbidden
              (Iold z.1.1 ∪ (Dold z.1.1 ∪ R z)) F) ∧
        1 - epsilonInt ≤ LP.probability Ready := by
  dsimp only
  subst U
  let LP := L.jointBind Kpre
  let reservePre : Omega × Xi → Finset (Sym2 V) := fun z ↦
    preliminaryAugmentedReserve (G z.1) (W.U i.succ) (sampled z.1)
      (addedPre z.1 z.2)
  have hreservePre : IsReserveStronglyWellDistributed LP W mid
      (jointInitial Iold) (jointLater Dold addedPre) reservePre
      pMid reserveDensityMid (2 * CMid) bMid := by
    exact hstrong.jointBind_preliminaryAugmentedReserve_of_numeric_supported
      addedPre hpreliminary hnonempty hkMid hCCMid hCMid hpMid hpOne
      hreserveMono hreserveOne halpha hetaOne hetaReserve hbOne herrorPre
      hnewPre
  let P0 : Omega × Xi → TripleSystemOn V := fun z ↦
    Iold z.1 ∪ (Dold z.1 ∪ addedPre z.1 z.2)
  let Ready : Omega × Xi → Prop := fun z ↦
    InternalOuterKernelReady W i F (G z.1) (A z.1) (P0 z)
      (bits z.1) a Dint
  obtain ⟨hpos, hupdate⟩ :=
    hreservePre.conditionInternalOuterEdgeKernel
      (G := fun z : Omega × Xi ↦ G z.1)
      (A := fun z : Omega × Xi ↦ A z.1) (P0 := P0)
      (bits := fun z : Omega × Xi ↦ bits z.1)
      i a Dint horizon hDint hbadInternal hepsilonInt horizonBound
      hnonempty hMidFinal hCFinal hCFinalOne hpFinal hfactor hbFinal
      hnewInternal
  refine ⟨hpos, ?_⟩
  let Lc := LP.conditionOn Ready hpos
  let Kint : Omega × Xi → FiniteLaw (InternalEdgeGreedyStateOn V) :=
    supportedInternalOuterEdgeKernel W i F
      (fun z ↦ G z.1) (fun z ↦ A z.1) P0 (fun z ↦ bits z.1)
      a Dint
  let Lint := Lc.jointBind Kint
  let R : (Omega × Xi) × InternalEdgeGreedyStateOn V →
      TripleSystemOn V := fun z ↦
    internalStageFamily (Iold z.1.1) (Dold z.1.1)
      (addedPre z.1.1 z.1.2) z.2.chosen
  let links := internalOutcomeResidualLinks
    (fun z : (Omega × Xi) × InternalEdgeGreedyStateOn V ↦ G z.1.1)
    (W.U i.succ) (fun z ↦ reservePre z.1) F
    (fun z ↦ A z.1.1) (fun z ↦ Iold z.1.1)
    (fun z ↦ Dold z.1.1) (fun z ↦ addedPre z.1.1 z.1.2)
    (fun z ↦ z.2.chosen)
  have hreserveFinal : IsReserveStronglyWellDistributed Lint W final
      (fun z ↦ Iold z.1.1) (fun z ↦ Dold z.1.1 ∪ R z)
      (fun z ↦ reservePre z.1) pFinal reserveDensityMid
      (2 * CFinal) bFinal := by
    have hlater :
        jointLater (jointLater Dold addedPre)
            (supportedInternalOuterEdgeAdded P0) =
          (fun z : (Omega × Xi) × InternalEdgeGreedyStateOn V ↦
            Dold z.1.1 ∪ R z) := by
      funext z
      simp only [jointLater, R, internalStageFamily,
        supportedInternalOuterEdgeAdded, P0]
      rw [union_assoc]
    have hdist := hupdate.1
    rw [hlater] at hdist
    have hinitial : jointInitial (jointInitial Iold) =
        (fun z : (Omega × Xi) × InternalEdgeGreedyStateOn V ↦
          Iold z.1.1) := rfl
    rw [hinitial] at hdist
    simpa only [Lint, Lc, LP, Ready, Kint, P0, reservePre] using hdist
  have hbaseConditioned := hbase.conditionOn hpos
  have hbaseAvoidConditioned := hbaseAvoid.conditionOn hpos
  have hlinks :=
    hbaseConditioned.preliminaryInternalResidualLinks
      (K := Kint) (sampled := fun z : Omega × Xi ↦ sampled z.1)
      (G := fun z : Omega × Xi ↦ G z.1)
      (A := fun z : Omega × Xi ↦ A z.1)
      (I := fun z : Omega × Xi ↦ Iold z.1)
      (D := fun z : Omega × Xi ↦ Dold z.1)
      (Mstar := fun z : Omega × Xi ↦ addedPre z.1 z.2)
      (P0 := P0) (Q := fun z w ↦ w.chosen)
      (fun z ↦ rfl) hupdate.2.1
  refine ⟨hreserveFinal, ?_, ?_, hupdate.2.2⟩
  · simpa only [Lint, Lc, LP, Ready, Kint, P0, reservePre, R, links] using
      hlinks
  · intro z hz
    have hmasses :=
      (FiniteLaw.jointBind_mass_pos_iff Lc Kint z.1 z.2).mp hz
    have hpre := hbaseConditioned z.1 hmasses.1
    have hpreAvoid := hbaseAvoidConditioned z.1 hmasses.1
    have hreach := (hupdate.2.1 z hz).1
    have hsubset := hreach.initial_subset
    have hunion :
        Iold z.1.1 ∪ (Dold z.1.1 ∪ R z) = z.2.chosen := by
      calc
        Iold z.1.1 ∪ (Dold z.1.1 ∪ R z) =
            (Iold z.1.1 ∪
                (Dold z.1.1 ∪ addedPre z.1.1 z.1.2)) ∪
              (z.2.chosen \ (Iold z.1.1 ∪
                (Dold z.1.1 ∪ addedPre z.1.1 z.1.2))) := by
                  ext T
                  simp only [R, internalStageFamily, mem_union, mem_sdiff]
                  aesop
        _ = z.2.chosen := union_sdiff_of_subset hsubset
    rw [hunion]
    exact ⟨hpre.2.2.1, hpre.2.1,
      hreach.isPacking hpre.2.2.2.2.2,
      hreach.avoidsForbidden hpreAvoid⟩

end

end Erdos207
