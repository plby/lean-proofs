/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeNativeWholeOwnerSurvivorAdvance

/-!
# Target completion of the native whole-owner residual block

The nonsurviving terminal block is `kappa`-bounded and lies on the source
frontier of the old captured stage web.  The corrected current-cardinal
extension contract therefore gives one simultaneous linkage from this
block to the original target.  Lifting it to the ambient web has an exact
old-roof incidence: it meets that roof precisely in its prescribed source
set.  Consequently it is star-compatible with the normalized old row.

This file deliberately does not union that target linkage with the survivor
interval family.  Their carriers beyond the old roof can still meet; a
joint component exchange or protected selection is needed for that step.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder
open _root_.Erdos599.CardinalInduction
open ColouredSafeMovingStages

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {seed : Set V} {z : V} {R : LimitClosure C seed}

namespace NativePostClosureIntervalTransaction

/-- The residual terminals are genuine sources of the old captured stage
web. -/
theorem nativeWholeOwnerNonsurvivingTerminals_subset_oldFrontier
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed') :
    T.nativeWholeOwnerNonsurvivingTerminals R' ⊆
      C.ladder.frontier R.later.stage := by
  intro t ht
  exact T.nativeWholeOwnerInterval_isLinkageBetween.terminalFrontier_subset
    ht.1

/-- A linkage lifted out of the old captured stage web meets its complete
old roof exactly in its prescribed stage sources. -/
theorem vertexSet_liftResidualStageFamily_inter_oldRoof
    {A : Set V} {P : Set (C.ladder.stageWeb R.later.stage).DPath}
    (hA : A ⊆ C.ladder.frontier R.later.stage)
    (hP : IsLinkageBetween (C.ladder.stageWeb R.later.stage) A
      (C.ladder.stageWeb R.later.stage).target P) :
    Gamma.vertexSet
        (SliceSegmentCore.liftStageFamily C.ladder R.later.stage P) ∩
      (nativeCapturedGeometry R).outerRoof = A := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨q, hq, hxq⟩, hxRoof⟩
    rw [SliceSegmentCore.mem_liftStageFamily] at hq
    obtain ⟨r, hrP, rfl⟩ := hq
    have hxeq : x = r.initial := by
      by_contra hxne
      have hxRawRoof : x ∈ Gamma.roof
          (Gamma.terminalFrontier (C.ladder.warpAt R.later.stage)) := by
        rw [← Gamma.roof_essential,
          ← C.ladder.frontier_eq_essential_terminalFrontier
            C.legal.roofsSourceAtStages R.later.stage]
        exact hxRoof
      exact (C.ladder.liftStagePath_not_mem_roof_of_ne_initial
        R.later.stage r hxq hxne) hxRawRoof
    rw [hxeq, ← hP.initialSet_eq]
    exact ⟨r, hrP, rfl⟩
  · intro x hxA
    have hxInitial : x ∈
        (C.ladder.stageWeb R.later.stage).initialSet P :=
      hP.initialSet_eq.symm ▸ hxA
    obtain ⟨p, hpP, hpInitial⟩ := hxInitial
    refine ⟨?_, Gamma.subset_roof (C.ladder.frontier R.later.stage) ?_⟩
    · refine ⟨C.ladder.liftStagePath R.later.stage p, ?_, ?_⟩
      · rw [SliceSegmentCore.mem_liftStageFamily]
        exact ⟨p, hpP, rfl⟩
      · rw [C.ladder.support_liftStagePath, ← hpInitial]
        exact p.initial_mem_support
    · exact hA hxA

/-- Corrected current-cardinal extension in the literal old captured stage
web supplies a simultaneous target linkage for every residual terminal. -/
theorem exists_nativeWholeOwnerResidualStageTargetLinkage
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage)
    (hext :
      _root_.Erdos599.CardinalInduction.ProtectedCardinalAssembly.ExtensionThroughFor
        Gamma kappa) :
    ∃ P : Set (C.ladder.stageWeb R.later.stage).DPath,
      IsLinkageBetween (C.ladder.stageWeb R.later.stage)
        (T.nativeWholeOwnerNonsurvivingTerminals R')
        (C.ladder.stageWeb R.later.stage).target P := by
  let G := C.ladder.stageWeb R.later.stage
  let A := T.nativeWholeOwnerNonsurvivingTerminals R'
  have hNorm : G.IsNormalized :=
    RegularCandidateProvider.stageWeb_isNormalized
      C.normalized C.ladder R.later.stage
  have hG : G.IsUnhindered := by
    exact (nativeCapturedGeometry R).newStage_isUnhindered
  have hA : A ⊆ G.source := by
    change A ⊆ C.ladder.frontier R.later.stage
    exact T.nativeWholeOwnerNonsurvivingTerminals_subset_oldFrontier R'
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  have hSub : (G.sourceSubweb A).IsUnhindered :=
    hG.sourceSubweb G hNoEnter hA
  have hSubBase : ∀ {x y : V},
      (G.sourceSubweb A).graph.Adj x y → Gamma.graph.Adj x y := by
    intro x y hxy
    exact Gamma.quotient_adj_imp hxy.1
  have hsourceCard : #(G.sourceSubweb A).source ≤ kappa := by
    simpa only [DWeb.sourceSubweb_source] using
      T.nativeWholeOwnerNonsurvivingTerminals_card_le R' hlater
  have hlinkable : IsLinkable (G.sourceSubweb A) :=
    _root_.Erdos599.CardinalInduction.ProtectedCardinalAssembly.ExtensionThroughFor.linkable_of_source_mk_le
      hext hSubBase hSub hsourceCard
  obtain ⟨P, hP⟩ := hlinkable
  change IsLinkageBetween G A G.target P at hP
  exact ⟨P, hP⟩

/-- Ambient form with the exact old-roof incidence retained. -/
theorem exists_nativeWholeOwnerResidualTargetLinkage
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage)
    (hext :
      _root_.Erdos599.CardinalInduction.ProtectedCardinalAssembly.ExtensionThroughFor
        Gamma kappa) :
    ∃ P : Set Gamma.DPath,
      IsLinkageBetween Gamma
        (T.nativeWholeOwnerNonsurvivingTerminals R') Gamma.target P ∧
      Gamma.vertexSet P ∩ (nativeCapturedGeometry R).outerRoof =
        T.nativeWholeOwnerNonsurvivingTerminals R' ∧
      Gamma.StarCompatible T.nativeWholeOwnerInterval P := by
  obtain ⟨Pstage, hPstage⟩ :=
    T.exists_nativeWholeOwnerResidualStageTargetLinkage R' hlater hext
  let P := SliceSegmentCore.liftStageFamily
    C.ladder R.later.stage Pstage
  have hP : IsLinkageBetween Gamma
      (T.nativeWholeOwnerNonsurvivingTerminals R') Gamma.target P := by
    exact SliceDeltaLift.IsLinkageBetween.liftStageFamily hPstage
  have hA : T.nativeWholeOwnerNonsurvivingTerminals R' ⊆
      (nativeCapturedGeometry R).newSlice := by
    simpa only [nativeCapturedGeometry_newSlice] using
      T.nativeWholeOwnerNonsurvivingTerminals_subset_oldFrontier R'
  have hroof : Gamma.vertexSet P ∩
      (nativeCapturedGeometry R).outerRoof =
        T.nativeWholeOwnerNonsurvivingTerminals R' := by
    exact vertexSet_liftResidualStageFamily_inter_oldRoof hA hPstage
  refine ⟨P, hP, hroof, ?_⟩
  intro p hp q hq x hxp hxq
  have hxOldRoof : x ∈ (nativeCapturedGeometry R).outerRoof :=
    T.nativeWholeOwnerInterval_vertices_subset_capturedRoof ⟨p, hp, hxp⟩
  have hxP : x ∈ Gamma.vertexSet P := ⟨q, hq, hxq⟩
  have hxResidual : x ∈ T.nativeWholeOwnerNonsurvivingTerminals R' := by
    rw [← hroof]
    exact ⟨hxP, hxOldRoof⟩
  constructor
  · apply T.nativeWholeOwnerInterval_meetsOnlyAtTerminal p hp x hxp
    exact T.nativeWholeOwnerInterval_isLinkageBetween.terminalFrontier_subset
      hxResidual.1
  · obtain ⟨f, rfl, _hends, hsource⟩ := hP.endpointPure q hq
    have hxSource : x ∈ f.support ∩
        T.nativeWholeOwnerNonsurvivingTerminals R' :=
      ⟨hxq, hxResidual⟩
    rw [hsource] at hxSource
    exact (Set.mem_singleton_iff.mp hxSource).symm

#print axioms
  NativePostClosureIntervalTransaction.exists_nativeWholeOwnerResidualStageTargetLinkage
#print axioms
  NativePostClosureIntervalTransaction.exists_nativeWholeOwnerResidualTargetLinkage

end NativePostClosureIntervalTransaction
end Erdos599.Blueprint.LinkageBlueprint
