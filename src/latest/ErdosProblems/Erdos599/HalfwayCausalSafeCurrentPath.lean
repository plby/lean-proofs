/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCausalSection9Rows
import ErdosProblems.Erdos599.HalfwayPostClosureIntervalTransaction

/-!
# A causal safe current-stage path inside the global carrier

The safe path used after the moving closure must already have been selected
by the causal Section 9 row construction.  The theorem below retrieves that
literal strict-prior safe-completion choice, transports it across prefix
agreement to the final current stage, and lifts it to the ambient web.  Its
carrier stays inside the previously constructed global carrier and is
`kappa`-small.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder
open _root_.Erdos599.CardinalInduction

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace CausalSection9Rows

/-- Ambient stage lifting preserves the literal vertex carrier. -/
private theorem vertexSet_liftStageFamily
    {L : Gamma.KappaLadder (succ kappa)}
    {a : Ladder.Stage (succ kappa)}
    (W : Set (L.stageWeb a).DPath) :
    Gamma.vertexSet (SliceSegmentCore.liftStageFamily L a W) =
      (L.stageWeb a).vertexSet W := by
  ext x
  constructor
  · rintro ⟨p, ⟨q, hqW, rfl⟩, hxp⟩
    exact ⟨q, hqW, by
      simpa only [SliceSegmentCore.liftStagePath_support] using hxp⟩
  · rintro ⟨q, hqW, hxq⟩
    exact ⟨L.liftStagePath a q, ⟨q, hqW, rfl⟩, by
      simpa only [SliceSegmentCore.liftStagePath_support] using hxq⟩

/-- A safe path at any unhindered actual stage already present in the
causal global carrier. The current-stage pair is not used to constrain
the queried index, so the theorem also applies at zero. -/
theorem exists_safeStageTargetPath_in_globalCarrier
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hC : C.ladder =
      finalLadder Gamma kappa hkappa hGamma seed hseed)
    (current : Ladder.Stage (succ kappa))
    (hcurrent : (C.ladder.stageWeb current).IsUnhindered)
    {z : V}
    (hz : z ∈ C.ladder.frontier current ∩
      globalCarrier Gamma kappa hkappa hGamma seed hseed) :
    ∃ P : SafeStageTargetPath C current z,
      Gamma.vertexSet P.ambientFamily ⊆
        globalCarrier Gamma kappa hkappa hGamma seed hseed ∧
      #(Gamma.vertexSet P.ambientFamily) ≤ kappa := by
  let L := finalLadder Gamma kappa hkappa hGamma seed hseed
  have hU : (L.stageWeb current).IsUnhindered := by
    change ((finalLadder Gamma kappa hkappa hGamma seed hseed).stageWeb
      current).IsUnhindered
    rw [← hC]
    exact hcurrent
  have hzFrontier : z ∈ L.frontier current := by
    change z ∈ (finalLadder Gamma kappa hkappa hGamma seed hseed).frontier
      current
    rw [← hC]
    exact hz.1
  obtain ⟨a, ha, hUprior, za, hza, hzaGlobal⟩ :=
    exists_later_safeStageTargetChoice
      (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed
      current hU hz.2 hzFrontier
  let prior := fun b (_hba : b < a) ↦
    (rule Gamma kappa hkappa hGamma seed hseed).state
      (hkappa.trans (le_succ kappa)) b
  let H := priorCore Gamma a prior
  let c : RegularSafeCompletion.SafeCompletionChoice
      (H.stageWeb current) ∅ za.1 :=
    safeStageTargetChoice H current (priorCarrier a prior)
      hUprior za
  have hstageFinal : H.stageWeb current = L.stageWeb current := by
    unfold DWeb.KappaLadder.stageWeb
    exact congrArg Gamma.stageWebOf
      (prior_geometry_eq_final_of_lt
        (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed ha).1
  have hstage : H.stageWeb current =
      C.ladder.stageWeb current := by
    calc
      H.stageWeb current = L.stageWeb current := hstageFinal
      _ = C.ladder.stageWeb current := by rw [hC]
  change c.path.support ⊆
    globalCarrier Gamma kappa hkappa hGamma seed hseed at hzaGlobal
  let liftAdj : ∀ {x y : V}, (H.stageWeb current).graph.Adj x y →
      (C.ladder.stageWeb current).graph.Adj x y := by
    intro x y hxy
    rw [← hstage]
    exact hxy
  let f : FinitePath (C.ladder.stageWeb current).graph :=
    c.path.lift liftAdj
  have hfSupport : f.support = c.path.support := by
    simp only [f, FinitePath.support_lift]
  have hcGlobal : f.support ⊆
      globalCarrier Gamma kappa hkappa hGamma seed hseed := by
    rw [hfSupport]
    exact hzaGlobal
  have hsource : (H.stageWeb current).source =
      (C.ladder.stageWeb current).source :=
    congrArg DWeb.source hstage
  have htarget : (H.stageWeb current).target =
      (C.ladder.stageWeb current).target :=
    congrArg DWeb.target hstage
  have hdelete :
      (H.stageWeb current).delete (∅ ∪ c.path.support) =
        (C.ladder.stageWeb current).delete (∅ ∪ f.support) := by
    rw [hfSupport]
    exact congrArg (fun G : DWeb V ↦ G.delete (∅ ∪ c.path.support)) hstage
  let cC : RegularSafeCompletion.SafeCompletionChoice
      (C.ladder.stageWeb current) ∅ z := {
    path := f
    start_eq := by
      simpa only [f, FinitePath.lift] using c.start_eq.trans hza
    start_source := by
      rw [← hsource]
      simpa only [f, FinitePath.lift] using c.start_source
    finish_target := by
      rw [← htarget]
      simpa only [f, FinitePath.lift] using c.finish_target
    source_pure := by
      rw [← hsource, hfSupport]
      simpa only [f, FinitePath.lift] using c.source_pure
    target_pure := by
      rw [← htarget, hfSupport]
      simpa only [f, FinitePath.lift] using c.target_pure
    avoids := by
      rw [hfSupport]
      exact c.avoids
    next_unhindered := by
      rw [← hdelete]
      exact c.next_unhindered }
  let P : SafeStageTargetPath C current z := {
    stageFamily := cC.family
    stage_linkage := cC.family_isLinkageBetween
    deletion_safe := by
      rw [cC.vertexSet_family]
      simpa only [Set.empty_union] using cC.next_unhindered
    ambientFamily := SliceSegmentCore.liftStageFamily
      C.ladder current cC.family
    ambient_eq_lift := rfl
    ambient_linkage :=
      CardinalInduction.SliceDeltaLift.IsLinkageBetween.liftStageFamily
        cC.family_isLinkageBetween }
  refine ⟨P, ?_, ?_⟩
  · change Gamma.vertexSet
      (SliceSegmentCore.liftStageFamily
        C.ladder current cC.family) ⊆ _
    rw [vertexSet_liftStageFamily, cC.vertexSet_family]
    exact hcGlobal
  · change #(Gamma.vertexSet
      (SliceSegmentCore.liftStageFamily
        C.ladder current cC.family)) ≤ kappa
    rw [vertexSet_liftStageFamily, cC.vertexSet_family]
    change #f.support ≤ kappa
    rw [hfSupport]
    exact c.path.support_countable.le_aleph0.trans hkappa

/-- Preserve the previous current-stage theorem as the exact specialization
of the stage-explicit causal selection. -/
theorem exists_safeCurrentStageTargetPath_in_globalCarrier
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hC : C.ladder = finalLadder Gamma kappa hkappa hGamma seed hseed)
    {z : V} (hz : z ∈ C.newSlice ∩ globalCarrier Gamma kappa hkappa hGamma seed hseed) :
    ∃ P : SafeCurrentStageTargetPath C z,
      Gamma.vertexSet P.ambientFamily ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed ∧
      #(Gamma.vertexSet P.ambientFamily) ≤ kappa := by
  obtain ⟨P, hPZ, hPcard⟩ := exists_safeStageTargetPath_in_globalCarrier hkappa hGamma hseed
    C hC C.newStage (C.stageWeb_isUnhindered C.new_mem_club) hz
  exact ⟨P.toCurrent, hPZ, hPcard⟩

end CausalSection9Rows

#print axioms
  CausalSection9Rows.exists_safeCurrentStageTargetPath_in_globalCarrier
#print axioms CausalSection9Rows.exists_safeStageTargetPath_in_globalCarrier

end Erdos599.Blueprint.LinkageBlueprint
