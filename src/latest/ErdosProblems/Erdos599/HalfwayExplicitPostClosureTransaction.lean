/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayExplicitStageIntervalTransaction
import ErdosProblems.Erdos599.HalfwayCausalInitialMovingClosure

/-!
# A post-closure transaction with its actual old index

The old index and its moving-reference difference are explicit. A native
limit closure may have been constructed using a different positive lower
index; that bookkeeping index is never identified with stage zero. The
interval retains the same safe family that was seeded before closing.
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint

open Set Cardinal Order DirectedPath Ladder
open _root_.Erdos599.CardinalInduction
open ColouredSafeMovingStages ExplicitStageInterval

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

structure StagePostClosureIntervalTransaction
    (C : ClubStageGeometry Gamma Y kappa (succ kappa)) (alpha : Stage (succ kappa))
    (seed : Set V) (z : V) (R : LimitClosure C seed) where
  current_lt : alpha < R.later.stage
  safe : SafeStageTargetPath C alpha z
  safe_seeded : Gamma.vertexSet safe.ambientFamily ⊆ seed
  safe_vertices_closed : Gamma.vertexSet safe.ambientFamily ⊆ R.closedSet
  interval : StageIntervalTransaction C alpha R.later.stage current_lt z
  interval_safe_eq : interval.safe = safe
  interval_reference_missing : ReferenceMissingCertificate interval
  difference_subset : C.movingReferenceDifference alpha R.later.stage ⊆ R.closedSet

namespace StagePostClosureIntervalTransaction

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {alpha : Stage (succ kappa)} {seed : Set V} {z : V} {R : LimitClosure C seed}

def intervalRealization (T : StagePostClosureIntervalTransaction C alpha seed z R) :=
  C.ordinaryStageRealization T.current_lt.le

def intervalReference (T : StagePostClosureIntervalTransaction C alpha seed z R) :
    Set Gamma.DPath :=
  SliceSegmentCore.liftStageFamily C.ladder alpha (C.ordinaryStageFamily T.current_lt.le)

theorem intervalReference_isLinkageBetween
    (T : StagePostClosureIntervalTransaction C alpha seed z R) :
    IsLinkageBetween Gamma (C.ladder.frontier alpha \ C.stageExceptional alpha R.later.stage)
      (C.ladder.frontier R.later.stage) T.intervalReference :=
  SliceDeltaLift.IsLinkageBetween.liftStageFamily
    (C.ordinaryStageFamily_isLinkageBetween T.current_lt.le)

theorem intervalReference_initialSet_subset_currentSlice
    (T : StagePostClosureIntervalTransaction C alpha seed z R) :
    Gamma.initialSet T.intervalReference ⊆ C.ladder.frontier alpha := by
  rw [T.intervalReference_isLinkageBetween.initialSet_eq]
  exact Set.sdiff_subset

@[simp] theorem intervalReference_eq_segmentFamily
    (T : StagePostClosureIntervalTransaction C alpha seed z R) :
    T.intervalReference =
      SliceSegmentCore.segmentFamily T.intervalRealization.toSegmentRealization :=
  C.liftStageFamily_ordinaryStageFamily T.current_lt.le

theorem safe_path_mem (T : StagePostClosureIntervalTransaction C alpha seed z R) :
    (Sum.inl T.interval.path : Gamma.DPath) ∈ T.safe.ambientFamily := by
  rw [← T.interval_safe_eq]
  exact T.interval.path_mem_safe

theorem exists_of_safe (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {alpha : Stage (succ kappa)} {seed : Set V} {z : V}
    (P : SafeStageTargetPath C alpha z) (hPseed : Gamma.vertexSet P.ambientFamily ⊆ seed)
    (R : LimitClosure C seed) (hab : alpha < R.later.stage)
    (hdiff : C.movingReferenceDifference alpha R.later.stage ⊆ R.closedSet)
    (hz : z ∈ C.ladder.frontier alpha)
    (hext : ProtectedCardinalAssembly.ExtensionThroughFor Gamma kappa) :
    Nonempty {T : StagePostClosureIntervalTransaction C alpha seed z R // T.safe = P} := by
  obtain ⟨⟨I, hIP, hmissing⟩⟩ := exists_stageIntervalTransaction C hab R.later.mem_club hext P hz
  exact ⟨⟨{
    current_lt := hab
    safe := P
    safe_seeded := hPseed
    safe_vertices_closed := hPseed.trans R.seed_subset
    interval := I
    interval_safe_eq := hIP
    interval_reference_missing := hmissing
    difference_subset := hdiff
  }, rfl⟩⟩

end StagePostClosureIntervalTransaction

namespace CausalSection9Rows

open ColouredSafeEndpointBlueprint

/-- The actual zero-stage safe path, contained closure and localized full
interval row are now returned together. No initial stable state is assumed. -/
theorem exists_initialPostClosureIntervalTransaction
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    (hUnhindered : Gamma.IsUnhindered) {seed : Set V} (hseed : #seed ≤ succ kappa)
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hC : C.ladder = finalLadder Gamma kappa hkappa hGamma seed hseed)
    (hext : ProtectedCardinalAssembly.ExtensionThroughFor Gamma kappa)
    {A0 : Set V} (hA0source : A0 ⊆ Gamma.source) (hA0card : #A0 ≤ kappa)
    (hA0Z : A0 ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed)
    {z : V} (hz : z ∈ A0) :
    ∃ (P : SafeStageTargetPath C (initialStage C) z)
      (R : ColouredSafeEndpointMovingStages.LimitClosure C
        (A0 ∪ Gamma.vertexSet P.ambientFamily))
      (T : StagePostClosureIntervalTransaction C (initialStage C)
        (A0 ∪ Gamma.vertexSet P.ambientFamily) z R.toLimitClosure),
      R.closedSet ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed ∧ T.safe = P := by
  obtain ⟨P, R, hRZ, hdiff⟩ := exists_safeInitialPath_and_containedClosure
    hkappa hGamma hUnhindered hseed C hC hA0source hA0card hA0Z hz
  have hab : initialStage C < R.later.stage := by
    apply lt_of_le_of_lt ?_ R.later.current_lt
    change (0 : Ordinal) ≤ C.newStage.1
    exact bot_le
  have hzOld : z ∈ C.ladder.frontier (initialStage C) := by
    rw [frontier_initialStage C hUnhindered]
    exact hA0source hz
  obtain ⟨⟨T, hTP⟩⟩ := StagePostClosureIntervalTransaction.exists_of_safe C P
    Set.subset_union_right R.toLimitClosure hab hdiff hzOld hext
  exact ⟨P, R, T, hRZ, hTP⟩

end CausalSection9Rows

#print axioms StagePostClosureIntervalTransaction.exists_of_safe
#print axioms CausalSection9Rows.exists_initialPostClosureIntervalTransaction

end Erdos599.Blueprint.LinkageBlueprint
