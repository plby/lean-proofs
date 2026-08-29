/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeNativeWholeOwnerInterval

/-!
# Transaction data retained by native whole-owner normalization

Whole-owner normalization changes the completed current-to-later row, but
does not change the preselected safe target path or its front/tail
decomposition.  This file packages the normalized ambient row together with
the exact fields used by the native outside-occurrence construction.  It
also proves the same missing-reference alternative as the original interval
transaction, now relative to the normalized row.

No assertion is made that the normalized ambient row has already been
absorbed by the old closed set.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath
open _root_.Erdos599.CardinalInduction
open _root_.Erdos599.CardinalInduction.SliceCandidate
open ColouredSafeMovingStages

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {seed : Set V} {z : V} {R : LimitClosure C seed}

namespace NativePostClosureIntervalTransaction

/-- The selected safe front remains literally present in the normalized
row. -/
theorem front_mem_nativeWholeOwnerInterval
    (T : NativePostClosureIntervalTransaction C seed z R) :
    (Sum.inl T.interval.front : Gamma.DPath) ∈
      T.nativeWholeOwnerInterval := by
  apply Or.inl
  refine ⟨T.interval.front_mem_interval, ?_⟩
  apply mem_exceptionalComponentVertices_of_mem
  change T.interval.front.start ∈ T.nativeWholeOwnerSeed
  rw [T.interval.front_start]
  exact Or.inl (Or.inr (Set.mem_singleton z))

/-- A canonical interval meeting the retained target tail is rooted in the
explicit seed of the whole-owner exchange. -/
theorem intervalReference_initial_mem_nativeWholeOwnerSeed_of_meets_tail
    (T : NativePostClosureIntervalTransaction C seed z R)
    {p : Gamma.DPath} (hp : p ∈ T.intervalReference)
    {x : V} (hxp : x ∈ p.support)
    (hxTail : x ∈ T.interval.tail.support) :
    p.initial ∈ T.nativeWholeOwnerSeed := by
  apply Or.inr
  simp only [oldStageContactInitials]
  obtain ⟨pH, hpOrdinary, hpLift⟩ := hp
  refine ⟨pH, ?_, ?_⟩
  refine ⟨hpOrdinary, ?_⟩
  have hpathSafe : (Sum.inl T.interval.path : Gamma.DPath) ∈
      T.interval.safe.ambientFamily := T.interval.path_mem_safe
  rw [T.interval.safe.ambient_eq_lift] at hpathSafe
  obtain ⟨qH, hqSafe, hqLift⟩ := hpathSafe
  refine ⟨qH, hqSafe, ?_⟩
  rw [Set.not_disjoint_iff]
  refine ⟨x, ?_, ?_⟩
  · have hxpLift : x ∈
        ((nativeCapturedGeometry R).ladder.liftStagePath
          (nativeCapturedGeometry R).oldStage pH).support := by
      rw [hpLift]
      exact hxp
    simpa only [
      (nativeCapturedGeometry R).ladder.support_liftStagePath
        (nativeCapturedGeometry R).oldStage pH] using hxpLift
  · have hxPath : x ∈ T.interval.path.support :=
      T.interval.tail_support_subset_path hxTail
    have hxqLift : x ∈
        ((nativeCapturedGeometry R).ladder.liftStagePath
          (nativeCapturedGeometry R).oldStage qH).support := by
      rw [hqLift]
      exact hxPath
    simpa only [
      (nativeCapturedGeometry R).ladder.support_liftStagePath
        (nativeCapturedGeometry R).oldStage qH] using hxqLift
  simpa only [SliceSegmentCore.liftStagePath_initial] using
    congrArg Path.initial hpLift

/-- Whole-owner normalization preserves the exact one-point intersection
of the interval row with the selected target tail. -/
theorem nativeWholeOwnerInterval_tail_inter
    (T : NativePostClosureIntervalTransaction C seed z R) :
    Gamma.vertexSet T.nativeWholeOwnerInterval ∩
        T.interval.tail.support =
      {T.interval.front.finish} := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨p, hpMixed, hxp⟩, hxTail⟩
    rcases hpMixed with hpW | hpY
    · have hx : x ∈ Gamma.vertexSet T.interval.ambientInterval ∩
          T.interval.tail.support := ⟨⟨p, hpW.1, hxp⟩, hxTail⟩
      rw [T.interval.interval_tail_inter] at hx
      exact hx
    · exfalso
      apply hpY.2
      apply mem_exceptionalComponentVertices_of_mem
      exact T.intervalReference_initial_mem_nativeWholeOwnerSeed_of_meets_tail
        hpY.1 hxp hxTail
  · intro x hx
    have hxeq : x = T.interval.front.finish :=
      Set.mem_singleton_iff.1 hx
    subst x
    refine ⟨⟨Sum.inl T.interval.front,
      T.front_mem_nativeWholeOwnerInterval,
      T.interval.front.finish_mem_support⟩, ?_⟩
    rw [← T.interval.tail_start]
    exact T.interval.tail.start_mem_support

/-- The normalized row has the same source-faithful missing-reference
certificate: a missing canonical interval is rooted in the explicit seed,
or its entire support lies in the changed alternating component. -/
theorem nativeWholeOwnerInterval_reference_missing
    (T : NativePostClosureIntervalTransaction C seed z R) :
    ∀ p ∈ (nativeCapturedGeometry R).deferredOldStageOrdinaryFamily,
      (nativeCapturedGeometry R).ladder.liftStagePath
          (nativeCapturedGeometry R).oldStage p ∉
        T.nativeWholeOwnerInterval →
      p.initial ∈ T.nativeWholeOwnerSeed ∨
        p.support ⊆ T.nativeWholeOwnerComponent := by
  intro p hp hnot
  by_cases hseed : p.initial ∈ T.nativeWholeOwnerSeed
  · exact Or.inl hseed
  · right
    have hpRef :
        (nativeCapturedGeometry R).ladder.liftStagePath
            (nativeCapturedGeometry R).oldStage p ∈ T.intervalReference :=
      ⟨p, hp, rfl⟩
    have hinitial :
        ((nativeCapturedGeometry R).ladder.liftStagePath
          (nativeCapturedGeometry R).oldStage p).initial ∈
            T.nativeWholeOwnerComponent :=
      T.intervalReference_initial_mem_component_of_not_mem_nativeWholeOwner
        hpRef hnot
    have hsupport := path_support_subset_exceptionalComponents_right
      T.intervalReference_isLinkageBetween.finiteCharacter hpRef
      ((nativeCapturedGeometry R).ladder.liftStagePath
        (nativeCapturedGeometry R).oldStage p).initial_mem_support hinitial
    intro x hxp
    apply hsupport
    simpa only [SliceSegmentCore.liftStagePath_support] using hxp

/-- Concrete ambient transaction after whole-owner normalization.  The
preselected path and its decomposition are not replaced: `safe`, `path`,
`front`, and `tail` are the literal fields of `base.interval`. -/
structure NativeWholeOwnerTransaction
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (seed : Set V) (z : V) (R : LimitClosure C seed) where
  base : NativePostClosureIntervalTransaction C seed z R
  ambientInterval : Set Gamma.DPath
  ambientInterval_eq : ambientInterval = base.nativeWholeOwnerInterval
  ambientInterval_linkage : IsLinkageBetween Gamma
    (nativeCapturedGeometry R).oldSlice
    (nativeCapturedGeometry R).newSlice ambientInterval
  ambientInterval_meetsOnlyAtTerminal :
    SliceSpliceSource.MeetsOnlyAtTerminal Gamma ambientInterval
      (nativeCapturedGeometry R).newSlice
  ambientInterval_in_outerRoof :
    Gamma.vertexSet ambientInterval ⊆ (nativeCapturedGeometry R).outerRoof
  front_mem_interval :
    (Sum.inl base.interval.front : Gamma.DPath) ∈ ambientInterval
  interval_tail_inter :
    Gamma.vertexSet ambientInterval ∩ base.interval.tail.support =
      {base.interval.front.finish}
  reference_missing :
    ∀ p ∈ (nativeCapturedGeometry R).deferredOldStageOrdinaryFamily,
      (nativeCapturedGeometry R).ladder.liftStagePath
          (nativeCapturedGeometry R).oldStage p ∉ ambientInterval →
      p.initial ∈ base.nativeWholeOwnerSeed ∨
        p.support ⊆ base.nativeWholeOwnerComponent

/-- Package the concrete normalized row while retaining the exact original
safe path and missing-reference provenance. -/
def toNativeWholeOwnerTransaction
    (T : NativePostClosureIntervalTransaction C seed z R) :
    NativeWholeOwnerTransaction C seed z R where
  base := T
  ambientInterval := T.nativeWholeOwnerInterval
  ambientInterval_eq := rfl
  ambientInterval_linkage := T.nativeWholeOwnerInterval_isLinkageBetween
  ambientInterval_meetsOnlyAtTerminal :=
    T.nativeWholeOwnerInterval_meetsOnlyAtTerminal
  ambientInterval_in_outerRoof :=
    T.nativeWholeOwnerInterval_vertices_subset_capturedRoof
  front_mem_interval := T.front_mem_nativeWholeOwnerInterval
  interval_tail_inter := T.nativeWholeOwnerInterval_tail_inter
  reference_missing := T.nativeWholeOwnerInterval_reference_missing

namespace NativeWholeOwnerTransaction

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {seed : Set V} {z : V} {R : LimitClosure C seed}

/-- The normalized transaction retains the preselected safe path by
identity, not merely by endpoint equality. -/
theorem safe_identity
    (N : NativeWholeOwnerTransaction C seed z R) :
    N.base.interval.safe = N.base.safe.toNativeCaptured R :=
  N.base.interval_safe_eq

theorem path_mem_preselected_safe
    (N : NativeWholeOwnerTransaction C seed z R) :
    (Sum.inl N.base.interval.path : Gamma.DPath) ∈
      (N.base.safe.toNativeCaptured R).ambientFamily := by
  rw [← N.safe_identity]
  exact N.base.interval.path_mem_safe

end NativeWholeOwnerTransaction

#print axioms NativePostClosureIntervalTransaction.nativeWholeOwnerInterval_tail_inter
#print axioms NativePostClosureIntervalTransaction.nativeWholeOwnerInterval_reference_missing
#print axioms NativePostClosureIntervalTransaction.toNativeWholeOwnerTransaction
#print axioms NativePostClosureIntervalTransaction.NativeWholeOwnerTransaction.safe_identity
#print axioms NativePostClosureIntervalTransaction.NativeWholeOwnerTransaction.path_mem_preselected_safe

end NativePostClosureIntervalTransaction
end Erdos599.Blueprint.LinkageBlueprint
