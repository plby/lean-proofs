/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosurePureBoundary
import ErdosProblems.Erdos599.ReferenceSubpathEmbedding

/-!
# Embedding the captured interval reference in the limiting warp

Each canonical interval is a finite segment of a distinct component of the
captured later-stage warp.  Direct-limit growth extends that component to a
limiting-warp owner.  Indexing by the segment's visible initial vertex makes
the owner assignment canonical enough to prove injectivity.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder
open _root_.Erdos599.CardinalInduction

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace PostClosureIntervalTransaction

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ X0 : Set V} {z : V}
variable {R : DynamicMoving931GlobalClosure C globalZ X0}

/-- The source coordinate of a literal captured interval. -/
noncomputable def intervalReferenceSource
    (T : PostClosureIntervalTransaction C globalZ X0 z R)
    (q : T.intervalReference) :
    ↑(R.capturedGeometry.oldSlice \
      R.capturedGeometry.deferredOldStageExceptional : Set V) := by
  refine ⟨q.1.initial, ?_⟩
  rw [← T.intervalReference_isLinkageBetween.initialSet_eq]
  exact ⟨q.1, q.2, rfl⟩

/-- A reference member is exactly the realized segment indexed by its
visible initial coordinate. -/
theorem intervalReference_eq_segment_source
    (T : PostClosureIntervalTransaction C globalZ X0 z R)
    (q : T.intervalReference) :
    q.1 =
      (Sum.inl
        (R.capturedGeometry.deferredOldStageRealization.toSegmentRealization.segment
          (T.intervalReferenceSource q)) : Gamma.DPath) := by
  have hq := q.2
  change q.1 ∈ SliceSegmentCore.liftStageFamily
    R.capturedGeometry.ladder R.capturedGeometry.oldStage
      R.capturedGeometry.deferredOldStageOrdinaryFamily at hq
  rw [R.capturedGeometry.liftStageFamily_deferredOldStageOrdinaryFamily] at hq
  obtain ⟨a, hqa⟩ := hq
  have ha : a = T.intervalReferenceSource q := by
    apply Subtype.ext
    change a.1 = q.1.initial
    exact
      (R.capturedGeometry.deferredOldStageRealization.toSegmentRealization.segment_start
        a).symm.trans (congrArg DirectedPath.Path.initial hqa)
  rw [← ha]
  exact hqa.symm

/-- A captured later-stage component has a continuation in the limiting
warp of the same deferred ladder. -/
theorem exists_limitWarp_owner_for_intervalSource
    (_T : PostClosureIntervalTransaction C globalZ X0 z R)
    (a : ↑(R.capturedGeometry.oldSlice \
      R.capturedGeometry.deferredOldStageExceptional : Set V)) :
    ∃ p ∈ C.ladder.limitWarp,
      Gamma.Extends
        (R.capturedGeometry.deferredOldStageRealization.toSegmentRealization.carrier a)
        p := by
  have hlimit : Order.IsSuccLimit (succ kappa).ord :=
    Cardinal.isSuccLimit_ord C.legal.regular.aleph0_le
  exact C.legal.limitStages.grows_to_limit
    (Ladder.finalStage (succ kappa)) hlimit
    ⟨R.capturedGeometry.newStage.1, R.capturedGeometry.newStage.2⟩
    (R.capturedGeometry.deferredOldStageRealization.toSegmentRealization.carrier a)
    (R.capturedGeometry.deferredOldStageRealization.toSegmentRealization.carrier_mem a)

/-- A fixed limiting owner for each interval source coordinate. -/
noncomputable def limitOwnerForIntervalSource
    (T : PostClosureIntervalTransaction C globalZ X0 z R)
    (a : ↑(R.capturedGeometry.oldSlice \
      R.capturedGeometry.deferredOldStageExceptional : Set V)) : Gamma.DPath :=
  Classical.choose (T.exists_limitWarp_owner_for_intervalSource a)

theorem limitOwnerForIntervalSource_mem
    (T : PostClosureIntervalTransaction C globalZ X0 z R)
    (a : ↑(R.capturedGeometry.oldSlice \
      R.capturedGeometry.deferredOldStageExceptional : Set V)) :
    T.limitOwnerForIntervalSource a ∈ C.ladder.limitWarp :=
  (Classical.choose_spec
    (T.exists_limitWarp_owner_for_intervalSource a)).1

theorem carrier_extends_limitOwnerForIntervalSource
    (T : PostClosureIntervalTransaction C globalZ X0 z R)
    (a : ↑(R.capturedGeometry.oldSlice \
      R.capturedGeometry.deferredOldStageExceptional : Set V)) :
    Gamma.Extends
      (R.capturedGeometry.deferredOldStageRealization.toSegmentRealization.carrier a)
      (T.limitOwnerForIntervalSource a) :=
  (Classical.choose_spec
    (T.exists_limitWarp_owner_for_intervalSource a)).2

/-- The limiting owner of an actual interval member. -/
noncomputable def intervalReferenceOwner
    (T : PostClosureIntervalTransaction C globalZ X0 z R)
    (q : T.intervalReference) : Gamma.DPath :=
  T.limitOwnerForIntervalSource (T.intervalReferenceSource q)

theorem intervalReferenceOwner_mem
    (T : PostClosureIntervalTransaction C globalZ X0 z R)
    (q : T.intervalReference) :
    T.intervalReferenceOwner q ∈ C.ladder.limitWarp :=
  T.limitOwnerForIntervalSource_mem (T.intervalReferenceSource q)

/-- Every local interval member is a subpath of its limiting owner. -/
theorem intervalReference_subpath_owner
    (T : PostClosureIntervalTransaction C globalZ X0 z R)
    (q : T.intervalReference) :
    q.1.IsSubpathOf (T.intervalReferenceOwner q) := by
  rw [T.intervalReference_eq_segment_source q]
  exact ⟨
    (R.capturedGeometry.deferredOldStageRealization.toSegmentRealization.segment_subpath
      (T.intervalReferenceSource q)).1.trans
        (Gamma.support_mono_of_extends
          (T.carrier_extends_limitOwnerForIntervalSource
            (T.intervalReferenceSource q))),
    (R.capturedGeometry.deferredOldStageRealization.toSegmentRealization.segment_subpath
      (T.intervalReferenceSource q)).2.trans
        (DirectedPath.Path.edgeSet_mono_of_extends
          (T.carrier_extends_limitOwnerForIntervalSource
            (T.intervalReferenceSource q)))⟩

/-- Distinct captured intervals have distinct limiting owners. -/
theorem intervalReferenceOwner_injective
    (T : PostClosureIntervalTransaction C globalZ X0 z R) :
    Function.Injective T.intervalReferenceOwner := by
  intro q r howner
  let a := T.intervalReferenceSource q
  let b := T.intervalReferenceSource r
  have hcarrier :
      R.capturedGeometry.deferredOldStageRealization.toSegmentRealization.carrier a =
        R.capturedGeometry.deferredOldStageRealization.toSegmentRealization.carrier b := by
    apply DWeb.IsWarp.eq_of_initial_eq Gamma
      (C.legal.warpStages
        (Ladder.Stage.toExtended R.capturedGeometry.newStage))
      (R.capturedGeometry.deferredOldStageRealization.toSegmentRealization.carrier_mem a)
      (R.capturedGeometry.deferredOldStageRealization.toSegmentRealization.carrier_mem b)
    calc
      (R.capturedGeometry.deferredOldStageRealization.toSegmentRealization.carrier a).initial =
          (T.limitOwnerForIntervalSource a).initial :=
        Gamma.extends_initial (T.carrier_extends_limitOwnerForIntervalSource a)
      _ = (T.limitOwnerForIntervalSource b).initial := by
        exact congrArg DirectedPath.Path.initial howner
      _ =
          (R.capturedGeometry.deferredOldStageRealization.toSegmentRealization.carrier b).initial :=
        (Gamma.extends_initial
          (T.carrier_extends_limitOwnerForIntervalSource b)).symm
  have hab : a = b :=
    R.capturedGeometry.deferredOldStageRealization.toSegmentRealization.carrier_injective
      hcarrier
  have hsources : T.intervalReferenceSource q =
      T.intervalReferenceSource r := by
    simpa only [a, b] using hab
  apply Subtype.ext
  rw [T.intervalReference_eq_segment_source q,
    T.intervalReference_eq_segment_source r, hsources]

/-- The actual captured interval reference embeds injectively, member by
member, into the global limiting warp. -/
noncomputable def intervalGlobalReferenceEmbedding
    (T : PostClosureIntervalTransaction C globalZ X0 z R) :
    _root_.Erdos599.Blueprint.ReferenceSubpathEmbedding Gamma
      T.intervalReference C.ladder.limitWarp where
  owner q := ⟨T.intervalReferenceOwner q,
    T.intervalReferenceOwner_mem q⟩
  owner_injective := by
    intro q r hqr
    apply T.intervalReferenceOwner_injective
    exact congrArg Subtype.val hqr
  support_subset q := (T.intervalReference_subpath_owner q).1
  edgeSet_subset q := (T.intervalReference_subpath_owner q).2
  global_isWarp := C.legal.warpStages (Ladder.finalStage (succ kappa))

/-- Internal safeness for the literal interval reference transports to the
limiting ladder warp; no exposed-endpoint confinement is required. -/
theorem internallySafe_limitWarp
    (T : PostClosureIntervalTransaction C globalZ X0 z R)
    {Q : _root_.Erdos599.Alternating.AltPath Gamma.graph}
    (hQ : _root_.Erdos599.Blueprint.InternallySafe
      T.intervalReference Q) :
    _root_.Erdos599.Blueprint.InternallySafe C.ladder.limitWarp Q :=
  T.intervalGlobalReferenceEmbedding.internallySafe hQ

#print axioms intervalReference_subpath_owner
#print axioms intervalReferenceOwner_injective
#print axioms intervalGlobalReferenceEmbedding
#print axioms internallySafe_limitWarp

end PostClosureIntervalTransaction
end Erdos599.Blueprint.LinkageBlueprint
