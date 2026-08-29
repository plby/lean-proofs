/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAssertion822UnusedRecord

/-!
# Selection controls avoiding the reserved grounded record

The stationary unused record used after Assertion 8.22 must not become the
owner of a backward link in a selected request route.  At each local fan we
therefore discard paths meeting the countable gadget trace of that record
away from the fan's own apex.  This exceptional family is nonstationary by
the standard joined-family countable-collision lemma.

The apex is deliberately retained.  A frontier point may lie on the
reserved record; the alternating route only needs to avoid a second contact
which could make that record a backward-link owner.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb.KappaLadder

open DirectedPath Stationary PopularGroundingBridge

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- The full auxiliary carrier of the reserved record.  Besides its ordinary
and represented-edge gadgets, this includes the canonical auxiliary source.
For an infinite record that last point is its proxy, which is deliberately
not part of `PopularSwitching.ladderTrace`. -/
def reservedRecordCarrier
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    (R : L.UnusedGroundedRecord hL S) :
    Set (PopularAuxiliary.Input.LambdaVertex V L.groundedInfiniteRecords) :=
  PopularSwitching.ladderTrace
      (L.popularAuxiliaryInput hL.legal) R.record ∪
    {R.auxiliarySource.1}

/-- The full auxiliary carrier of one reserved record is countable. -/
theorem reservedRecordCarrier_countable
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    (R : L.UnusedGroundedRecord hL S) :
    (reservedRecordCarrier R).Countable := by
  exact (PopularSwitching.ladderTrace_countable
    (L.popularAuxiliaryInput hL.legal) R.record).union
      (Set.countable_singleton R.auxiliarySource.1)

/-- Paths in the local request fan which meet the reserved record away from
their own request apex. -/
def reservedRecordCollidingPaths
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    (R : L.UnusedGroundedRecord hL S)
    (r : Request (L.popularAuxiliaryInput hL.legal) S.cut) :
    Set (_root_.Erdos599.DirectedPath.FinitePath
      (L.popularAuxiliaryInput hL.legal).lambda.graph) :=
  {p | ∃ x ∈
      reservedRecordCarrier R \ {requestAuxVertex r},
      x ∈ p.support}

/-- The source indices of reserved-record collisions form a nonstationary
subset of every local stationary fan. -/
theorem reservedRecordCollidingIndices_nonstationary
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    (R : L.UnusedGroundedRecord hL S)
    (r : Request (L.popularAuxiliaryInput hL.legal) S.cut) :
    ¬ IsStationaryBelow kappa
      (GroundingSelection.restrictedIndices
        (L.popularAuxiliaryIndexed hL) (requestFan S r)
          (reservedRecordCollidingPaths R r)) := by
  apply
    PopularAuxiliary.Input.joinedFamily_initialIndices_nonstationary_of_meets_countable
      (L.popularAuxiliaryIndexed hL)
      (PopularSwitching.restrictPaths (requestFan S r)
        (reservedRecordCollidingPaths R r))
      ((reservedRecordCarrier_countable R).mono Set.sdiff_subset)
      Set.disjoint_sdiff_left
  intro p hp
  obtain ⟨x, hxTrace, hxp⟩ := hp.2
  exact ⟨x, hxTrace, hxp⟩

/-- Grounded controls strengthened by off-apex avoidance of one reserved
grounded record. -/
noncomputable def reservedGroundedControls
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S) :
    GroundingSelection.Controls S :=
  let K := L.groundedConcreteControls hL S
  {
    hangingLadder := K.hangingLadder
    hangingFragment := fun r ↦
      K.hangingFragment r ∪ reservedRecordCollidingPaths R r
    ladderRank := K.ladderRank
    ladderTrace := K.ladderTrace
    ladderRank_regressive := K.ladderRank_regressive
    ladderTrace_countable := K.ladderTrace_countable
    ladderTrace_disjoint_apex := K.ladderTrace_disjoint_apex
    hangingLadder_meets := K.hangingLadder_meets
    fragmentIndices_nonstationary := by
      intro r
      have hbase := K.fragmentIndices_nonstationary r
      have hreserved := reservedRecordCollidingIndices_nonstationary R r
      intro hstationary
      apply GroundingSelection.not_isStationaryBelow_union
        hL.legal.regular hL.legal.uncountable hbase hreserved
      exact hstationary.mono
        (GroundingControlledAssembly.restrictedIndices_union_subset
          (L.popularAuxiliaryIndexed hL) (requestFan S r)
          (K.hangingFragment r) (reservedRecordCollidingPaths R r))
  }

/-- A path retained by the reserved controls is still grounded in exactly
the same sense as for the original concrete controls. -/
theorem mem_controlledRequestFan_reservedGroundedControls
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    (R : L.UnusedGroundedRecord hL S)
    (r : Request (L.popularAuxiliaryInput hL.legal) S.cut)
    {p : _root_.Erdos599.DirectedPath.FinitePath
      (L.popularAuxiliaryInput hL.legal).lambda.graph}
    (hp : p ∈ (GroundingControlledAssembly.controlledRequestFan S
      (L.reservedGroundedControls hL S R) r).paths) :
    p ∈ L.groundedSourcePaths hL := by
  have hnot : p ∉
      (L.reservedGroundedControls hL S R).hangingFragment r := by
    intro hbad
    exact hp.2 (Or.inr hbad)
  by_contra hground
  apply hnot
  left
  exact Or.inr hground

/-- The selected request path meets the full reserved-record carrier only at
its own request apex.  In particular, this also controls the proxy which
represents an infinite reserved record. -/
theorem strongSelectedPath_no_offApex_reservedRecord_contact
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    (R : L.UnusedGroundedRecord hL S)
    (r : Request (L.popularAuxiliaryInput hL.legal) S.cut)
    {x : PopularAuxiliary.Input.LambdaVertex V
      L.groundedInfiniteRecords}
    (hxTrace : x ∈ reservedRecordCarrier R)
    (hxApex : x ≠ requestAuxVertex r) :
    x ∉ (GroundingSimultaneousDecode.strongSelectedPath
      (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) r).support := by
  intro hxPath
  apply GroundingSimultaneousDecode.strongSelectedPath_not_mem_hangingFragment
    (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) r
  right
  exact ⟨x, ⟨hxTrace, by simpa only [Set.mem_singleton_iff]⟩, hxPath⟩

/-- The selected request path cannot start at the canonical auxiliary source
of the reserved record.  The source is outside the cut, whereas the request
apex lies in the cut, so the preceding off-apex avoidance applies. -/
theorem strongSelectedPath_start_ne_reservedAuxiliarySource
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    (R : L.UnusedGroundedRecord hL S)
    (r : Request (L.popularAuxiliaryInput hL.legal) S.cut) :
    (GroundingSimultaneousDecode.strongSelectedPath
      (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) r).start ≠
      R.auxiliarySource.1 := by
  intro hstart
  have hsourceCarrier : R.auxiliarySource.1 ∈ reservedRecordCarrier R := by
    exact Or.inr (Set.mem_singleton _)
  have hsourceNeApex : R.auxiliarySource.1 ≠ requestAuxVertex r := by
    intro heq
    apply R.auxiliarySource_not_mem_cut
    rw [heq]
    exact requestAuxVertex_mem_cut r
  apply strongSelectedPath_no_offApex_reservedRecord_contact R r
    hsourceCarrier hsourceNeApex
  rw [← hstart]
  exact (GroundingSimultaneousDecode.strongSelectedPath
    (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) r).start_mem_support

/-- The selected path under reserved controls still has a grounded source
index. -/
theorem strongSelectedPath_mem_groundedSourcePaths_reserved
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    (R : L.UnusedGroundedRecord hL S)
    (r : Request (L.popularAuxiliaryInput hL.legal) S.cut) :
    GroundingSimultaneousDecode.strongSelectedPath
        (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R) r ∈
      L.groundedSourcePaths hL := by
  apply mem_controlledRequestFan_reservedGroundedControls R r
  exact
    GroundingSimultaneousDecode.strongSelectedPath_mem_controlledRequestFan
      (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) r

end DWeb.KappaLadder
end Erdos599
