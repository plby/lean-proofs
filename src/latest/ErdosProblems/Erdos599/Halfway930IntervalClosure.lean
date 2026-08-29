/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Halfway930IntervalSeed
import ErdosProblems.Erdos599.HalfwayRowClosure
import ErdosProblems.Erdos599.HalfwaySelectedClubGeometry

/-!
# The joint closed carrier for Assertions 9.30 and 9.31

The selected 9.30 hammock and the exceptional old-stage interval are first
put into the common small seed.  Assertions 9.22--9.25 then close this seed
under both the selected reference and the actual old-to-new interval row.

Only the first-hit front of the scheduled target path is part of this
roofed row.  Its suffix from the new frontier to the ambient target remains
external and is retained through the exact splice equation in
`OldStageIntervalTransaction`.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Ladder

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- The literal output of closing the coupled 9.30/9.31 seed. -/
structure Closed930IntervalTransaction
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
    {W : LinkageBlueprint Gamma C.selectedReference kappa}
    {u z : V} (R : Contact930Request C W u)
    (T : OldStageIntervalTransaction C z) where
  closedSet : Set V
  seed_subset : R.intervalSeed T ⊆ closedSet
  card_closedSet : #closedSet ≤ kappa
  hammock_closed : HammockClosedUpTo Gamma C.selectedReference closedSet
    C.before C.innerRoof C.outerRoof kappa
  large_hammock_closed : LargeHammockClosed Gamma C.selectedReference
    closedSet C.before C.innerRoof C.outerRoof kappa
  target_paths : HasPreservingTargetPaths Gamma C.oldSlice closedSet
    C.newSlice (fun _ ↦ True)
  reference_closed : ClosedUnderPaths Gamma C.selectedReference closedSet
  interval_closed : ClosedUnderPaths Gamma T.ambientInterval closedSet
  contained_in_roof : ContainedInRoof closedSet C.outerRoof

namespace Closed930IntervalTransaction

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {W : LinkageBlueprint Gamma C.selectedReference kappa}
variable {u z : V} {R : Contact930Request C W u}
variable {T : OldStageIntervalTransaction C z}

/-- The selected first-hit front is literally inside the common closed
carrier. -/
theorem front_support_subset (Q : Closed930IntervalTransaction R T) :
    T.front.support ⊆ Q.closedSet :=
  (R.front_support_subset_intervalSeed T).trans Q.seed_subset

/-- The splice point lies in the common carrier. -/
theorem splice_mem (Q : Closed930IntervalTransaction R T) :
    T.tail.start ∈ Q.closedSet := by
  rw [T.tail_start]
  exact Q.front_support_subset T.front.finish_mem_support

/-- The external target suffix meets the complete interval row only at its
splice point.  This is the separation needed by the later varying-stage
union. -/
theorem interval_tail_inter (Q : Closed930IntervalTransaction R T) :
    Gamma.vertexSet T.ambientInterval ∩ T.tail.support =
      {T.tail.start} := by
  simpa only [T.tail_start] using T.interval_tail_inter

end Closed930IntervalTransaction

namespace Contact930Request

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {W : LinkageBlueprint Gamma C.selectedReference kappa}
variable {u z : V}

/-- Assertions 9.22--9.25 applied to the exact joint 9.30/9.31 seed.

The row-closure family is the actual old-to-new interval, not the external
target suffix. -/
theorem exists_closedIntervalTransaction
    (R : Contact930Request C W u)
    (T : OldStageIntervalTransaction C z)
    (hW : W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent)
    (hbefore : C.before ⊆ C.outerRoof)
    (href : ∀ p ∈ C.selectedReference, p.support ⊆ C.outerRoof)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (heligible : R.IsClubEligible) :
    Nonempty (Closed930IntervalTransaction R T) := by
  obtain ⟨X, hseed, hcard, hclosed, hlarge, htarget,
      hrefClosed, hintervalClosed, hroof⟩ :=
    exists_assertions_9_22_to_9_25_with_rowClosure
      Gamma C.selectedReference T.ambientInterval kappa kappa
      C.before C.innerRoof C.outerRoof C.oldSlice C.newSlice
      (R.intervalSeed T) (fun _ ↦ True)
      (ClubStageGeometry.oldSlice_target_paths C)
      C.selectedReference_isWarp T.ambientInterval_linkage.isWarp
      href T.ambientInterval_in_outerRoof hSafeRoof
      C.capacity_infinite le_rfl C.before_card
      (R.intervalSeed_mk_le T hW)
      (R.intervalSeed_subset_outerRoof T hW hbefore href hSafeRoof heligible)
  exact ⟨{
    closedSet := X
    seed_subset := hseed
    card_closedSet := hcard
    hammock_closed := hclosed
    large_hammock_closed := hlarge
    target_paths := htarget
    reference_closed := hrefClosed
    interval_closed := hintervalClosed
    contained_in_roof := hroof }⟩

end Contact930Request

#print axioms Contact930Request.exists_closedIntervalTransaction
#print axioms Closed930IntervalTransaction.front_support_subset

end LinkageBlueprint
end Blueprint
end Erdos599
