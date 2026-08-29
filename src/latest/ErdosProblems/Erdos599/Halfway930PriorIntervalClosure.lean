/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Halfway930PriorStageRequest
import ErdosProblems.Erdos599.HalfwayOldStageIntervalSeed
import ErdosProblems.Erdos599.HalfwayOldStageIntervalSplice
import ErdosProblems.Erdos599.HalfwayRowClosure
import ErdosProblems.Erdos599.HalfwaySelectedClubGeometry

/-!
# The prior-stage joint closure for Assertions 9.30 and 9.31

The incoming blueprint in the coupled construction is certified at the old
club frontier.  A 9.30 request is selected there; only after its endpoint at
that frontier has been fixed is the old-to-new interval transaction chosen.
This file forms and closes that dependency-correct joint seed.

The ambient target suffix is deliberately not part of the roofed closure.
Only its first-hit front belongs to the closed carrier; the suffix is retained
externally by the exact splice equation of `OldStageIntervalTransaction`.
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

namespace PriorContact930Request

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {W : LinkageBlueprint Gamma C.selectedReference kappa}
variable {u z : V}

/-- The complete joint seed of a prior-stage 9.30 request and the exceptional
old-to-new interval exchange. -/
def intervalSeed
    (R : PriorContact930Request C W u)
    (T : OldStageIntervalTransaction C z) : Set V :=
  T.augmentedIntervalSeed R.seed

/-- The dependency-correct joint seed is still `kappa`-small. -/
theorem intervalSeed_mk_le
    (R : PriorContact930Request C W u)
    (T : OldStageIntervalTransaction C z)
    (hW : W.IsLinkageBlueprint C.oldSlice C.oldClosedSet C.persistent) :
    #(R.intervalSeed T) <= kappa := by
  apply T.mk_augmentedIntervalSeed_le
  exact R.seed_mk_le hW

/-- The branch-specific 9.30 seed survives literally. -/
theorem seed_subset_intervalSeed
    (R : PriorContact930Request C W u)
    (T : OldStageIntervalTransaction C z) :
    R.seed <= R.intervalSeed T :=
  T.baseSeed_subset_augmentedIntervalSeed R.seed

/-- Every exceptional interval component is explicitly included. -/
theorem exceptionalComponents_subset_intervalSeed
    (R : PriorContact930Request C W u)
    (T : OldStageIntervalTransaction C z) :
    T.exceptionalComponents <= R.intervalSeed T :=
  T.exceptionalComponents_subset_augmentedIntervalSeed R.seed

/-- In particular the scheduled first-hit front belongs to the joint seed. -/
theorem front_support_subset_intervalSeed
    (R : PriorContact930Request C W u)
    (T : OldStageIntervalTransaction C z) :
    T.front.support <= R.intervalSeed T :=
  T.front_support_subset_exceptional.trans
    (R.exceptionalComponents_subset_intervalSeed T)

/-- Every selected-reference component which touches an exceptional interval
component is swallowed in full. -/
theorem exceptionalReference_support_subset
    (R : PriorContact930Request C W u)
    (T : OldStageIntervalTransaction C z)
    {p : Gamma.DPath} (hp : p ∈ C.selectedReference)
    (hcontact : (p.support ∩ T.exceptionalComponents).Nonempty) :
    p.support <= R.intervalSeed T := by
  exact (support_subset_meetingVertices Gamma C.selectedReference
    T.exceptionalComponents hp hcontact).trans
      (Set.subset_union_right.trans Set.subset_union_right)

/-- The old-stage request and interval seed are contained in the later roof,
without any cardinal bound on the ambient source. -/
theorem intervalSeed_subset_outerRoof
    (R : PriorContact930Request C W u)
    (T : OldStageIntervalTransaction C z)
    (hW : W.IsLinkageBlueprint C.oldSlice C.oldClosedSet C.persistent)
    (hbefore : C.before <= C.outerRoof)
    (href : ∀ p ∈ C.selectedReference, p.support <= C.outerRoof)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (heligible : R.IsClubEligible) :
    R.intervalSeed T <= C.outerRoof :=
  T.augmentedIntervalSeed_subset_outerRoof
    (R.seed_subset_outerRoof hW hbefore href hSafeRoof heligible) href

end PriorContact930Request

/-- The literal output of closing the dependency-correct joint seed. -/
structure ClosedPrior930IntervalTransaction
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
    {W : LinkageBlueprint Gamma C.selectedReference kappa}
    {u z : V} (R : PriorContact930Request C W u)
    (T : OldStageIntervalTransaction C z) where
  closedSet : Set V
  seed_subset : R.intervalSeed T <= closedSet
  card_closedSet : #closedSet <= kappa
  hammock_closed : HammockClosedUpTo Gamma C.selectedReference closedSet
    C.before C.innerRoof C.outerRoof kappa
  large_hammock_closed : LargeHammockClosed Gamma C.selectedReference
    closedSet C.before C.innerRoof C.outerRoof kappa
  target_paths : HasPreservingTargetPaths Gamma C.oldSlice closedSet
    C.newSlice (fun _ => True)
  reference_closed : ClosedUnderPaths Gamma C.selectedReference closedSet
  interval_closed : ClosedUnderPaths Gamma T.splicedIntervalRow closedSet
  contained_in_roof : ContainedInRoof closedSet C.outerRoof

namespace ClosedPrior930IntervalTransaction

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {W : LinkageBlueprint Gamma C.selectedReference kappa}
variable {u z : V} {R : PriorContact930Request C W u}
variable {T : OldStageIntervalTransaction C z}

theorem front_support_subset (Q : ClosedPrior930IntervalTransaction R T) :
    T.front.support <= Q.closedSet :=
  (R.front_support_subset_intervalSeed T).trans Q.seed_subset

theorem splice_mem (Q : ClosedPrior930IntervalTransaction R T) :
    T.tail.start ∈ Q.closedSet := by
  rw [T.tail_start]
  exact Q.front_support_subset T.front.finish_mem_support

/-- The target suffix remains external and meets the complete interval row
only at the splice point. -/
theorem interval_tail_inter (Q : ClosedPrior930IntervalTransaction R T) :
    Gamma.vertexSet T.ambientInterval ∩ T.tail.support =
      {T.tail.start} := by
  simpa only [T.tail_start] using T.interval_tail_inter

end ClosedPrior930IntervalTransaction

namespace PriorContact930Request

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {W : LinkageBlueprint Gamma C.selectedReference kappa}
variable {u z : V}

/-- Assertions 9.22--9.25 applied after the genuine old-stage request has
been selected.  This is the old-slice analogue of the earlier closure API. -/
theorem exists_closedIntervalTransaction
    (R : PriorContact930Request C W u)
    (T : OldStageIntervalTransaction C z)
    (hW : W.IsLinkageBlueprint C.oldSlice C.oldClosedSet C.persistent)
    (hbefore : C.before <= C.outerRoof)
    (href : ∀ p ∈ C.selectedReference, p.support <= C.outerRoof)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (heligible : R.IsClubEligible) :
    Nonempty (ClosedPrior930IntervalTransaction R T) := by
  have hrowRoof : Gamma.vertexSet T.splicedIntervalRow ⊆ C.outerRoof :=
    CardinalInduction.SliceSpliceSource.vertexSet_star_subset_roof
      T.oldReference_starCompatible
      (C.legal.frontierChronology C.old_lt_new)
      T.oldReference_vertexSet_subset_roof
      (by
        rintro x ⟨p, hp, hxp⟩
        exact T.ambientInterval_in_outerRoof p hp hxp)
  obtain ⟨X, hseed, hcard, hclosed, hlarge, htarget,
      hrefClosed, hintervalClosed, hroof⟩ :=
    exists_assertions_9_22_to_9_25_with_rowClosure
      Gamma C.selectedReference T.splicedIntervalRow kappa kappa
      C.before C.innerRoof C.outerRoof C.oldSlice C.newSlice
      (R.intervalSeed T) (fun _ => True)
      (ClubStageGeometry.oldSlice_target_paths C)
      C.selectedReference_isWarp T.splicedIntervalRow_tight.1.isWarp
      href (fun p hp x hxp ↦ hrowRoof ⟨p, hp, hxp⟩) hSafeRoof
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

end PriorContact930Request

#print axioms PriorContact930Request.exists_closedIntervalTransaction
#print axioms ClosedPrior930IntervalTransaction.front_support_subset

end LinkageBlueprint
end Blueprint
end Erdos599
