/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCofinalGlobalTransition
import ErdosProblems.Erdos599.HalfwayClubFinalGeometry

/-!
# The concrete final interface of the half-way scheduler

`Stable934Compiler` is a one-request successor operation: it returns a new
blueprint together with `StableExtensionConclusion`.  The sound global lane
needs strictly more information.  Namely, it needs the retained real-edge
relation and carrier at every stage, their monotonicity and fairness, and the
exact root/sink boundary at the selected ladder frontier.

This file records the shortest existing checked route once those genuinely
global objects have been constructed.  It deliberately consumes the concrete
`SuccessorClubStageRun` and `RankedClubFrontierBoundary` structures rather
than hiding the missing scheduler construction behind a proposition alias.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- A concrete successor-stage run, together with its exact final frontier
boundary, compiles to the oriented resolution consumed by the half-way
clause.  Countable boundedness and the global rank are constructed by the
cofinal-run conversion. -/
theorem SuccessorClubStageRun.exists_orientedGlobalResolution
    {C : ClubStageGeometry Gamma Y kappa (Order.succ kappa)}
    (R : SuccessorClubStageRun C) (hkappa : aleph0 <= kappa)
    {A0 : Set V}
    (B : CardinalInduction.HalfwayScheduler.RankedClubFrontierBoundary
      C (R.toCofinalRun hkappa).rankedFairGlobalRelation A0) :
    Nonempty
      (CardinalInduction.HalfwayScheduler.OrientedGlobalResolution
        Gamma A0 kappa) :=
  B.exists_globalResolution

/-- The same concrete scheduler output already gives the qualified half-way
linkage for its designated source set. -/
theorem SuccessorClubStageRun.exists_halfwayLinkage
    {C : ClubStageGeometry Gamma Y kappa (Order.succ kappa)}
    (R : SuccessorClubStageRun C) (hkappa : aleph0 <= kappa)
    {A0 : Set V}
    (B : CardinalInduction.HalfwayScheduler.RankedClubFrontierBoundary
      C (R.toCofinalRun hkappa).rankedFairGlobalRelation A0) :
    exists W : Set Gamma.DPath,
      CardinalInduction.IsHalfwayLinkageOfAltitude Gamma A0 kappa W :=
  B.exists_halfwayLinkage

/-- Per-designated-set construction of the concrete successor run and its
frontier boundary is exactly the remaining scheduler constructor needed for
`HalfwayClauseAt`. -/
theorem halfwayClauseAt_of_successorClubStageRuns
    (hkappa : aleph0 <= kappa)
    (hbuild : forall A0 : Set V, A0 ⊆ Gamma.source -> #A0 = kappa ->
      exists reference : Set Gamma.DPath,
        exists C : ClubStageGeometry Gamma reference kappa
            (Order.succ kappa),
          exists R : SuccessorClubStageRun C,
            CardinalInduction.HalfwayScheduler.RankedClubFrontierBoundary
              C (R.toCofinalRun hkappa).rankedFairGlobalRelation A0) :
    CardinalInduction.HalfwayClauseAt Gamma kappa := by
  intro A0 hA0 hcard
  obtain ⟨reference, C, R, B⟩ := hbuild A0 hA0 hcard
  exact R.exists_halfwayLinkage hkappa B

/-- Actual arbitrary-web endpoint of the scheduler lane.  The Section 9
run is carried out in the normalization of `G`; the selected legal-ladder
frontier then transports the resulting linkage back to `G`.  The reference
warp is existential because it is selected only after the club stage has
been chosen. -/
theorem halfwayClauseAt_of_normalizedSuccessorClubStageRuns
    {G : DWeb V} (hkappa : aleph0 <= kappa)
    (hbuild : forall A0 : Set V, A0 ⊆ G.source -> #A0 = kappa ->
      exists reference : Set G.normalized.DPath,
        exists C : ClubStageGeometry G.normalized reference kappa
            (Order.succ kappa),
          exists R : SuccessorClubStageRun C,
            CardinalInduction.HalfwayScheduler.RankedClubFrontierBoundary
              C (R.toCofinalRun hkappa).rankedFairGlobalRelation A0) :
    CardinalInduction.HalfwayClauseAt G kappa := by
  intro A0 hA0 hcard
  obtain ⟨reference, C, R, B⟩ := hbuild A0 hA0 hcard
  exact B.exists_original_halfwayLinkage

end LinkageBlueprint
end Blueprint
end Erdos599
