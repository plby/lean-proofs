/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayMovingReferenceReservoir

/-!
# The bounded deferred history seed

At stage `a`, the concrete closing recursion has to remember the carriers of
all paths recorded before `a` and every marker born before `a`.  This file
packages that literal history set and proves the two facts needed by the
causal closure: it has cardinality at most `kappa`, and it is contained in
the roof of the stage-`a` frontier.

No final closing set or hammock provider occurs in these statements.  The
proof uses only the deferred ladder's actual recorded-path persistence and
marker roof transport.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace ClubStageGeometry

/-- The literal history available strictly before `a`: all vertices of
earlier recorded paths together with all earlier markers. -/
def deferredHistorySeed
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (a : Ladder.Stage (succ kappa)) : Set V :=
  Gamma.vertexSet
      ((DWeb.KappaLadder.Deferred.bookkeeping C.ladder).recordedBefore a) ∪
    C.ladder.markerSetBelow a

/-- There are at most `kappa` markers born below one stage of the
`kappa^+` ladder. -/
theorem mk_markerSetBelow_le
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (a : Ladder.Stage (succ kappa)) :
    #(C.ladder.markerSetBelow a) ≤ kappa := by
  let witness : ∀ y : C.ladder.markerSetBelow a,
      ∃ b : Ladder.Stage (succ kappa),
        b < a ∧ C.ladder.marker b = some y.1 :=
    fun y ↦ y.2
  let owner : C.ladder.markerSetBelow a → Ladder.Stage (succ kappa) :=
    fun y ↦ Classical.choose (witness y)
  have howner_lt : ∀ y, owner y < a := fun y ↦
    (Classical.choose_spec (witness y)).1
  have howner_injective : Function.Injective owner := by
    intro y z hyz
    apply Subtype.ext
    have hy := (Classical.choose_spec (witness y)).2
    have hz := (Classical.choose_spec (witness z)).2
    rw [show Classical.choose (witness y) =
      Classical.choose (witness z) by exact hyz] at hy
    exact Option.some.inj (hy.symm.trans hz)
  have hlt : #(C.ladder.markerSetBelow a) < succ kappa :=
    RegularCardinal.mk_lt_of_injective_bounded_stage
      a owner howner_injective howner_lt
  exact lt_succ_iff.mp hlt

/-- Fewer than `kappa^+` paths are recorded below one stage, hence at most
`kappa` of them occur there. -/
theorem mk_recordedBefore_le
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (a : Ladder.Stage (succ kappa)) :
    #((DWeb.KappaLadder.Deferred.bookkeeping C.ladder).recordedBefore a)
      ≤ kappa := by
  let witness : ∀ p :
      (DWeb.KappaLadder.Deferred.bookkeeping C.ladder).recordedBefore a,
      ∃ b : Ladder.Stage (succ kappa),
        b < a ∧ C.ladder.chosen b = some p.1 :=
    fun p ↦ p.2
  let owner :
      (DWeb.KappaLadder.Deferred.bookkeeping C.ladder).recordedBefore a →
        Ladder.Stage (succ kappa) :=
    fun p ↦ Classical.choose (witness p)
  have howner_lt : ∀ p, owner p < a := fun p ↦
    (Classical.choose_spec (witness p)).1
  have howner_injective : Function.Injective owner := by
    intro p q hpq
    apply Subtype.ext
    have hp := (Classical.choose_spec (witness p)).2
    have hq := (Classical.choose_spec (witness q)).2
    rw [show Classical.choose (witness p) =
      Classical.choose (witness q) by exact hpq] at hp
    exact Option.some.inj (hp.symm.trans hq)
  have hlt :
      #((DWeb.KappaLadder.Deferred.bookkeeping C.ladder).recordedBefore a) <
        succ kappa :=
    RegularCardinal.mk_lt_of_injective_bounded_stage
      a owner howner_injective howner_lt
  exact lt_succ_iff.mp hlt

/-- The carriers of paths recorded before one stage remain
`kappa`-bounded. -/
theorem mk_recordedHistoryVertices_le
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (a : Ladder.Stage (succ kappa)) :
    #(Gamma.vertexSet
        ((DWeb.KappaLadder.Deferred.bookkeeping C.ladder).recordedBefore a))
      ≤ kappa := by
  apply CardinalInduction.HalfwayFrontierHeight.mk_vertexSet_le_of_mk_family_le
    C.capacity_infinite
  exact C.mk_recordedBefore_le a

/-- The complete deferred history before one stage is `kappa`-small. -/
theorem mk_deferredHistorySeed_le
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (a : Ladder.Stage (succ kappa)) :
    #(C.deferredHistorySeed a) ≤ kappa := by
  unfold deferredHistorySeed
  exact (Cardinal.mk_union_le _ _).trans
    (Cardinal.add_le_of_le C.capacity_infinite
      (C.mk_recordedHistoryVertices_le a)
      (C.mk_markerSetBelow_le a))

/-- Every recorded carrier and earlier marker is already roofed by the
current frontier. -/
theorem deferredHistorySeed_subset_roof
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (a : Ladder.Stage (succ kappa)) :
    C.deferredHistorySeed a ⊆ Gamma.roof (C.ladder.frontier a) := by
  intro x hx
  rcases hx with hx | hx
  · obtain ⟨p, hpRecorded, hxp⟩ := hx
    obtain ⟨b, hba, hb⟩ := hpRecorded
    have hsucc : Ladder.Stage.succExtended b ≤
        Ladder.Stage.toExtended a := by
      change b.1 + 1 ≤ a.1
      exact (Order.add_one_le_iff).2 hba
    have hpStage : p ∈ C.ladder.warpAt a :=
      (C.legal.recordedPathsPersist b p hb
        (Ladder.Stage.toExtended a) hsucc).1
    have hxRoofTerminal : x ∈
        Gamma.roof (Gamma.terminalFrontier (C.ladder.warpAt a)) :=
      DWeb.KappaLadder.Deferred.vertexSet_warpAt_subset_roof_terminalFrontier
        C.legal a ⟨p, hpStage, hxp⟩
    rw [C.ladder.frontier_eq_essential_terminalFrontier
        C.legal.roofsSourceAtStages a,
      Gamma.roof_essential]
    exact hxRoofTerminal
  · obtain ⟨b, hba, hb⟩ := hx
    exact DWeb.KappaLadder.Deferred.marker_mem_roof_frontier_of_lt
      C.legal hba hb

#print axioms ClubStageGeometry.mk_deferredHistorySeed_le
#print axioms ClubStageGeometry.deferredHistorySeed_subset_roof

end ClubStageGeometry
end Erdos599.Blueprint.LinkageBlueprint
