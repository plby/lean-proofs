/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeExplicitPostClosureClassification
import ErdosProblems.Erdos599.HalfwaySourceInsideRestriction

/-!
# The literal native inside-plus-assignment relation

The finite selected edges and inside row edges are separately biunique.
Actual cut initials and terminals exclude cross-incidence collisions. The
resulting closed relation preserves original roots, and its sinks are popular
or carry a concrete closed limiting owner. It is not yet asserted to be a
source-covering blueprint: covered owners still need the simultaneous repair.
-/

namespace Erdos599.Blueprint.LinkageBlueprint

open Set Cardinal Order DirectedPath
open _root_.Erdos599.Alternating
open SwitchingCore.RelationalInterval
open ColouredSafeReverseReachability ColouredSafeMovingStages
open FracturedFixedSafeAssignment
open StagePostClosureIntervalTransaction

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {alpha : Ladder.Stage (succ kappa)}
variable {seed : Set V} {z : V} {R : LimitClosure C seed}
variable {T : StagePostClosureIntervalTransaction C alpha seed z R}
variable {F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
  (Gamma := Gamma) T.interval.ambientInterval R.closedSet}

namespace StagePostClosureIntervalTransaction.ClassifiedFixedOutsideAssignment

def closedEdges (A : ClassifiedFixedOutsideAssignment T F) : Set (V × V) :=
  sourceInsideEdges T.interval.ambientInterval R.closedSet ∪ A.assignment.toCompressed.finiteEdges

theorem closedEdges_subset_closed (A : ClassifiedFixedOutsideAssignment T F) :
    A.closedEdges ⊆ R.closedSet ×ˢ R.closedSet := by
  intro e he
  rcases he with he | he
  · exact he.2
  · exact T.fixedAssignment_finiteEdges_subset_closed F.outside A.assignment he

/-- A finite assigned edge has an actual incoming outside row edge at its
head. This follows from terminal legality and absorption, not word syntax. -/
theorem finiteEdge_head_hasIncoming_outside (A : ClassifiedFixedOutsideAssignment T F)
    {s t : V} (hst : (s, t) ∈ A.assignment.toCompressed.finiteEdges) :
    ∃ y, (y, t) ∈ outsideFamilyEdges T.interval.ambientInterval R.closedSet := by
  obtain ⟨u, hut, _hus⟩ := hst
  have ht := A.assignment.finite_terminal u hut
  have htX := T.finite_terminal_mem_closedSet F.outside ht.1 ht.2
  have htCut := ht.1
  rw [F.outside.terminalFrontier_eq] at htCut
  rcases htCut with htCut | htCut
  · exact htCut.2
  · exact False.elim (htCut.2.1 htX)

/-- Every selected source in the actual closed set has an outgoing outside
row edge, even when its selected occurrence is infinite. -/
theorem source_hasOutgoing_outside (_A : ClassifiedFixedOutsideAssignment T F)
    (s : Source F.outside.holes (outsideReference T.intervalReference R.closedSet)) :
    ∃ y, (s.1, y) ∈ outsideFamilyEdges T.interval.ambientInterval R.closedSet := by
  rcases s with ⟨s, hs⟩
  have hsX := T.uncovered_initials_subset_closedSet F.outside hs
  have hsCut := hs.1
  rw [F.outside.initialSet_eq] at hsCut
  rcases hsCut with hsCut | hsCut
  · exact hsCut.2
  · exact False.elim (hsCut.2.1 hsX)

theorem inside_finiteEdge_no_common_head (A : ClassifiedFixedOutsideAssignment T F)
    {a b t : V}
    (hat : (a, t) ∈ sourceInsideEdges T.interval.ambientInterval R.closedSet)
    (hbt : (b, t) ∈ A.assignment.toCompressed.finiteEdges) : False := by
  obtain ⟨y, hyt⟩ := A.finiteEdge_head_hasIncoming_outside hbt
  have hay : a = y :=
    (IsWarp.familyEdges_biUnique T.interval.ambientInterval_linkage.isWarp).1 hat.1 hyt.1
  exact hyt.2 ⟨hay ▸ hat.2.1, hat.2.2⟩

theorem inside_finiteEdge_no_common_tail (A : ClassifiedFixedOutsideAssignment T F)
    {s a b : V}
    (hsa : (s, a) ∈ sourceInsideEdges T.interval.ambientInterval R.closedSet)
    (hsb : (s, b) ∈ A.assignment.toCompressed.finiteEdges) : False := by
  obtain ⟨u, _hub, hus⟩ := hsb
  obtain ⟨y, huy⟩ := A.source_hasOutgoing_outside u
  rw [hus] at huy
  have hay : a = y :=
    (IsWarp.familyEdges_biUnique T.interval.ambientInterval_linkage.isWarp).2 hsa.1 huy.1
  exact huy.2 ⟨hsa.2.1, hay ▸ hsa.2.2⟩

/-- Both uniqueness directions hold for the literal union. This theorem
does not infer acyclicity from biuniqueness. -/
theorem closedEdges_biUnique (A : ClassifiedFixedOutsideAssignment T F) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ A.closedEdges) := by
  have hrow := IsWarp.familyEdges_biUnique T.interval.ambientInterval_linkage.isWarp
  have hfinite := A.assignment.toCompressed.finiteEdges_biUnique
  constructor
  · intro x w y hxy hwy
    rcases hxy with hxy | hxy <;> rcases hwy with hwy | hwy
    · exact hrow.1 hxy.1 hwy.1
    · exact False.elim (A.inside_finiteEdge_no_common_head hxy hwy)
    · exact False.elim (A.inside_finiteEdge_no_common_head hwy hxy)
    · exact hfinite.1 hxy hwy
  · intro x y w hxy hxw
    rcases hxy with hxy | hxy <;> rcases hxw with hxw | hxw
    · exact hrow.2 hxy.1 hxw.1
    · exact False.elim (A.inside_finiteEdge_no_common_tail hxy hxw)
    · exact False.elim (A.inside_finiteEdge_no_common_tail hxw hxy)
    · exact hfinite.2 hxy hxw

theorem noIncoming_of_original_initial (A : ClassifiedFixedOutsideAssignment T F)
    {x : V} (hx : x ∈ Gamma.initialSet T.interval.ambientInterval) :
    ¬HasIncoming A.closedEdges x := by
  rintro ⟨y, hxy | hxy⟩
  · exact isWarp_noIncoming_familyEdges_of_mem_initialSet
      T.interval.ambientInterval_linkage.isWarp hx ⟨y, hxy.1⟩
  · obtain ⟨w, hwx⟩ := A.finiteEdge_head_hasIncoming_outside hxy
    exact isWarp_noIncoming_familyEdges_of_mem_initialSet
      T.interval.ambientInterval_linkage.isWarp hx ⟨w, hwx.1⟩

/-- No unexplained sink is lost: it is persistent, an infinite assigned
source, or has the closed limiting owner supplied by that assignment. -/
theorem sink_popular_or_closedOwner (A : ClassifiedFixedOutsideAssignment T F)
    {x : V} (hx : x ∈ sourceInsideCarrier T.interval.ambientInterval R.closedSet)
    (hsink : ¬HasOutgoing A.closedEdges x) :
    ColouredSafeShortcutGraph.IsPopular C.ladder.limitWarp C.persistent kappa x ∨
      ∃ p ∈ C.ladder.limitWarp, x ∈ p.support ∧ p.support ⊆ R.closedSet := by
  by_cases ht : x ∈ Gamma.terminalFrontier T.interval.ambientInterval
  · left
    left
    have hxFrontier := T.interval.ambientInterval_linkage.terminalFrontier_subset ht
    exact (R.frontier_inter ▸ (show x ∈
      R.closedSet ∩ C.ladder.frontier R.later.stage from ⟨hx.2, hxFrontier⟩)).2
  have hout : ∃ y, (x, y) ∈ familyEdges T.interval.ambientInterval := by
    by_contra hnone
    apply ht
    rw [isWarp_terminalFrontier_eq_noOutgoing T.interval.ambientInterval_linkage.isWarp]
    exact ⟨hx.1, hnone⟩
  obtain ⟨y, hxy⟩ := hout
  have hyNotX : y ∉ R.closedSet := by
    intro hyX
    exact hsink ⟨y, Or.inl ⟨hxy, hx.2, hyX⟩⟩
  have hxHole : x ∈ Gamma.initialSet F.outside.holes.paths := by
    rw [F.outside.initialSet_eq]
    exact Or.inl ⟨hx.2, y, hxy, fun hboth ↦ hyNotX hboth.2⟩
  have hxOff : x ∉ Gamma.initialSet
      (outsideReference T.intervalReference R.closedSet) := by
    rintro ⟨p, hp, hpx⟩
    exact Set.disjoint_left.mp hp.2 (hpx ▸ p.initial_mem_support) hx.2
  let s : Source F.outside.holes (outsideReference T.intervalReference R.closedSet) :=
    ⟨x, hxHole, hxOff⟩
  cases hs : (A.assignment.assigned s).terminal? with
  | none => exact A.infinite_classification s hs
  | some t => exact False.elim (hsink ⟨t, Or.inr ⟨s, hs, rfl⟩⟩)

#print axioms closedEdges_biUnique
#print axioms noIncoming_of_original_initial
#print axioms sink_popular_or_closedOwner

end StagePostClosureIntervalTransaction.ClassifiedFixedOutsideAssignment

end Erdos599.Blueprint.LinkageBlueprint

