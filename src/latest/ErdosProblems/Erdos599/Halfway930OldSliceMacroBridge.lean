/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayOldSliceTailIncidence

/-!
# The complete local old-slice macro branch

This file packages the part of Assertions 9.30--9.31 which is genuinely
available at one fixed pair of club stages.  A scheduled real terminal which
already belongs to the old frontier is cut locally, an honest old-to-new
interval is selected, its joint seed is closed, and the resulting pruned row
is compiled into the canonical macro relation.

Only the first-hit front belongs to this local relation.  The suffix from the
later frontier to the ambient target is retained as external data.  In
particular this interface does not put that suffix into the roofed carrier and
does not claim that the incoming blueprint's unrelated real edges belong to
the interval row.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- The fully chosen local old-slice transaction, including its canonical
inside macro relation. -/
structure ClosedOldSlice930MacroTransaction
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma C.selectedReference kappa)
    (u : V) where
  intervalTransaction : OldSlice930IntervalTransaction C W u
  macroTransaction : OldSliceMacroTransaction intervalTransaction

/-- The identity branch at an old-frontier real terminal is unconditional
from the two induction hypotheses and the concrete club geometry. -/
theorem exists_closedOldSlice930MacroTransaction
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma C.selectedReference kappa)
    {u : V}
    (hlower : CardinalInduction.UniversalCardinalInductionBelow V kappa)
    (hext : CardinalInduction.UniversalExtensionClauseAt V kappa)
    (hW : W.IsLinkageBlueprint C.oldSlice C.oldClosedSet C.persistent)
    (hu : u ∈ W.realPart.terminals) (huOld : u ∈ C.oldSlice)
    (hbefore : C.before ⊆ C.outerRoof)
    (href : ∀ p ∈ C.selectedReference, p.support ⊆ C.outerRoof)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    Nonempty (ClosedOldSlice930MacroTransaction C W u) := by
  obtain ⟨P⟩ := exists_oldSlice930IntervalTransaction C W hlower hext hW
    hu huOld hbefore href hSafeRoof
  exact ⟨{
    intervalTransaction := P
    macroTransaction := (OldSliceMacroTransaction.exists_macroTransaction P).some }⟩

namespace ClosedOldSlice930MacroTransaction

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {W : LinkageBlueprint Gamma C.selectedReference kappa}
variable {u : V}

/-- The Assertion 9.30 cut separately retains every incoming real edge.
This fact is deliberately not folded into the interval macro relation: the
joint-survivor theorem must still prove that the two relations are compatible. -/
theorem old_realEdges_subset_cut
    (Q : ClosedOldSlice930MacroTransaction C W u) :
    W.realPart.edges ⊆ Q.intervalTransaction.cut.realPart.edges :=
  Q.intervalTransaction.continuation.real_extends_to_endpoint.realEdges_mono

/-- Apart from the scheduled endpoint, every incoming real terminal survives
the Assertion 9.30 cut. -/
theorem preserves_other_realTerminals_in_cut
    (Q : ClosedOldSlice930MacroTransaction C W u) :
    W.realPart.terminals \ {u} ⊆
      Q.intervalTransaction.cut.realPart.terminals :=
  Q.intervalTransaction.continuation.preserves_other_terminals

/-- Every vertex of the selected first-hit front is in the actual canonical
inside carrier. -/
theorem front_support_subset_carrier
    (Q : ClosedOldSlice930MacroTransaction C W u) :
    Q.intervalTransaction.interval.front.support ⊆
      Q.macroTransaction.inside.insideFamily.vertexSet := by
  intro x hx
  rw [Q.macroTransaction.inside.vertexSet_eq]
  exact Or.inl (Or.inl ⟨
    Q.intervalTransaction.interval.front_support_subset_splicedIntervalRow hx,
    Q.intervalTransaction.closed.front_support_subset hx⟩)

/-- Every edge of the selected first-hit front survives literally in the
local macro relation. -/
theorem front_edgeSet_subset_macroEdge
    (Q : ClosedOldSlice930MacroTransaction C W u) :
    Q.intervalTransaction.interval.front.edgeSet ⊆
      Q.macroTransaction.macroEdge := by
  intro e he
  apply Or.inl
  rw [Q.macroTransaction.inside.edgeSet_eq]
  have hend :=
    Q.intervalTransaction.interval.front.edgeSet_subset_support_prod he
  exact ⟨Q.intervalTransaction.interval.front_edgeSet_subset_splicedIntervalRow he,
    Q.intervalTransaction.closed.front_support_subset hend.1,
    Q.intervalTransaction.closed.front_support_subset hend.2⟩

/-- The selected front is an original-web route in the real part of the
local macro relation. -/
theorem front_edgeSet_subset_realMacroEdge
    (Q : ClosedOldSlice930MacroTransaction C W u) :
    Q.intervalTransaction.interval.front.edgeSet ⊆
      relationRealEdges (Gamma := Gamma) Q.macroTransaction.macroEdge := by
  intro e he
  exact ⟨Q.front_edgeSet_subset_macroEdge he,
    Q.intervalTransaction.interval.front.edgeSet_subset_adj he⟩

/-- The local macro carrier is the actual bounded, roofed closed carrier. -/
theorem carrier_subset_closedSet
    (Q : ClosedOldSlice930MacroTransaction C W u) :
    Q.macroTransaction.inside.insideFamily.vertexSet ⊆
      Q.intervalTransaction.closed.closedSet :=
  Q.macroTransaction.carrier_subset_closedSet

theorem carrier_subset_outerRoof
    (Q : ClosedOldSlice930MacroTransaction C W u) :
    Q.macroTransaction.inside.insideFamily.vertexSet ⊆ C.outerRoof :=
  Q.macroTransaction.carrier_subset_outerRoof

theorem mk_carrier_le
    (Q : ClosedOldSlice930MacroTransaction C W u) :
    #Q.macroTransaction.inside.insideFamily.vertexSet ≤ kappa :=
  Q.macroTransaction.mk_carrier_le

/-- The local front relation already has the complete finite-stage geometry
needed by a joint survivor: bi-uniqueness, a strict rank, its later-frontier
sink boundary, and absence of a forward ray. -/
theorem macroEdge_biUnique
    (Q : ClosedOldSlice930MacroTransaction C W u) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ Q.macroTransaction.macroEdge) :=
  Q.macroTransaction.macroEdge_biUnique

theorem macroEdge_rank
    (Q : ClosedOldSlice930MacroTransaction C W u) {x y : V}
    (hxy : (x, y) ∈ Q.macroTransaction.macroEdge) :
    laterRowRank Q.intervalTransaction.interval.splicedIntervalRow
        Q.intervalTransaction.interval.splicedIntervalRow_tight.1.isWarp x <
      laterRowRank Q.intervalTransaction.interval.splicedIntervalRow
        Q.intervalTransaction.interval.splicedIntervalRow_tight.1.isWarp y :=
  Q.macroTransaction.macroEdge_rank hxy

theorem sink_subset_newSlice
    (Q : ClosedOldSlice930MacroTransaction C W u) :
    {x | x ∈ Q.macroTransaction.inside.insideFamily.vertexSet ∧
      ¬ ∃ y, (x, y) ∈ Q.macroTransaction.macroEdge} ⊆ C.newSlice :=
  Q.macroTransaction.sink_subset_newSlice

theorem no_directedRay
    (Q : ClosedOldSlice930MacroTransaction C W u) :
    ¬ ContainsDirectedRay Q.macroTransaction.macroEdge :=
  Q.macroTransaction.no_directedRay

/-- The local route begins at the scheduled old-frontier vertex. -/
theorem front_start
    (Q : ClosedOldSlice930MacroTransaction C W u) :
    Q.intervalTransaction.interval.front.start = u :=
  Q.intervalTransaction.interval.front_start

/-- Its endpoint belongs to the later club frontier. -/
theorem front_finish
    (Q : ClosedOldSlice930MacroTransaction C W u) :
    Q.intervalTransaction.interval.front.finish ∈ C.newSlice :=
  Q.intervalTransaction.interval.front_finish_mem

/-- The ambient suffix begins exactly at the local frontier endpoint and
ends in the original target. -/
theorem tail_boundary
    (Q : ClosedOldSlice930MacroTransaction C W u) :
    Q.intervalTransaction.interval.tail.start =
        Q.intervalTransaction.interval.front.finish ∧
      Q.intervalTransaction.interval.tail.finish ∈ Gamma.target := by
  exact ⟨Q.intervalTransaction.interval.tail_start,
    Q.intervalTransaction.interval.tail_boundary.2⟩

/-- The retained local front and external suffix are still the literal
deletion-safe target path selected at the old stage. -/
theorem front_append_tail
    (Q : ClosedOldSlice930MacroTransaction C W u) :
    Q.intervalTransaction.interval.front.appendFinite
        Q.intervalTransaction.interval.tail
        Q.intervalTransaction.interval.tail_start
        Q.intervalTransaction.interval.front_tail_inter.subset =
      Q.intervalTransaction.interval.path :=
  Q.intervalTransaction.interval.splice_eq

/-- Before any joint survivor is formed, the honest roofed interval row and
the external target suffix have exactly their intended single contact. -/
theorem splicedIntervalRow_tail_inter
    (Q : ClosedOldSlice930MacroTransaction C W u) :
    Gamma.vertexSet Q.intervalTransaction.interval.splicedIntervalRow ∩
        Q.intervalTransaction.interval.tail.support =
      {Q.intervalTransaction.interval.tail.start} :=
  Q.intervalTransaction.interval.splicedIntervalRow_tail_inter

/-- The relation compiler uses only the canonical inside carrier.  It too
meets the external suffix exactly at the splice vertex, even though the
larger auxiliary closed set need not avoid that suffix. -/
theorem macroCarrier_tail_inter
    (Q : ClosedOldSlice930MacroTransaction C W u) :
    Q.macroTransaction.inside.insideFamily.vertexSet ∩
        Q.intervalTransaction.interval.tail.support =
      {Q.intervalTransaction.interval.tail.start} :=
  Q.macroTransaction.inside_vertexSet_tail_inter

/-- Every old-roof contact of the retained ambient suffix is the splice
vertex.  This is the incidence fact needed when the incoming old-stage
blueprint, rather than only the canonical interval row, is retained by the
diamond advance. -/
theorem oldRoof_tail_inter_subset
    (Q : ClosedOldSlice930MacroTransaction C W u) :
    Gamma.roof C.oldSlice ∩
        Q.intervalTransaction.interval.tail.support ⊆
      {Q.intervalTransaction.interval.tail.start} := by
  intro x hx
  let T := Q.intervalTransaction.interval
  have hxPath : x ∈ T.path.support :=
    T.tail_support_subset_path hx.2
  have hpathLift := T.path_mem_safe
  rw [T.safe.ambient_eq_lift] at hpathLift
  obtain ⟨q, hq, hqeq⟩ := hpathLift
  have hxLift : x ∈
      (C.ladder.liftStagePath C.oldStage q).support := by
    rw [hqeq]
    exact hxPath
  have hxRawRoof : x ∈ Gamma.roof
      (Gamma.terminalFrontier (C.ladder.warpAt C.oldStage)) := by
    rw [← Gamma.roof_essential,
      ← C.ladder.frontier_eq_essential_terminalFrontier
        C.legal.roofsSourceAtStages C.oldStage]
    exact hx.1
  have hxInitial : x = T.path.start := by
    by_contra hxne
    have hxneQ : x ≠ q.initial := by
      intro hxeq
      apply hxne
      calc
        x = q.initial := hxeq
        _ = (C.ladder.liftStagePath C.oldStage q).initial :=
          (C.ladder.initial_liftStagePath C.oldStage q).symm
        _ = T.path.start := congrArg DirectedPath.Path.initial hqeq
    exact (C.ladder.liftStagePath_not_mem_roof_of_ne_initial
      C.oldStage q hxLift hxneQ) hxRawRoof
  have hxFront : x ∈ T.front.support := by
    have hpathFrontInitial : T.path.start = T.front.start :=
      T.path_start.trans T.front_start.symm
    rw [hxInitial, hpathFrontInitial]
    exact T.front.start_mem_support
  have hxInter : x ∈ T.front.support ∩ T.tail.support :=
    ⟨hxFront, hx.2⟩
  rw [T.front_tail_inter] at hxInter
  simpa only [← T.tail_start] using hxInter

/-- The splice vertex is a terminal of the honest stopped row. -/
theorem front_finish_mem_splicedIntervalRow_terminalFrontier
    (Q : ClosedOldSlice930MacroTransaction C W u) :
    Q.intervalTransaction.interval.front.finish ∈
      Gamma.terminalFrontier
        Q.intervalTransaction.interval.splicedIntervalRow := by
  rw [Q.intervalTransaction.interval.terminalFrontier_splicedIntervalRow]
  exact ⟨Sum.inl Q.intervalTransaction.interval.front,
    Q.intervalTransaction.interval.front_mem_interval, rfl⟩

/-- Hence no local macro edge leaves the point at which the external suffix
is attached. -/
theorem no_macroEdge_from_front_finish
    (Q : ClosedOldSlice930MacroTransaction C W u) :
    ¬ ∃ y, (Q.intervalTransaction.interval.front.finish, y) ∈
      Q.macroTransaction.macroEdge := by
  rintro ⟨y, hy⟩
  have hyRow :
      (Q.intervalTransaction.interval.front.finish, y) ∈
        familyEdges Q.intervalTransaction.interval.splicedIntervalRow := by
    rw [Q.macroTransaction.macroEdge_eq_inside,
      Q.macroTransaction.inside.edgeSet_eq] at hy
    exact hy.1
  have hterminal := Q.front_finish_mem_splicedIntervalRow_terminalFrontier
  rw [terminalFrontier_eq_vertexSet_diff_hasOutgoing
      Q.intervalTransaction.interval.splicedIntervalRow_tight.1.isWarp
      Q.intervalTransaction.interval.splicedIntervalRow_tight.1.finiteCharacter]
      at hterminal
  exact hterminal.2 ⟨y, hyRow⟩

/-- The first honest relation which includes the post-frontier target suffix.
It is intentionally not claimed to be contained in `C.outerRoof`. -/
def macroTailEdge (Q : ClosedOldSlice930MacroTransaction C W u) :
    Set (V × V) :=
  Q.macroTransaction.macroEdge ∪
    Q.intervalTransaction.interval.tail.edgeSet

/-- Carrier of the honest front-plus-target-suffix relation. -/
def macroTailCarrier (Q : ClosedOldSlice930MacroTransaction C W u) : Set V :=
  Q.macroTransaction.inside.insideFamily.vertexSet ∪
    Q.intervalTransaction.interval.tail.support

/-- The local macro relation and the external suffix form a bi-unique
relation.  Exact one-point carrier incidence handles incoming collisions;
the stopped-row terminal property handles outgoing collisions. -/
theorem macroTailEdge_biUnique
    (Q : ClosedOldSlice930MacroTransaction C W u) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ Q.macroTailEdge) := by
  apply biUnique_union_of_cross Q.macroEdge_biUnique
    (Alternating.FinitePath.edgeSet_biUnique
      Q.intervalTransaction.interval.tail)
  · intro x y z hxz hyz
    have hzInside : z ∈
        Q.macroTransaction.inside.insideFamily.vertexSet := by
      rw [Q.macroTransaction.macroEdge_eq_inside] at hxz
      exact (edgeSet_endpoints_mem_vertexSet
        Q.macroTransaction.inside.insideFamily hxz).2
    have hzTail : z ∈ Q.intervalTransaction.interval.tail.support :=
      (Q.intervalTransaction.interval.tail.edgeSet_subset_support_prod hyz).2
    have hzContact : z ∈
        Q.macroTransaction.inside.insideFamily.vertexSet ∩
          Q.intervalTransaction.interval.tail.support :=
      ⟨hzInside, hzTail⟩
    rw [Q.macroCarrier_tail_inter] at hzContact
    have hz : z = Q.intervalTransaction.interval.tail.start := by
      exact Set.mem_singleton_iff.1 hzContact
    exact False.elim
      (Alternating.FinitePath.no_incoming_edge_at_start
        Q.intervalTransaction.interval.tail y (hz ▸ hyz))
  · intro x y z hxy hxz
    have hxInside : x ∈
        Q.macroTransaction.inside.insideFamily.vertexSet := by
      rw [Q.macroTransaction.macroEdge_eq_inside] at hxy
      exact (edgeSet_endpoints_mem_vertexSet
        Q.macroTransaction.inside.insideFamily hxy).1
    have hxTail : x ∈ Q.intervalTransaction.interval.tail.support :=
      (Q.intervalTransaction.interval.tail.edgeSet_subset_support_prod hxz).1
    have hxContact : x ∈
        Q.macroTransaction.inside.insideFamily.vertexSet ∩
          Q.intervalTransaction.interval.tail.support :=
      ⟨hxInside, hxTail⟩
    rw [Q.macroCarrier_tail_inter] at hxContact
    have hx : x = Q.intervalTransaction.interval.tail.start := by
      exact Set.mem_singleton_iff.1 hxContact
    apply False.elim
    apply Q.no_macroEdge_from_front_finish
    refine ⟨y, ?_⟩
    rw [← Q.intervalTransaction.interval.tail_start, ← hx]
    exact hxy

/-- Every edge of the augmented relation is an original-web edge. -/
theorem macroTailEdge_real
    (Q : ClosedOldSlice930MacroTransaction C W u) :
    Q.macroTailEdge ⊆ {e | Gamma.graph.Adj e.1 e.2} := by
  intro e he
  rcases he with heMacro | heTail
  · rw [Q.macroTransaction.macroEdge_eq_inside,
      Q.macroTransaction.inside.edgeSet_eq] at heMacro
    exact familyEdges_subset_adj
      Q.intervalTransaction.interval.splicedIntervalRow heMacro.1
  · exact Q.intervalTransaction.interval.tail.edgeSet_subset_adj heTail

/-- The explicit carrier contains both endpoints of every augmented edge. -/
theorem macroTailEdge_endpoints
    (Q : ClosedOldSlice930MacroTransaction C W u) {e : V × V}
    (he : e ∈ Q.macroTailEdge) :
    e.1 ∈ Q.macroTailCarrier ∧ e.2 ∈ Q.macroTailCarrier := by
  rcases he with heMacro | heTail
  · rw [Q.macroTransaction.macroEdge_eq_inside] at heMacro
    have hend := edgeSet_endpoints_mem_vertexSet
      Q.macroTransaction.inside.insideFamily heMacro
    exact ⟨Or.inl hend.1, Or.inl hend.2⟩
  · have hend :=
      Q.intervalTransaction.interval.tail.edgeSet_subset_support_prod heTail
    exact ⟨Or.inr hend.1, Or.inr hend.2⟩

/-- Extend the stopped-row rank along the ordered external target suffix.
The two formulas agree at the unique common vertex because the suffix starts
at position zero. -/
noncomputable def macroTailRank
    (Q : ClosedOldSlice930MacroTransaction C W u) (x : V) : Nat := by
  classical
  exact
    if x ∈ Q.intervalTransaction.interval.tail.support then
      laterRowRank Q.intervalTransaction.interval.splicedIntervalRow
          Q.intervalTransaction.interval.splicedIntervalRow_tight.1.isWarp
          Q.intervalTransaction.interval.tail.start +
        Q.intervalTransaction.interval.tail.walk.support.idxOf x
    else
      laterRowRank Q.intervalTransaction.interval.splicedIntervalRow
        Q.intervalTransaction.interval.splicedIntervalRow_tight.1.isWarp x

private theorem tail_start_idxOf [DecidableEq V]
    (Q : ClosedOldSlice930MacroTransaction C W u) :
    Q.intervalTransaction.interval.tail.walk.support.idxOf
        Q.intervalTransaction.interval.tail.start = 0 := by
  classical
  let p := Q.intervalTransaction.interval.tail
  calc
    p.walk.support.idxOf p.start =
        p.walk.support.idxOf
          (p.walk.support[0]'p.support_length_pos) := by
      rw [p.support_getElem_zero]
    _ = 0 := by rw [p.isPath.idxOf_getElem]

/-- The augmented rank strictly increases on both the stopped macro relation
and the external suffix. -/
theorem macroTailRank_strict
    (Q : ClosedOldSlice930MacroTransaction C W u) {x y : V}
    (hxy : (x, y) ∈ Q.macroTailEdge) :
    Q.macroTailRank x < Q.macroTailRank y := by
  classical
  rcases hxy with hxyMacro | hxyTail
  · have hend : x ∈ Q.macroTransaction.inside.insideFamily.vertexSet ∧
        y ∈ Q.macroTransaction.inside.insideFamily.vertexSet := by
      rw [Q.macroTransaction.macroEdge_eq_inside] at hxyMacro
      exact edgeSet_endpoints_mem_vertexSet
        Q.macroTransaction.inside.insideFamily hxyMacro
    have hxNotTail : x ∉ Q.intervalTransaction.interval.tail.support := by
      intro hxTail
      have hxContact : x ∈
          Q.macroTransaction.inside.insideFamily.vertexSet ∩
            Q.intervalTransaction.interval.tail.support :=
        ⟨hend.1, hxTail⟩
      rw [Q.macroCarrier_tail_inter] at hxContact
      have hxeq : x = Q.intervalTransaction.interval.tail.start :=
        Set.mem_singleton_iff.1 hxContact
      apply Q.no_macroEdge_from_front_finish
      refine ⟨y, ?_⟩
      rw [← Q.intervalTransaction.interval.tail_start, ← hxeq]
      exact hxyMacro
    by_cases hyTail : y ∈ Q.intervalTransaction.interval.tail.support
    · have hyContact : y ∈
          Q.macroTransaction.inside.insideFamily.vertexSet ∩
            Q.intervalTransaction.interval.tail.support :=
        ⟨hend.2, hyTail⟩
      rw [Q.macroCarrier_tail_inter] at hyContact
      have hyeq : y = Q.intervalTransaction.interval.tail.start :=
        Set.mem_singleton_iff.1 hyContact
      have hrank := Q.macroEdge_rank hxyMacro
      rw [macroTailRank, if_neg hxNotTail, macroTailRank, if_pos hyTail,
        hyeq, Q.tail_start_idxOf, Nat.add_zero]
      simpa only [hyeq] using hrank
    · simpa only [macroTailRank, if_neg hxNotTail, if_neg hyTail] using
        Q.macroEdge_rank hxyMacro
  · have hend :=
      Q.intervalTransaction.interval.tail.edgeSet_subset_support_prod hxyTail
    have hidx := Alternating.Walk.idxOf_target_eq_source_add_one
      Q.intervalTransaction.interval.tail.walk
      Q.intervalTransaction.interval.tail.isPath hxyTail
    simp only [macroTailRank, if_pos hend.1, if_pos hend.2]
    omega

/-- The honest front-plus-target-suffix relation has no directed cycle. -/
theorem macroTailEdge_noDirectedCycle
    (Q : ClosedOldSlice930MacroTransaction C W u) :
    ¬ ContainsDirectedCycle Q.macroTailEdge :=
  not_containsDirectedCycle_of_rank Q.macroTailEdge Q.macroTailRank
    Q.macroTailRank_strict

/-- The honest front-plus-target-suffix relation has no reverse directed
ray. -/
theorem macroTailEdge_noReverseDirectedRay
    (Q : ClosedOldSlice930MacroTransaction C W u) :
    ¬ ContainsReverseDirectedRay Q.macroTailEdge :=
  not_containsReverseDirectedRay_of_rank Q.macroTailEdge Q.macroTailRank
    Q.macroTailRank_strict

/-- Every edge of the original deletion-safe target path now occurs in the
honest front-plus-external-tail relation. -/
theorem targetPath_edgeSet_subset_macroTailEdge
    (Q : ClosedOldSlice930MacroTransaction C W u) :
    Q.intervalTransaction.interval.path.edgeSet ⊆ Q.macroTailEdge := by
  rw [← Q.front_append_tail, FinitePath.edgeSet_appendFinite]
  intro e he
  exact he.elim (fun h ↦ Or.inl (Q.front_edgeSet_subset_macroEdge h)) Or.inr

/-- The whole retained deletion-safe target path is carried by the augmented
front-plus-tail relation. -/
theorem targetPath_support_subset_macroTailCarrier
    (Q : ClosedOldSlice930MacroTransaction C W u) :
    Q.intervalTransaction.interval.path.support ⊆ Q.macroTailCarrier := by
  rw [← Q.front_append_tail, FinitePath.support_appendFinite_eq_union]
  intro x hx
  exact hx.elim (fun h ↦ Or.inl (Q.front_support_subset_carrier h)) Or.inr

theorem targetPath_boundary
    (Q : ClosedOldSlice930MacroTransaction C W u) :
    Q.intervalTransaction.interval.path.start = u ∧
      Q.intervalTransaction.interval.path.finish ∈ Gamma.target :=
  ⟨Q.intervalTransaction.interval.path_start,
    Q.intervalTransaction.interval.path_finish⟩

end ClosedOldSlice930MacroTransaction

#print axioms exists_closedOldSlice930MacroTransaction
#print axioms ClosedOldSlice930MacroTransaction.front_edgeSet_subset_realMacroEdge
#print axioms ClosedOldSlice930MacroTransaction.macroTailRank_strict
#print axioms ClosedOldSlice930MacroTransaction.macroTailEdge_noDirectedCycle

end LinkageBlueprint
end Blueprint
end Erdos599
