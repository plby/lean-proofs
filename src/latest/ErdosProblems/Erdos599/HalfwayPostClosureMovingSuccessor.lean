/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.MovingAdvance931Compiler
import ErdosProblems.Erdos599.MovingSchedulerSuccessor

/-!
# Compiling one concrete post-closure relation to an indexed successor

The classified contact construction ultimately produces one relation and
one carrier.  `AdvanceSpliceRelation` already stores all six linkage-
blueprint conditions, the exact real target path, preservation of old real
terminals, and the relation-level form of (9.32).  The one additional fact
needed by the fair relation limit is only source-faithful root preservation:
old nonroots are automatic from retained edges and bi-uniqueness.

This file is deliberately a one-transaction adapter.  It introduces no
universal compiler or scheduler premise.
-/

noncomputable section

open Cardinal Set

namespace Erdos599.Blueprint.LinkageBlueprint

universe u w

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}} {persistent B : Set V}

/-- Retaining all old edges in a bi-unique relation reduces full
old-carrier predecessor preservation to the genuine root condition.  A
noninitial old vertex already has an old incoming edge, and left uniqueness
forces any proposed new incoming edge to be that same edge. -/
theorem noIncomingOld_of_oldEdges_biunique_of_initialsRemainRoots
    (current : LinkageBlueprint Gamma Y kappa) (E : Set (V × V))
    (hold : current.edgeSet ⊆ E)
    (hbiunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E))
    (hroots : ∀ x ∈ current.initialSet, ¬ ∃ y, (y, x) ∈ E) :
    ∀ {x y : V}, x ∈ current.vertexSet →
      (y, x) ∈ E → (y, x) ∉ current.edgeSet → False := by
  intro x y hx hyx hyxOld
  by_cases hxInitial : x ∈ current.initialSet
  · exact hroots x hxInitial ⟨y, hyx⟩
  · obtain ⟨p, hpCurrent, hxp⟩ := hx
    have hxNe : x ≠ p.initial := by
      intro hxInitialValue
      exact hxInitial ⟨p, hpCurrent, hxInitialValue.symm⟩
    obtain ⟨z, hzxPath⟩ : ∃ z, (z, x) ∈ p.edgeSet := by
      rcases p with p | r
      · exact Alternating.FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
          p hxp hxNe
      · obtain ⟨n, hn⟩ := hxp
        have hnpos : 0 < n := by
          by_contra hnpos
          have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnpos
          apply hxNe
          simpa only [DirectedPath.Path.initial,
            DirectedPath.Ray.initial, hnzero] using hn.symm
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
          (Nat.ne_of_gt hnpos)
        exact ⟨r m, ⟨m, Prod.ext rfl hn.symm⟩⟩
    have hzxOld : (z, x) ∈ current.edgeSet :=
      Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨hpCurrent, hzxPath⟩⟩
    have hzy : z = y := hbiunique.1 (hold hzxOld) hyx
    exact hyxOld (by simpa only [hzy] using hzxOld)

/-- Every old root which is an ambient source remains a root of the concrete
relation.  The reference-remainder alternative in the source-cover clause is
impossible because every old vertex belongs to the new carrier, whereas a
retained reference member is required to avoid that carrier. -/
theorem AdvanceSpliceRelation.sourceInitialRemainsRoot
    {ancestor current : LinkageBlueprint Gamma Y kappa}
    {z : V} {T Z : Set V}
    (R : AdvanceSpliceRelation ancestor current z T Z persistent B)
    {x : V} (hxInitial : x ∈ current.initialSet)
    (hxSource : x ∈ Gamma.source) :
    ¬ ∃ y, (y, x) ∈ R.edge := by
  have hxCurrent : x ∈ current.vertexSet := by
    obtain ⟨p, hp, hpInitial⟩ := hxInitial
    exact ⟨p, hp, hpInitial.symm ▸ p.initial_mem_support⟩
  rcases R.covers_source hxSource with hxRoot | hxReference
  · exact hxRoot.2
  · obtain ⟨p, hpReference, hpInitial⟩ := hxReference
    exfalso
    apply hpReference.2
    refine ⟨hpReference.1.1, x, ?_, R.old_vertices hxCurrent⟩
    exact hpInitial.symm ▸ p.initial_mem_support

/-- Therefore the construction-specific incidence proof is needed only for
old roots outside the ambient source.  Those are precisely the extra roots
which can be exposed by the preceding 9.30 cut. -/
theorem AdvanceSpliceRelation.initialsRemainRoots_of_nonSourceInitialsRemainRoots
    {ancestor current : LinkageBlueprint Gamma Y kappa}
    {z : V} {T Z : Set V}
    (R : AdvanceSpliceRelation ancestor current z T Z persistent B)
    (hnonSource : ∀ x ∈ current.initialSet, x ∉ Gamma.source →
      ¬ ∃ y, (y, x) ∈ R.edge) :
    ∀ x ∈ current.initialSet, ¬ ∃ y, (y, x) ∈ R.edge := by
  intro x hxInitial
  by_cases hxSource : x ∈ Gamma.source
  · exact R.sourceInitialRemainsRoot hxInitial hxSource
  · exact hnonSource x hxInitial hxSource

/-- In the source-rooted case no additional incidence proof is needed. -/
theorem AdvanceSpliceRelation.initialsRemainRoots_of_initialSet_subset_source
    {ancestor current : LinkageBlueprint Gamma Y kappa}
    {z : V} {T Z : Set V}
    (R : AdvanceSpliceRelation ancestor current z T Z persistent B)
    (hsource : current.initialSet ⊆ Gamma.source) :
    ∀ x ∈ current.initialSet, ¬ ∃ y, (y, x) ∈ R.edge := by
  intro x hxInitial
  exact R.sourceInitialRemainsRoot hxInitial (hsource hxInitial)

/-- Full predecessor preservation follows from the exact edge realization
of the compiled relation and the construction-specific no-new-incoming
incidence theorem.  All other moving 9.31 fields are supplied by the existing
root-orbit compiler. -/
theorem AdvanceSpliceRelation.exists_fullyPredecessorPreservingMovingAdvance931_of_noIncomingOld
    {ancestor current : LinkageBlueprint Gamma Y kappa}
    {z : V} {Told Tnew Z : Set V}
    (R : AdvanceSpliceRelation ancestor current z Tnew Z persistent B)
    (hzOld : z ∈ Told)
    (hnoIncomingOld : ∀ {x y : V}, x ∈ current.vertexSet →
      (y, x) ∈ R.edge → (y, x) ∉ current.edgeSet → False) :
    ∃ U : LinkageBlueprint Gamma Y kappa,
      MovingAdvance931 ancestor current U z Told Tnew Z persistent B ∧
        current.NoNewPredecessorsTo U := by
  obtain ⟨U, hU, _hnoReal, hedge⟩ :=
    R.exists_predecessorPreservingMovingAdvance931_with_edgeSet hzOld
  refine ⟨U, hU, ?_⟩
  intro x y hx hxy
  rw [hedge] at hxy
  by_cases hcurrent : (y, x) ∈ current.edgeSet
  · exact hcurrent
  · exact False.elim (hnoIncomingOld hx hxy hcurrent)

/-- Construction-facing form: the segmented transaction need only show that
old initial vertices are still relation roots.  Retention and bi-uniqueness
are already fields of `AdvanceSpliceRelation`, so the preceding theorem
derives the full incidence statement automatically. -/
theorem AdvanceSpliceRelation.exists_fullyPredecessorPreservingMovingAdvance931_of_initialsRemainRoots
    {ancestor current : LinkageBlueprint Gamma Y kappa}
    {z : V} {Told Tnew Z : Set V}
    (R : AdvanceSpliceRelation ancestor current z Tnew Z persistent B)
    (hzOld : z ∈ Told)
    (hroots : ∀ x ∈ current.initialSet, ¬ ∃ y, (y, x) ∈ R.edge) :
    ∃ U : LinkageBlueprint Gamma Y kappa,
      MovingAdvance931 ancestor current U z Told Tnew Z persistent B ∧
        current.NoNewPredecessorsTo U := by
  apply R.exists_fullyPredecessorPreservingMovingAdvance931_of_noIncomingOld
    hzOld
  exact noIncomingOld_of_oldEdges_biunique_of_initialsRemainRoots
    current R.edge R.old_edges R.biunique hroots

/-- Preferred general construction-facing form: source roots are automatic
from the actual source-cover clause, leaving only roots exposed away from the
ambient source to the contact-incidence geometry. -/
theorem AdvanceSpliceRelation.exists_fullyPredecessorPreservingMovingAdvance931_of_nonSourceRoots
    {ancestor current : LinkageBlueprint Gamma Y kappa}
    {z : V} {Told Tnew Z : Set V}
    (R : AdvanceSpliceRelation ancestor current z Tnew Z persistent B)
    (hzOld : z ∈ Told)
    (hnonSource : ∀ x ∈ current.initialSet, x ∉ Gamma.source →
      ¬ ∃ y, (y, x) ∈ R.edge) :
    ∃ U : LinkageBlueprint Gamma Y kappa,
      MovingAdvance931 ancestor current U z Told Tnew Z persistent B ∧
        current.NoNewPredecessorsTo U := by
  apply R.exists_fullyPredecessorPreservingMovingAdvance931_of_initialsRemainRoots
    hzOld
  exact R.initialsRemainRoots_of_nonSourceInitialsRemainRoots hnonSource

/-- Source-rooted specialization: the relation's actual source-cover field
discharges root preservation, and bi-uniqueness then handles every remaining
old vertex. -/
theorem AdvanceSpliceRelation.exists_fullyPredecessorPreservingMovingAdvance931_of_sourceRooted
    {ancestor current : LinkageBlueprint Gamma Y kappa}
    {z : V} {Told Tnew Z : Set V}
    (R : AdvanceSpliceRelation ancestor current z Tnew Z persistent B)
    (hzOld : z ∈ Told)
    (hsource : current.initialSet ⊆ Gamma.source) :
    ∃ U : LinkageBlueprint Gamma Y kappa,
      MovingAdvance931 ancestor current U z Told Tnew Z persistent B ∧
        current.NoNewPredecessorsTo U := by
  apply R.exists_fullyPredecessorPreservingMovingAdvance931_of_initialsRemainRoots
    hzOld
  exact R.initialsRemainRoots_of_initialSet_subset_source hsource

namespace IndexedTerminalResolutionState

variable {Stage : Type w} [LinearOrder Stage]
variable {slice closure : Stage → Set V}

local notation "State" => IndexedTerminalResolutionState
  (Gamma := Gamma) (Y := Y) (kappa := kappa)
  (persistent := persistent) (B := B) slice closure

/-- A concrete 9.30 continuation and a concrete classified 9.31 relation
produce the precise indexed successor datum consumed by the fair scheduler.

The 9.30 refinement remains the separate certificate proved by the cut and
continuation geometry.  The 9.31 refinement is derived here from full
old-carrier predecessor preservation, rather than postulated. -/
theorem exists_movingTerminalAdvance_of_continuation_relation
    {S : State} {u z : V}
    {cut current : LinkageBlueprint Gamma Y kappa}
    (j : Stage) (hij : S.stageIndex < j)
    (h30 : Continuation930 S.blueprint cut current u z
      (slice S.stageIndex) B)
    (h30refines : S.blueprint.PredecessorRefines current)
    (R : AdvanceSpliceRelation S.blueprint current z
      (slice j) (closure j) persistent B)
    (hnoIncomingOld : ∀ {x y : V}, x ∈ current.vertexSet →
      (y, x) ∈ R.edge → (y, x) ∉ current.edgeSet → False) :
    Nonempty (MovingTerminalAdvance S u) := by
  obtain ⟨U, h31, h31full⟩ :=
    R.exists_fullyPredecessorPreservingMovingAdvance931_of_noIncomingOld
      h30.endpoint_mem_slice hnoIncomingOld
  exact ⟨MovingTerminalAdvance.of930931 j hij h30 h31 h30refines
    h31full.predecessorRefines⟩

/-- Root-preservation form of the relation adapter.  This is the preferred
interface for the actual segmented post-closure construction. -/
theorem exists_movingTerminalAdvance_of_continuation_relation_roots
    {S : State} {u z : V}
    {cut current : LinkageBlueprint Gamma Y kappa}
    (j : Stage) (hij : S.stageIndex < j)
    (h30 : Continuation930 S.blueprint cut current u z
      (slice S.stageIndex) B)
    (h30refines : S.blueprint.PredecessorRefines current)
    (R : AdvanceSpliceRelation S.blueprint current z
      (slice j) (closure j) persistent B)
    (hroots : ∀ x ∈ current.initialSet, ¬ ∃ y, (y, x) ∈ R.edge) :
    Nonempty (MovingTerminalAdvance S u) := by
  obtain ⟨U, h31, h31full⟩ :=
    R.exists_fullyPredecessorPreservingMovingAdvance931_of_initialsRemainRoots
      h30.endpoint_mem_slice hroots
  exact ⟨MovingTerminalAdvance.of930931 j hij h30 h31 h30refines
    h31full.predecessorRefines⟩

/-- General actual-geometry form.  The relation itself protects source
roots; the caller proves only that the contact splice does not enter a
non-source root exposed by the preceding continuation. -/
theorem exists_movingTerminalAdvance_of_continuation_relation_nonSourceRoots
    {S : State} {u z : V}
    {cut current : LinkageBlueprint Gamma Y kappa}
    (j : Stage) (hij : S.stageIndex < j)
    (h30 : Continuation930 S.blueprint cut current u z
      (slice S.stageIndex) B)
    (h30refines : S.blueprint.PredecessorRefines current)
    (R : AdvanceSpliceRelation S.blueprint current z
      (slice j) (closure j) persistent B)
    (hnonSource : ∀ x ∈ current.initialSet, x ∉ Gamma.source →
      ¬ ∃ y, (y, x) ∈ R.edge) :
    Nonempty (MovingTerminalAdvance S u) := by
  obtain ⟨U, h31, h31full⟩ :=
    R.exists_fullyPredecessorPreservingMovingAdvance931_of_nonSourceRoots
      h30.endpoint_mem_slice hnonSource
  exact ⟨MovingTerminalAdvance.of930931 j hij h30 h31 h30refines
    h31full.predecessorRefines⟩

/-- Source-rooted form used when the reachable-state invariant identifies
all current roots as ambient sources.  No separate relation-incidence premise
is then needed. -/
theorem exists_movingTerminalAdvance_of_continuation_relation_sourceRooted
    {S : State} {u z : V}
    {cut current : LinkageBlueprint Gamma Y kappa}
    (j : Stage) (hij : S.stageIndex < j)
    (h30 : Continuation930 S.blueprint cut current u z
      (slice S.stageIndex) B)
    (h30refines : S.blueprint.PredecessorRefines current)
    (R : AdvanceSpliceRelation S.blueprint current z
      (slice j) (closure j) persistent B)
    (hsource : current.initialSet ⊆ Gamma.source) :
    Nonempty (MovingTerminalAdvance S u) := by
  obtain ⟨U, h31, h31full⟩ :=
    R.exists_fullyPredecessorPreservingMovingAdvance931_of_sourceRooted
      h30.endpoint_mem_slice hsource
  exact ⟨MovingTerminalAdvance.of930931 j hij h30 h31 h30refines
    h31full.predecessorRefines⟩

/-- Direct form for the intended post-closure output.  A segmented
construction which has already isolated its current-disjoint fresh relation
can hand that exact `FreshAdvanceSpliceRelation` to the scheduler without
first repackaging a separate occurrence assignment. -/
theorem exists_movingTerminalAdvance_of_continuation_fresh
    {S : State} {u z : V}
    {cut current : LinkageBlueprint Gamma Y kappa}
    (j : Stage) (hij : S.stageIndex < j)
    (h30 : Continuation930 S.blueprint cut current u z
      (slice S.stageIndex) B)
    (h30refines : S.blueprint.PredecessorRefines current)
    (R : FreshAdvanceSpliceRelation S.blueprint current z
      (slice j) (closure j) persistent B) :
    Nonempty (MovingTerminalAdvance S u) := by
  obtain ⟨U, h31, h31full⟩ :=
    R.exists_fullyPredecessorPreservingMovingAdvance931
      h30.endpoint_mem_slice
  exact ⟨MovingTerminalAdvance.of930931 j hij h30 h31 h30refines
    h31full.predecessorRefines⟩

#print axioms
  noIncomingOld_of_oldEdges_biunique_of_initialsRemainRoots
#print axioms AdvanceSpliceRelation.sourceInitialRemainsRoot
#print axioms
  AdvanceSpliceRelation.initialsRemainRoots_of_nonSourceInitialsRemainRoots
#print axioms
  AdvanceSpliceRelation.initialsRemainRoots_of_initialSet_subset_source
#print axioms
  AdvanceSpliceRelation.exists_fullyPredecessorPreservingMovingAdvance931_of_initialsRemainRoots
#print axioms
  AdvanceSpliceRelation.exists_fullyPredecessorPreservingMovingAdvance931_of_nonSourceRoots
#print axioms
  AdvanceSpliceRelation.exists_fullyPredecessorPreservingMovingAdvance931_of_sourceRooted
#print axioms
  AdvanceSpliceRelation.exists_fullyPredecessorPreservingMovingAdvance931_of_noIncomingOld
#print axioms
  IndexedTerminalResolutionState.exists_movingTerminalAdvance_of_continuation_relation
#print axioms
  IndexedTerminalResolutionState.exists_movingTerminalAdvance_of_continuation_relation_roots
#print axioms
  IndexedTerminalResolutionState.exists_movingTerminalAdvance_of_continuation_relation_nonSourceRoots
#print axioms
  IndexedTerminalResolutionState.exists_movingTerminalAdvance_of_continuation_relation_sourceRooted
#print axioms
  IndexedTerminalResolutionState.exists_movingTerminalAdvance_of_continuation_fresh

end IndexedTerminalResolutionState
end Erdos599.Blueprint.LinkageBlueprint
