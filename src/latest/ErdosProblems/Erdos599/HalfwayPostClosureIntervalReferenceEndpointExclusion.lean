/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosurePureBoundary
import ErdosProblems.Erdos599.HalfwayLinkageFirstBoundary

/-!
# Endpoint exclusions for the actual finite interval reference

The later interval row and the finite interval reference have the same two
slice boundaries.  Hence a row edge cannot enter an interval-reference
initial and cannot leave an interval-reference terminal.  These statements
are deliberately about `intervalReference`, not the limiting ladder warp:
global marker initials need not be initials of the later interval row.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint.PostClosureIntervalTransaction

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ X0 : Set V} {z : V}
variable {R : DynamicMoving931GlobalClosure C globalZ X0}

/-- A later-row edge cannot enter an initial of the finite interval
reference: both initial sets lie on the captured old slice. -/
theorem ambientInterval_edge_head_not_mem_intervalReference_initialSet
    (T : PostClosureIntervalTransaction C globalZ X0 z R)
    {x y : V} (hxy : (x, y) ∈ familyEdges T.interval.ambientInterval) :
    y ∉ Gamma.initialSet T.intervalReference := by
  intro hyReference
  have hyOld : y ∈ R.capturedGeometry.oldSlice := by
    simpa only [DynamicMoving931GlobalClosure.capturedGeometry_oldSlice] using
      T.intervalReference_initialSet_subset_currentSlice hyReference
  have hyRow : y ∈ Gamma.initialSet T.interval.ambientInterval := by
    rw [T.interval.ambientInterval_linkage.initialSet_eq]
    exact hyOld
  exact isWarp_noIncoming_familyEdges_of_mem_initialSet
    T.interval.ambientInterval_linkage.isWarp hyRow ⟨x, hxy⟩

/-- A later-row edge cannot leave a terminal of the finite interval
reference.  Reference terminals lie on the captured new slice, and the row
meets that slice only at its own finite terminals. -/
theorem ambientInterval_edge_tail_not_mem_intervalReference_terminalFrontier
    (T : PostClosureIntervalTransaction C globalZ X0 z R)
    {x y : V} (hxy : (x, y) ∈ familyEdges T.interval.ambientInterval) :
    x ∉ Gamma.terminalFrontier T.intervalReference := by
  intro hxReference
  have hxNew : x ∈ R.capturedGeometry.newSlice :=
    T.intervalReference_isLinkageBetween.terminalFrontier_subset hxReference
  simp only [familyEdges, Set.mem_iUnion] at hxy
  obtain ⟨p, hpRow, hpxy⟩ := hxy
  have hxp : x ∈ p.support := (p.edgeSet_subset_support_prod hpxy).1
  have hpTerminal : Gamma.terminal? p = some x :=
    T.interval.ambientInterval_meetsOnlyAtTerminal p hpRow x hxp hxNew
  have hxRow : x ∈ Gamma.terminalFrontier T.interval.ambientInterval :=
    ⟨p, hpRow, hpTerminal⟩
  apply isWarp_noOutgoing_familyEdges_of_mem_terminalFrontier
    T.interval.ambientInterval_linkage.isWarp hxRow
  exact ⟨y, by
    simp only [familyEdges, Set.mem_iUnion]
    exact ⟨p, hpRow, hpxy⟩⟩

/-- The same head exclusion holds for the exact outside reference used by
the fractured assignment. -/
theorem ambientInterval_edge_head_not_mem_outsideIntervalReference_initialSet
    (T : PostClosureIntervalTransaction C globalZ X0 z R)
    {x y : V} (hxy : (x, y) ∈ familyEdges T.interval.ambientInterval) :
    y ∉ Gamma.initialSet (outsideReference T.intervalReference R.closedSet) := by
  intro hy
  apply T.ambientInterval_edge_head_not_mem_intervalReference_initialSet hxy
  obtain ⟨p, hp, rfl⟩ := hy
  exact ⟨p, hp.1, rfl⟩

/-- The same tail exclusion holds for the exact outside reference used by
the fractured assignment. -/
theorem ambientInterval_edge_tail_not_mem_outsideIntervalReference_terminalFrontier
    (T : PostClosureIntervalTransaction C globalZ X0 z R)
    {x y : V} (hxy : (x, y) ∈ familyEdges T.interval.ambientInterval) :
    x ∉ Gamma.terminalFrontier
      (outsideReference T.intervalReference R.closedSet) := by
  intro hx
  apply T.ambientInterval_edge_tail_not_mem_intervalReference_terminalFrontier hxy
  obtain ⟨p, hp, hterminal⟩ := hx
  exact ⟨p, hp.1, hterminal⟩

#print axioms
  ambientInterval_edge_head_not_mem_intervalReference_initialSet
#print axioms
  ambientInterval_edge_tail_not_mem_intervalReference_terminalFrontier
#print axioms
  ambientInterval_edge_head_not_mem_outsideIntervalReference_initialSet
#print axioms
  ambientInterval_edge_tail_not_mem_outsideIntervalReference_terminalFrontier

end Erdos599.Blueprint.LinkageBlueprint.PostClosureIntervalTransaction
