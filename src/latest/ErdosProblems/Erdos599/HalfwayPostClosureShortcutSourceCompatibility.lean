/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedAssignmentMacroFiniteOccurrence
import ErdosProblems.Erdos599.FracturedAssignmentMacroInfiniteOccurrence
import ErdosProblems.Erdos599.FracturedProjectionCutContact
import ErdosProblems.Erdos599.HalfwayPostClosureMacroCompressorAssignment
import ErdosProblems.Erdos599.HalfwayPostClosureShortcutForwardIncidence
import ErdosProblems.Erdos599.HalfwayPostClosureShortcutOutgoingIncidence
import ErdosProblems.Erdos599.HalfwayPostClosureShortcutClosedCarrier

/-!
# Occurrence compatibility of actual post-closure shortcuts

An actual shortcut head has an incoming forward edge in its compressed
route.  In the finite occurrence branch this edge lifts to the exact
macro-owned route upstairs, where cut endpoint purity identifies the head
as the incoming copy of the closed contact.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment

open DirectedPath _root_.Erdos599.Alternating
open FracturedAssignmentPeel Alternating.FracturedDuplication

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V} {z : V}
variable {Rlimit : LimitMoving931GlobalClosure C globalZ seed}
variable {T : PostClosureIntervalTransaction C globalZ seed z
  Rlimit.toDynamicMoving931GlobalClosure}

/-- Every forward edge of an active macro projection lifts to its literal
selected occurrence route, in either the finite or infinite branch. -/
theorem activeProjection_forwardEdge_occurrenceLift
    {Z : FracturedWarp Gamma} {Yref : Set Gamma.DPath}
    (A : FracturedAssignmentPeel.MacroCompressorProducedBracketFracturedAssignment
      Z Yref)
    (a : {x // x ∈ Gamma.initialSet (FracturedAssignmentPeel.activePaths Z) \
      Gamma.initialSet Yref})
    {x y : V}
    (hxy : (x, y) ∈
      (A.activeProjection a).traversal.produced.base.path.directionEdges
        .forward) :
    ∃ (l : Link (web Gamma Z).graph),
      l ∈ (A.occurrenceAssignment.assigned
        (toLiftedSource Z A.reference_finite a)).links ∧
      l.direction = .forward ∧
      ∃ e ∈ l.path.edgeSet, project e.1 = x ∧ project e.2 = y := by
  cases hQ : A.occurrenceAssignment.assigned
      (toLiftedSource Z A.reference_finite a) with
  | trivial w =>
      exact False.elim
        (FracturedAssignmentPeel.assigned_ne_trivial Z A.reference_finite
          A.occurrenceAssignment.toBracketSimultaneousAssignment a w hQ)
  | finite Q =>
      simpa only [hQ] using
        A.activeProjection_forwardEdge_occurrenceLift_of_finite a Q hQ hxy
  | infinite R =>
      simpa only [hQ] using
        A.activeProjection_forwardEdge_occurrenceLift_of_infinite a R hQ hxy

/-- In a finite selected occurrence branch, the head of an actual shortcut
is literally the incoming cut occurrence on that selected route. -/
theorem finiteShortcutHead_mem_incomingOccurrence
    (A : PostClosureMacroCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference
        Rlimit.closedSet)})
    (hs : s.1 ∉ singletonVertices A.fractured.outside.holes)
    (Q : FiniteTrace (web Gamma A.fractured.outside.holes).graph)
    (hQ : A.assignment.occurrenceAssignment.assigned
      (toLiftedSource A.fractured.outside.holes
        A.assignment.reference_finite
        (A.assignment.activeSource s hs)) = .finite Q)
    {x y : V}
    (hxy : (x, y) ∈
      (A.toPostClosureCompressorAssignment
        |>.actualClosedClassifiedContactSegmentation s).shortcutEdges) :
    incoming y ∈
      (A.assignment.occurrenceAssignment.assigned
        (toLiftedSource A.fractured.outside.holes
          A.assignment.reference_finite
          (A.assignment.activeSource s hs))).vertexSet := by
  let A0 := A.toPostClosureCompressorAssignment
  let S := A0.actualClosedClassifiedContactSegmentation s
  let a := A.assignment.activeSource s hs
  have hforward := A0.segmentation_shortcut_head_hasIncoming_forward s S
    (A0.actualClosedClassifiedContactSegmentation_contactSet_subset s) hxy
  obtain ⟨w, hwy⟩ := hforward
  have hwyActive : (w, y) ∈
      (A.assignment.activeProjection a).traversal.produced.base.path.directionEdges
        .forward := by
    rw [← A.assignment.compiled_assigned_eq_activeSourceProjection s hs]
    exact hwy
  obtain ⟨l, hl, hldir, e, he, htail, hhead⟩ :=
    A.assignment.activeProjection_forwardEdge_occurrenceLift_of_finite
      a Q hQ hwyActive
  have hbracket := A.assignment.occurrenceAssignment.bracket_safe
    (toLiftedSource A.fractured.outside.holes
      A.assignment.reference_finite a)
  have hrole :=
    bracketSafe_forwardEdge_head_eq_incoming_of_cutEndpointPure
      A.fractured.outside.holes Rlimit.closedSet
      (fun p hp v hv hvX =>
        A.fractured.cut_vertex_is_endpoint p hp (x := v) hv hvX)
      hbracket hl hldir he
      (by
        rw [hhead]
        exact A0.actualClosedClassifiedContactSegmentation_contactSet_subset s
          (S.endpoints_mem_contactSet hxy).2)
  have heSupport := l.path.edgeSet_subset_support_prod he
  have heVertex : e.2 ∈
      (A.assignment.occurrenceAssignment.assigned
        (toLiftedSource A.fractured.outside.holes
          A.assignment.reference_finite a)).vertexSet :=
    (A.assignment.occurrenceAssignment.assigned
      (toLiftedSource A.fractured.outside.holes
        A.assignment.reference_finite a)).link_support_subset_vertexSet
          hl heSupport.2
  rw [hrole, hhead] at heVertex
  exact heVertex

/-- The head of every actual shortcut is the incoming occurrence of its
closed contact on the exact selected macro route. -/
theorem shortcutHead_mem_incomingOccurrence
    (A : PostClosureMacroCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference
        Rlimit.closedSet)})
    (hs : s.1 ∉ singletonVertices A.fractured.outside.holes)
    {x y : V}
    (hxy : (x, y) ∈
      (A.toPostClosureCompressorAssignment
        |>.actualClosedClassifiedContactSegmentation s).shortcutEdges) :
    incoming y ∈
      (A.assignment.occurrenceAssignment.assigned
        (toLiftedSource A.fractured.outside.holes
          A.assignment.reference_finite
          (A.assignment.activeSource s hs))).vertexSet := by
  let A0 := A.toPostClosureCompressorAssignment
  let S := A0.actualClosedClassifiedContactSegmentation s
  let a := A.assignment.activeSource s hs
  obtain ⟨w, hwy⟩ :=
    A0.segmentation_shortcut_head_hasIncoming_forward s S
      (A0.actualClosedClassifiedContactSegmentation_contactSet_subset s) hxy
  have hwyActive : (w, y) ∈
      (A.assignment.activeProjection a).traversal.produced.base.path.directionEdges
        .forward := by
    rw [← A.assignment.compiled_assigned_eq_activeSourceProjection s hs]
    exact hwy
  obtain ⟨l, hl, hldir, e, he, htail, hhead⟩ :=
    activeProjection_forwardEdge_occurrenceLift A.assignment a hwyActive
  have hbracket := A.assignment.occurrenceAssignment.bracket_safe
    (toLiftedSource A.fractured.outside.holes
      A.assignment.reference_finite a)
  have hrole :=
    bracketSafe_forwardEdge_head_eq_incoming_of_cutEndpointPure
      A.fractured.outside.holes Rlimit.closedSet
      (fun p hp v hv hvX =>
        A.fractured.cut_vertex_is_endpoint p hp (x := v) hv hvX)
      hbracket hl hldir he
      (by
        rw [hhead]
        exact A0.actualClosedClassifiedContactSegmentation_contactSet_subset s
          (S.endpoints_mem_contactSet hxy).2)
  have heSupport := l.path.edgeSet_subset_support_prod he
  have heVertex : e.2 ∈
      (A.assignment.occurrenceAssignment.assigned
        (toLiftedSource A.fractured.outside.holes
          A.assignment.reference_finite a)).vertexSet :=
    (A.assignment.occurrenceAssignment.assigned
      (toLiftedSource A.fractured.outside.holes
        A.assignment.reference_finite a)).link_support_subset_vertexSet
          hl heSupport.2
  rw [hrole, hhead] at heVertex
  exact heVertex

/-- The tail of every actual shortcut is the outgoing occurrence of its
closed contact on the exact selected macro route. -/
theorem shortcutTail_mem_outgoingOccurrence
    (A : PostClosureMacroCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference
        Rlimit.closedSet)})
    (hs : s.1 ∉ singletonVertices A.fractured.outside.holes)
    {x y : V}
    (hxy : (x, y) ∈
      (A.toPostClosureCompressorAssignment
        |>.actualClosedClassifiedContactSegmentation s).shortcutEdges) :
    outgoing x ∈
      (A.assignment.occurrenceAssignment.assigned
        (toLiftedSource A.fractured.outside.holes
          A.assignment.reference_finite
          (A.assignment.activeSource s hs))).vertexSet := by
  let A0 := A.toPostClosureCompressorAssignment
  let S := A0.actualClosedClassifiedContactSegmentation s
  let a := A.assignment.activeSource s hs
  obtain ⟨w, hxw⟩ := A0.actualSegmentation_shortcut_tail_hasOutgoing_forward
    s hxy
  have hxwActive : (x, w) ∈
      (A.assignment.activeProjection a).traversal.produced.base.path.directionEdges
        .forward := by
    rw [← A.assignment.compiled_assigned_eq_activeSourceProjection s hs]
    exact hxw
  obtain ⟨l, hl, hldir, e, he, htail, hhead⟩ :=
    activeProjection_forwardEdge_occurrenceLift A.assignment a hxwActive
  have hbracket := A.assignment.occurrenceAssignment.bracket_safe
    (toLiftedSource A.fractured.outside.holes
      A.assignment.reference_finite a)
  have hrole :=
    bracketSafe_forwardEdge_tail_eq_outgoing_of_cutEndpointPure
      A.fractured.outside.holes Rlimit.closedSet
      (fun p hp v hv hvX =>
        A.fractured.cut_vertex_is_endpoint p hp (x := v) hv hvX)
      hbracket hl hldir he
      (by
        rw [htail]
        exact A0.actualClosedClassifiedContactSegmentation_contactSet_subset s
          (S.endpoints_mem_contactSet hxy).1)
  have heSupport := l.path.edgeSet_subset_support_prod he
  have heVertex : e.1 ∈
      (A.assignment.occurrenceAssignment.assigned
        (toLiftedSource A.fractured.outside.holes
          A.assignment.reference_finite a)).vertexSet :=
    (A.assignment.occurrenceAssignment.assigned
      (toLiftedSource A.fractured.outside.holes
        A.assignment.reference_finite a)).link_support_subset_vertexSet
          hl heSupport.1
  rw [hrole, htail] at heVertex
  exact heVertex

/-- Two finite-branch actual shortcuts with a common head come from the
same fractured source.  This is the cross-source half of left uniqueness. -/
theorem source_eq_of_common_shortcutHead_of_finite
    (A : PostClosureMacroCompressorAssignment T)
    (s t : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference
        Rlimit.closedSet)})
    (hs : s.1 ∉ singletonVertices A.fractured.outside.holes)
    (ht : t.1 ∉ singletonVertices A.fractured.outside.holes)
    (Qs Qt : FiniteTrace (web Gamma A.fractured.outside.holes).graph)
    (hQs : A.assignment.occurrenceAssignment.assigned
      (toLiftedSource A.fractured.outside.holes
        A.assignment.reference_finite
        (A.assignment.activeSource s hs)) = .finite Qs)
    (hQt : A.assignment.occurrenceAssignment.assigned
      (toLiftedSource A.fractured.outside.holes
        A.assignment.reference_finite
        (A.assignment.activeSource t ht)) = .finite Qt)
    {x y w : V}
    (hxy : (x, y) ∈
      (A.toPostClosureCompressorAssignment
        |>.actualClosedClassifiedContactSegmentation s).shortcutEdges)
    (hwy : (w, y) ∈
      (A.toPostClosureCompressorAssignment
        |>.actualClosedClassifiedContactSegmentation t).shortcutEdges) :
    s = t := by
  let A0 := A.toPostClosureCompressorAssignment
  let Ss := A0.actualClosedClassifiedContactSegmentation s
  let St := A0.actualClosedClassifiedContactSegmentation t
  have hys := A.finiteShortcutHead_mem_incomingOccurrence s hs Qs hQs hxy
  have hyt := A.finiteShortcutHead_mem_incomingOccurrence t ht Qt hQt hwy
  have hyX : y ∈ Rlimit.closedSet :=
    A0.actualClosedClassifiedContactSegmentation_contactSet_subset s
      (Ss.endpoints_mem_contactSet hxy).2
  have hlift :=
    FracturedAssignmentPeel.MacroOwnedBracketSimultaneousAssignment.source_eq_of_common_incoming
      A.fractured.outside.holes Rlimit.closedSet A.assignment.boundary
      A.assignment.reference_isWarp A.assignment.reference_finite
      A.assignment.occurrenceAssignment
      (toLiftedSource A.fractured.outside.holes
        A.assignment.reference_finite (A.assignment.activeSource s hs))
      (toLiftedSource A.fractured.outside.holes
        A.assignment.reference_finite (A.assignment.activeSource t ht))
      hys hyt hyX
  have hactive : A.assignment.activeSource s hs =
      A.assignment.activeSource t ht := by
    apply Subtype.ext
    have hval := congrArg
      (fun q => project q.1) hlift
    exact hval
  calc
    s = ofActiveSource A.fractured.outside.holes
        (A.assignment.activeSource s hs) :=
      (A.assignment.ofActiveSource_activeSource s hs).symm
    _ = ofActiveSource A.fractured.outside.holes
        (A.assignment.activeSource t ht) := congrArg _ hactive
    _ = t := A.assignment.ofActiveSource_activeSource t ht

/-- Finite-branch shortcuts are left-unique even across two different
members of the simultaneous assignment. -/
theorem shortcutTail_eq_of_common_head_of_finite
    (A : PostClosureMacroCompressorAssignment T)
    (s t : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference
        Rlimit.closedSet)})
    (hs : s.1 ∉ singletonVertices A.fractured.outside.holes)
    (ht : t.1 ∉ singletonVertices A.fractured.outside.holes)
    (Qs Qt : FiniteTrace (web Gamma A.fractured.outside.holes).graph)
    (hQs : A.assignment.occurrenceAssignment.assigned
      (toLiftedSource A.fractured.outside.holes
        A.assignment.reference_finite
        (A.assignment.activeSource s hs)) = .finite Qs)
    (hQt : A.assignment.occurrenceAssignment.assigned
      (toLiftedSource A.fractured.outside.holes
        A.assignment.reference_finite
        (A.assignment.activeSource t ht)) = .finite Qt)
    {x y w : V}
    (hxy : (x, y) ∈
      (A.toPostClosureCompressorAssignment
        |>.actualClosedClassifiedContactSegmentation s).shortcutEdges)
    (hwy : (w, y) ∈
      (A.toPostClosureCompressorAssignment
        |>.actualClosedClassifiedContactSegmentation t).shortcutEdges) :
    x = w := by
  have hst := A.source_eq_of_common_shortcutHead_of_finite s t hs ht
    Qs Qt hQs hQt hxy hwy
  subst t
  exact (A.toPostClosureCompressorAssignment
    |>.actualClosedClassifiedContactSegmentation s).shortcutEdges_biUnique.1
      hxy hwy

/-- Common shortcut heads force equality of the underlying fractured
sources, without a finite/infinite branch restriction. -/
theorem source_eq_of_common_shortcutHead
    (A : PostClosureMacroCompressorAssignment T)
    (s t : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference
        Rlimit.closedSet)})
    (hs : s.1 ∉ singletonVertices A.fractured.outside.holes)
    (ht : t.1 ∉ singletonVertices A.fractured.outside.holes)
    {x y w : V}
    (hxy : (x, y) ∈
      (A.toPostClosureCompressorAssignment
        |>.actualClosedClassifiedContactSegmentation s).shortcutEdges)
    (hwy : (w, y) ∈
      (A.toPostClosureCompressorAssignment
        |>.actualClosedClassifiedContactSegmentation t).shortcutEdges) :
    s = t := by
  have hys := A.shortcutHead_mem_incomingOccurrence s hs hxy
  have hyt := A.shortcutHead_mem_incomingOccurrence t ht hwy
  have hyX : y ∈ Rlimit.closedSet :=
    A.toPostClosureCompressorAssignment
      |>.actualClosedClassifiedContactSegmentation_contactSet_subset s
        ((A.toPostClosureCompressorAssignment
          |>.actualClosedClassifiedContactSegmentation s)
            |>.endpoints_mem_contactSet hxy).2
  have hlift :=
    FracturedAssignmentPeel.MacroOwnedBracketSimultaneousAssignment.source_eq_of_common_incoming
      A.fractured.outside.holes Rlimit.closedSet A.assignment.boundary
      A.assignment.reference_isWarp A.assignment.reference_finite
      A.assignment.occurrenceAssignment
      (toLiftedSource A.fractured.outside.holes
        A.assignment.reference_finite (A.assignment.activeSource s hs))
      (toLiftedSource A.fractured.outside.holes
        A.assignment.reference_finite (A.assignment.activeSource t ht))
      hys hyt hyX
  have hactive : A.assignment.activeSource s hs =
      A.assignment.activeSource t ht := by
    apply Subtype.ext
    exact congrArg (fun q => project q.1) hlift
  calc
    s = ofActiveSource A.fractured.outside.holes
        (A.assignment.activeSource s hs) :=
      (A.assignment.ofActiveSource_activeSource s hs).symm
    _ = ofActiveSource A.fractured.outside.holes
        (A.assignment.activeSource t ht) := congrArg _ hactive
    _ = t := A.assignment.ofActiveSource_activeSource t ht

/-- Common shortcut tails force equality of the underlying fractured
sources. -/
theorem source_eq_of_common_shortcutTail
    (A : PostClosureMacroCompressorAssignment T)
    (s t : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference
        Rlimit.closedSet)})
    (hs : s.1 ∉ singletonVertices A.fractured.outside.holes)
    (ht : t.1 ∉ singletonVertices A.fractured.outside.holes)
    {x y w : V}
    (hxy : (x, y) ∈
      (A.toPostClosureCompressorAssignment
        |>.actualClosedClassifiedContactSegmentation s).shortcutEdges)
    (hxw : (x, w) ∈
      (A.toPostClosureCompressorAssignment
        |>.actualClosedClassifiedContactSegmentation t).shortcutEdges) :
    s = t := by
  have hxs := A.shortcutTail_mem_outgoingOccurrence s hs hxy
  have hxt := A.shortcutTail_mem_outgoingOccurrence t ht hxw
  have hxX : x ∈ Rlimit.closedSet :=
    A.toPostClosureCompressorAssignment
      |>.actualClosedClassifiedContactSegmentation_contactSet_subset s
        ((A.toPostClosureCompressorAssignment
          |>.actualClosedClassifiedContactSegmentation s)
            |>.endpoints_mem_contactSet hxy).1
  have hlift :=
    FracturedAssignmentPeel.MacroOwnedBracketSimultaneousAssignment.source_eq_of_common_outgoing
      A.fractured.outside.holes Rlimit.closedSet A.assignment.boundary
      A.assignment.reference_isWarp A.assignment.reference_finite
      A.assignment.occurrenceAssignment
      (toLiftedSource A.fractured.outside.holes
        A.assignment.reference_finite (A.assignment.activeSource s hs))
      (toLiftedSource A.fractured.outside.holes
        A.assignment.reference_finite (A.assignment.activeSource t ht))
      hxs hxt hxX
  have hactive : A.assignment.activeSource s hs =
      A.assignment.activeSource t ht := by
    apply Subtype.ext
    exact congrArg (fun q => project q.1) hlift
  calc
    s = ofActiveSource A.fractured.outside.holes
        (A.assignment.activeSource s hs) :=
      (A.assignment.ofActiveSource_activeSource s hs).symm
    _ = ofActiveSource A.fractured.outside.holes
        (A.assignment.activeSource t ht) := congrArg _ hactive
    _ = t := A.assignment.ofActiveSource_activeSource t ht

/-- The complete actual shortcut union is biunique across all assignment
sources. -/
theorem actualPostClosureShortcutEdges_biUnique
    (A : PostClosureMacroCompressorAssignment T) :
    Relator.BiUnique (fun x y =>
      (x, y) ∈
        A.toPostClosureCompressorAssignment.actualPostClosureShortcutEdges) := by
  let A0 := A.toPostClosureCompressorAssignment
  constructor
  · intro x w y hxy hwy
    rw [A0.mem_actualPostClosureShortcutEdges_iff] at hxy hwy
    obtain ⟨s, hxy⟩ := hxy
    obtain ⟨t, hwy⟩ := hwy
    have hs := A.assignment.not_singleton_of_mem_segmentation_shortcut s
      (A0.actualClosedClassifiedContactSegmentation s) hxy
    have ht := A.assignment.not_singleton_of_mem_segmentation_shortcut t
      (A0.actualClosedClassifiedContactSegmentation t) hwy
    have hst := A.source_eq_of_common_shortcutHead s t hs ht hxy hwy
    subst t
    exact (A0.actualClosedClassifiedContactSegmentation s)
      |>.shortcutEdges_biUnique.1 hxy hwy
  · intro x y w hxy hxw
    rw [A0.mem_actualPostClosureShortcutEdges_iff] at hxy hxw
    obtain ⟨s, hxy⟩ := hxy
    obtain ⟨t, hxw⟩ := hxw
    have hs := A.assignment.not_singleton_of_mem_segmentation_shortcut s
      (A0.actualClosedClassifiedContactSegmentation s) hxy
    have ht := A.assignment.not_singleton_of_mem_segmentation_shortcut t
      (A0.actualClosedClassifiedContactSegmentation t) hxw
    have hst := A.source_eq_of_common_shortcutTail s t hs ht hxy hxw
    subst t
    exact (A0.actualClosedClassifiedContactSegmentation s)
      |>.shortcutEdges_biUnique.2 hxy hxw

end Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment

#print axioms Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment.finiteShortcutHead_mem_incomingOccurrence
#print axioms Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment.source_eq_of_common_shortcutHead_of_finite
#print axioms Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment.shortcutTail_eq_of_common_head_of_finite
#print axioms Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment.actualPostClosureShortcutEdges_biUnique
