/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingErasedRouteCore
import ErdosProblems.Erdos599.GroundingActiveControls

/-!
# The active simultaneous loop-erased grounding switch

This wrapper instantiates the pre-active chronological-erasure core with the
greedy active-control family and defines the literal simultaneous switched
relation used in Assertion 8.22.
-/

noncomputable section

namespace Erdos599
namespace GroundingErasedDecode

open Set DirectedPath Alternating PopularGroundingBridge
open GroundingSimultaneousDecode PopularAuxiliary.Input
open PopularAuxiliary.Input.EndpointTrace

universe u

variable {V I : Type u} {Gamma : DWeb V}

@[simp] theorem requestExit_chosenRequest
    {L : PopularAuxiliary.Input Gamma I} {C : Set L.LV}
    (c : ControlRequest L C) : requestExit (chosenRequest c) = c.1 := by
  rw [requestExit_eq_requestVertex]
  exact requestVertex_chosenRequest c


/-- Union of the retained edges of all loop-erased request routes. -/
def erasedSelectedRouteEdges
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) : Set (V × V) :=
  ⋃ c : ActiveControlRequest U S K,
    (selectedErasedCompression U S K (chosenRequest c.1)).path.edgeSet

theorem erasedSelectedRouteEdges_subset_adj
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) :
    erasedSelectedRouteEdges U S K ⊆ {e | Gamma.graph.Adj e.1 e.2} := by
  intro e he
  simp only [erasedSelectedRouteEdges, Set.mem_iUnion] at he
  obtain ⟨c, he⟩ := he
  let T := selectedRequestTrace U S K (chosenRequest c.1)
  let E := T.erasedRoute
  have he' : e ∈ signedEdgeSet E.steps := by
    rw [← (selectedErasedCompression U S K (chosenRequest c.1)).edgeSet_eq]
    exact he
  obtain ⟨s, hs, rfl⟩ := he'
  exact T.valid s (E.steps_sublist.subset hs)

/-- The union of the compressed selected-route edges traversed in one
specified alternating direction. -/
def erasedSelectedDirectionEdges
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (d : Alternating.Direction) : Set (V × V) :=
  ⋃ c : ActiveControlRequest U S K,
    (selectedErasedCompression U S K
      (chosenRequest c.1)).path.directionEdges d

theorem erasedSelectedDirectionEdges_subset_routeEdges
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (d : Alternating.Direction) :
    erasedSelectedDirectionEdges U S K d ⊆
      erasedSelectedRouteEdges U S K := by
  intro e he
  simp only [erasedSelectedDirectionEdges, Set.mem_iUnion] at he
  obtain ⟨c, he⟩ := he
  simp only [erasedSelectedRouteEdges, Set.mem_iUnion]
  refine ⟨c, ?_⟩
  rw [(selectedErasedCompression U S K
    (chosenRequest c.1)).path.edgeSet_eq_directionEdges_union]
  cases d with
  | forward => exact Or.inl he
  | backward => exact Or.inr he

theorem erasedSelectedDirectionEdges_subset_adj
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (d : Alternating.Direction) :
    erasedSelectedDirectionEdges U S K d ⊆
      {e | Gamma.graph.Adj e.1 e.2} :=
  (erasedSelectedDirectionEdges_subset_routeEdges U S K d).trans
    (erasedSelectedRouteEdges_subset_adj U S K)

/-- The simultaneous forward relation after source-style pruning inside
each link: only the prefix reachable before the first old request is
retained. -/
def erasedSelectedRetainedForwardEdges
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) : Set (V × V) :=
  ⋃ c : ActiveControlRequest U S K,
    retainedForwardEdges (L := L) S.cut
      (selectedErasedCompression U S K (chosenRequest c.1)).path

theorem erasedSelectedRetainedForwardEdges_subset_forward
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) :
    erasedSelectedRetainedForwardEdges U S K ⊆
      erasedSelectedDirectionEdges U S K .forward := by
  intro e he
  simp only [erasedSelectedRetainedForwardEdges, Set.mem_iUnion] at he
  obtain ⟨c, he⟩ := he
  simp only [erasedSelectedDirectionEdges, Set.mem_iUnion]
  exact ⟨c, retainedForwardEdges_subset_directionEdges S.cut _ he⟩

theorem erasedSelectedRetainedForwardEdges_subset_adj
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) :
    erasedSelectedRetainedForwardEdges U S K ⊆
      {e | Gamma.graph.Adj e.1 e.2} :=
  (erasedSelectedRetainedForwardEdges_subset_forward U S K).trans
    (erasedSelectedDirectionEdges_subset_adj U S K .forward)

theorem oldRequest_noOutgoing_erasedSelectedRetainedForwardEdges
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : oldRequests L S.cut) :
    ¬ Alternating.HasOutgoing
      (erasedSelectedRetainedForwardEdges U S K) r.1 := by
  rintro ⟨y, hy⟩
  simp only [erasedSelectedRetainedForwardEdges, Set.mem_iUnion] at hy
  obtain ⟨c, hy⟩ := hy
  exact oldRequest_noOutgoing_retainedForwardEdges S.cut
    (selectedErasedCompression U S K (chosenRequest c.1)).path r ⟨y, hy⟩

theorem boundary_noOutgoing_erasedSelectedRetainedForwardEdges
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    {b : V} (hb : b ∈ GroundingCut.BB L S.cut) :
    ¬ Alternating.HasOutgoing
      (erasedSelectedRetainedForwardEdges U S K) b := by
  rintro ⟨y, hy⟩
  simp only [erasedSelectedRetainedForwardEdges, Set.mem_iUnion] at hy
  obtain ⟨c, hy⟩ := hy
  exact boundary_noOutgoing_retainedForwardEdges S.cut
    (selectedErasedCompression U S K (chosenRequest c.1)).path hb ⟨y, hy⟩

/-- The source's residual ladder relation `G = Y - C_E`.  The old cut
vertices `C_V` remain boundary vertices of the residual fragments; only the
represented ladder edges are absent before any selected route is switched
in. -/
def residualLadderEdges
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) : Set (V × V) :=
  L.familyEdges \ GroundingCut.CE L S.cut

theorem residualLadderEdges_subset_adj
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) :
    residualLadderEdges U S ⊆ {e | Gamma.graph.Adj e.1 e.2} := by
  intro e he
  exact Alternating.familyEdges_subset_adj L.ladder.paths (by
    simpa [PopularAuxiliary.Input.familyEdges,
      Alternating.familyEdges] using he.1)

/-- A proxy route attaches at an internal vertex of its represented ladder
path.  Replacing the proxy arc by the corresponding prefix of that path
deletes the old outgoing edge at the attachment vertex.  The same formula
is harmless for a finite-source route: a finite ladder terminal has no
outgoing residual ladder edge. -/
def attachmentCutEdges
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) : Set (V × V) :=
  {e | e ∈ residualLadderEdges U S ∧
    ∃ c : ActiveControlRequest U S K,
      e.1 = (selectedRequestTrace U S K (chosenRequest c.1)).initial}

theorem attachmentCutEdges_subset_residualLadderEdges
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) :
    attachmentCutEdges U S K ⊆ residualLadderEdges U S := by
  intro e he
  exact he.1

/-- A decoded request route ends at its chosen original control vertex.
The residual ladder may already have an incoming edge there (this is the
old-vertex request case).  The simultaneous switch replaces that incoming
edge by the last forward edge of the decoded route.  For an edge request
the represented incoming edge belongs to `CE` and is already absent from
the residual relation, so this additional deletion is harmless. -/
def terminalAttachmentCutEdges
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) : Set (V × V) :=
  {e | e ∈ residualLadderEdges U S ∧
    ∃ c : ActiveControlRequest U S K,
      e.2 = requestExit (chosenRequest c.1)}

theorem terminalAttachmentCutEdges_subset_residualLadderEdges
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) :
    terminalAttachmentCutEdges U S K ⊆ residualLadderEdges U S := by
  intro e he
  exact he.1

/-- Residual ladder edges whose head or tail conflicts with an actually
added forward connector.  Deleting these edges before inserting the
forward relation is the component-selection normalization implicit in
applying all selected routes to the residual fragment family.  At an
initial proxy attachment it deletes the old outgoing ladder edge; at an old
cut endpoint reached by a forward connector it deletes the old incoming
ladder edge.  A request ending through a backward gadget join creates no
spurious terminal deletion. -/
def forwardConflictCutEdges
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) : Set (V × V) :=
  {e | e ∈ residualLadderEdges U S ∧
    ∃ f ∈ erasedSelectedRetainedForwardEdges U S K,
      e.1 = f.1 ∨ e.2 = f.2}

theorem forwardConflictCutEdges_subset_residualLadderEdges
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) :
    forwardConflictCutEdges U S K ⊆ residualLadderEdges U S := by
  intro e he
  exact he.1

/-- Residual continuations leaving an old-vertex control.  This named subset
is retained for compatibility with the old-request endpoint lemmas; the final
switch uses the stronger `boundaryOutgoingCutEdges` below. -/
def oldRequestOutgoingCutEdges
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) : Set (V × V) :=
  {e | e ∈ residualLadderEdges U S ∧
    ∃ r : oldRequests L S.cut, e.1 = r.1}

theorem oldRequestOutgoingCutEdges_subset_residualLadderEdges
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) :
    oldRequestOutgoingCutEdges U S ⊆ residualLadderEdges U S := by
  intro e he
  exact he.1

/-- Every residual departure from the final boundary is removed.  Incoming
edges are untouched, so the source-side prefix reaching the first boundary
contact remains available while no switched component can pass through that
contact to a second point of `BB`. -/
def boundaryOutgoingCutEdges
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) : Set (V × V) :=
  {e | e ∈ residualLadderEdges U S ∧
    e.1 ∈ GroundingCut.BB L S.cut}

theorem boundaryOutgoingCutEdges_subset_residualLadderEdges
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) :
    boundaryOutgoingCutEdges U S ⊆ residualLadderEdges U S := by
  intro e he
  exact he.1

theorem oldRequestOutgoingCutEdges_subset_boundaryOutgoingCutEdges
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) :
    oldRequestOutgoingCutEdges U S ⊆ boundaryOutgoingCutEdges U S := by
  rintro e ⟨heResidual, r, hr⟩
  refine ⟨heResidual, ?_⟩
  rw [hr]
  exact GroundingCut.CV_subset_BB L S.cut r.2.1

/-- All forward-route edges outside the source-side retained prefixes.
This removes not only the edge leaving the first old request but the whole
non-starting suffix of that link, exactly as in the source's component
elimination step. -/
def oldRequestOutgoingForwardCutEdges
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) : Set (V × V) :=
  erasedSelectedDirectionEdges U S K .forward \
    erasedSelectedRetainedForwardEdges U S K

theorem oldRequestOutgoingForwardCutEdges_subset_forward
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) :
    oldRequestOutgoingForwardCutEdges U S K ⊆
      erasedSelectedDirectionEdges U S K .forward := by
  intro e he
  exact he.1

theorem forward_diff_oldRequestOutgoingForwardCutEdges_eq_retained
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) :
    erasedSelectedDirectionEdges U S K .forward \
        oldRequestOutgoingForwardCutEdges U S K =
      erasedSelectedRetainedForwardEdges U S K := by
  apply Set.Subset.antisymm
  · rintro e ⟨heforward, henotCut⟩
    by_contra henotRetained
    exact henotCut ⟨heforward, henotRetained⟩
  · intro e heretained
    refine ⟨erasedSelectedRetainedForwardEdges_subset_forward U S K
      heretained, ?_⟩
    rintro ⟨_heforward, henotRetained⟩
    exact henotRetained heretained

/-- Every residual continuation from the endpoint of an actual old request
is one of the explicit endpoint cuts. -/
theorem oldRequest_residualOutgoing_mem_cut
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (r : oldRequests L S.cut) {y : V}
    (h : (r.1, y) ∈ residualLadderEdges U S) :
    (r.1, y) ∈ oldRequestOutgoingCutEdges U S := by
  exact ⟨h, r, rfl⟩

theorem boundary_residualOutgoing_mem_cut
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    {b y : V} (hb : b ∈ GroundingCut.BB L S.cut)
    (h : (b, y) ∈ residualLadderEdges U S) :
    (b, y) ∈ boundaryOutgoingCutEdges U S := by
  exact ⟨h, hb⟩

/-- Edges deleted by the source-faithful decoded switch: the selected
backward route edges together with every residual edge conflicting with an
inserted forward connector and every residual continuation leaving an old
request endpoint.  Forward route edges are added separately rather than
blindly toggled, so no edge outside the residual base is reintroduced. -/
def erasedSelectedToggleEdges
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) : Set (V × V) :=
  erasedSelectedDirectionEdges U S K .backward ∪
    (forwardConflictCutEdges U S K ∪ boundaryOutgoingCutEdges U S)

theorem erasedSelectedToggleEdges_subset_adj
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) :
    erasedSelectedToggleEdges U S K ⊆
      {e | Gamma.graph.Adj e.1 e.2} := by
  intro e he
  rcases he with he | he
  · exact erasedSelectedDirectionEdges_subset_adj U S K .backward he
  · rcases he with he | he
    · exact residualLadderEdges_subset_adj U S
        (forwardConflictCutEdges_subset_residualLadderEdges U S K he)
    · exact residualLadderEdges_subset_adj U S
        (boundaryOutgoingCutEdges_subset_residualLadderEdges U S he)

/-- Literal simultaneous switch relation using the residual ladder and the
head-stopping erased request routes.  Backward links and residual edges
conflicting with inserted forward connectors are removed from the base.
Every departure from a boundary point is then cut on both sides of
the union: residual continuations by `erasedSelectedToggleEdges`, and
selected forward departures by `oldRequestOutgoingForwardCutEdges`.
All other forward links are added. -/
def erasedSelectedSwitchedEdges
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) : Set (V × V) :=
  (residualLadderEdges U S \ erasedSelectedToggleEdges U S K) ∪
    (erasedSelectedDirectionEdges U S K .forward \
      oldRequestOutgoingForwardCutEdges U S K)

/-- The retained prefix of each active route is literally contained in the
final switched relation. -/
theorem activeRetainedForwardEdges_subset_switched
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (c : ActiveControlRequest U S K) :
    retainedForwardEdges (L := L) S.cut
        (selectedErasedCompression U S K (chosenRequest c.1)).path ⊆
      erasedSelectedSwitchedEdges U S K := by
  intro e he
  rw [erasedSelectedSwitchedEdges,
    forward_diff_oldRequestOutgoingForwardCutEdges_eq_retained U S K]
  exact Or.inr (Set.mem_iUnion.2 ⟨c, he⟩)

/-- Every point of `BB` is a literal sink of the final switched relation.
The residual branch is removed by `boundaryOutgoingCutEdges`, while the
retained forward branch stops when its tail first belongs to `BB`. -/
theorem boundary_noOutgoing_switched
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    {b : V} (hb : b ∈ GroundingCut.BB L S.cut) :
    ¬ Alternating.HasOutgoing (erasedSelectedSwitchedEdges U S K) b := by
  rintro ⟨y, hry⟩
  rcases hry with hry | hry
  · apply hry.2
    exact Or.inr (Or.inr
      (boundary_residualOutgoing_mem_cut U S hb hry.1))
  · rw [forward_diff_oldRequestOutgoingForwardCutEdges_eq_retained
      U S K] at hry
    exact boundary_noOutgoing_erasedSelectedRetainedForwardEdges
      U S K hb ⟨y, hry⟩

/-- Compatibility specialization for old request endpoints. -/
theorem oldRequest_noOutgoing_switched
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : oldRequests L S.cut) :
    ¬ Alternating.HasOutgoing (erasedSelectedSwitchedEdges U S K) r.1 := by
  apply boundary_noOutgoing_switched U S K
  exact GroundingCut.CV_subset_BB L S.cut r.2.1

/-! ## Minimal-boundary-parametric switch

These definitions use a freely supplied boundary `T`.  The active-control
recursion and every retained prefix use that same `T`, so vertices of
`BB \ T` remain available as pass-through points. -/

def erasedSelectedDirectionEdgesAt
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (T : Set V) (d : Alternating.Direction) : Set (V × V) :=
  ⋃ c : ActiveControlRequestAt U S K T,
    (selectedErasedCompression U S K
      (chosenRequest c.1)).path.directionEdges d

theorem erasedSelectedDirectionEdgesAt_subset_adj
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (T : Set V) (d : Alternating.Direction) :
    erasedSelectedDirectionEdgesAt U S K T d ⊆
      {e | Gamma.graph.Adj e.1 e.2} := by
  intro e he
  simp only [erasedSelectedDirectionEdgesAt, Set.mem_iUnion] at he
  obtain ⟨c, he⟩ := he
  let R := selectedRequestTrace U S K (chosenRequest c.1)
  let E := R.erasedRoute
  have heEdge : e ∈
      (selectedErasedCompression U S K
        (chosenRequest c.1)).path.edgeSet := by
    rw [(selectedErasedCompression U S K
      (chosenRequest c.1)).path.edgeSet_eq_directionEdges_union]
    cases d with
    | forward => exact Or.inl he
    | backward => exact Or.inr he
  have he' : e ∈ signedEdgeSet E.steps := by
    rw [← (selectedErasedCompression U S K
      (chosenRequest c.1)).edgeSet_eq]
    exact heEdge
  obtain ⟨s, hs, rfl⟩ := he'
  exact R.valid s (E.steps_sublist.subset hs)

def erasedSelectedRetainedForwardEdgesAt
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (T : Set V) : Set (V × V) :=
  ⋃ c : ActiveControlRequestAt U S K T,
    retainedForwardEdgesAt T
      (selectedErasedCompression U S K (chosenRequest c.1)).path

theorem erasedSelectedRetainedForwardEdgesAt_subset_forward
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) (T : Set V) :
    erasedSelectedRetainedForwardEdgesAt U S K T ⊆
      erasedSelectedDirectionEdgesAt U S K T .forward := by
  intro e he
  simp only [erasedSelectedRetainedForwardEdgesAt, Set.mem_iUnion] at he
  obtain ⟨c, he⟩ := he
  simp only [erasedSelectedDirectionEdgesAt, Set.mem_iUnion]
  exact ⟨c, retainedForwardEdgesAt_subset_directionEdges T _ he⟩

/-- With an empty stopping frontier the selected forward relation is not
truncated: it is exactly the union of all forward direction edges. -/
theorem erasedSelectedRetainedForwardEdgesAt_empty
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) :
    erasedSelectedRetainedForwardEdgesAt U S K (∅ : Set V) =
      erasedSelectedDirectionEdgesAt U S K ∅ .forward := by
  ext e
  simp only [erasedSelectedRetainedForwardEdgesAt,
    erasedSelectedDirectionEdgesAt, Set.mem_iUnion]
  constructor
  · rintro ⟨c, he⟩
    exact ⟨c, by
      simpa only [retainedForwardEdgesAt_empty] using he⟩
  · rintro ⟨c, he⟩
    exact ⟨c, by
      simpa only [retainedForwardEdgesAt_empty] using he⟩

theorem boundary_noOutgoing_erasedSelectedRetainedForwardEdgesAt
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) (T : Set V)
    {t : V} (ht : t ∈ T) :
    ¬ Alternating.HasOutgoing
      (erasedSelectedRetainedForwardEdgesAt U S K T) t := by
  rintro ⟨y, hy⟩
  simp only [erasedSelectedRetainedForwardEdgesAt, Set.mem_iUnion] at hy
  obtain ⟨c, hy⟩ := hy
  exact boundary_noOutgoing_retainedForwardEdgesAt T
    (selectedErasedCompression U S K (chosenRequest c.1)).path ht
      ⟨y, hy⟩

def forwardConflictCutEdgesAt
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) (T : Set V) : Set (V × V) :=
  {e | e ∈ residualLadderEdges U S ∧
    ∃ f ∈ erasedSelectedRetainedForwardEdgesAt U S K T,
      e.1 = f.1 ∨ e.2 = f.2}

def boundaryOutgoingCutEdgesAt
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) (T : Set V) : Set (V × V) :=
  {e | e ∈ residualLadderEdges U S ∧ e.1 ∈ T}

theorem boundaryOutgoingCutEdgesAt_empty
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) :
    boundaryOutgoingCutEdgesAt U S (∅ : Set V) = ∅ := by
  ext e
  simp [boundaryOutgoingCutEdgesAt]

def erasedSelectedToggleEdgesAt
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) (T : Set V) : Set (V × V) :=
  erasedSelectedDirectionEdgesAt U S K T .backward ∪
    (forwardConflictCutEdgesAt U S K T ∪
      boundaryOutgoingCutEdgesAt U S T)

def erasedSelectedForwardCutEdgesAt
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) (T : Set V) : Set (V × V) :=
  erasedSelectedDirectionEdgesAt U S K T .forward \
    erasedSelectedRetainedForwardEdgesAt U S K T

theorem erasedSelectedForwardCutEdgesAt_empty
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) :
    erasedSelectedForwardCutEdgesAt U S K (∅ : Set V) = ∅ := by
  rw [erasedSelectedForwardCutEdgesAt,
    erasedSelectedRetainedForwardEdgesAt_empty]
  exact Set.diff_self

theorem forward_diff_erasedSelectedForwardCutEdgesAt_eq_retained
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) (T : Set V) :
    erasedSelectedDirectionEdgesAt U S K T .forward \
        erasedSelectedForwardCutEdgesAt U S K T =
      erasedSelectedRetainedForwardEdgesAt U S K T := by
  apply Set.Subset.antisymm
  · rintro e ⟨heforward, henotCut⟩
    by_contra henotRetained
    exact henotCut ⟨heforward, henotRetained⟩
  · intro e heretained
    refine ⟨erasedSelectedRetainedForwardEdgesAt_subset_forward
      U S K T heretained, ?_⟩
    rintro ⟨_heforward, henotRetained⟩
    exact henotRetained heretained

def erasedSelectedSwitchedEdgesAt
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) (T : Set V) : Set (V × V) :=
  (residualLadderEdges U S \ erasedSelectedToggleEdgesAt U S K T) ∪
    (erasedSelectedDirectionEdgesAt U S K T .forward \
      erasedSelectedForwardCutEdgesAt U S K T)

/-- Exact expansion of the pre-stopped switch.  No boundary edge and no
selected forward edge is removed when the stopping frontier is empty. -/
theorem erasedSelectedSwitchedEdgesAt_empty_eq
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) :
    erasedSelectedSwitchedEdgesAt U S K (∅ : Set V) =
      (residualLadderEdges U S \
          (erasedSelectedDirectionEdgesAt U S K ∅ .backward ∪
            forwardConflictCutEdgesAt U S K ∅)) ∪
        erasedSelectedDirectionEdgesAt U S K ∅ .forward := by
  rw [erasedSelectedSwitchedEdgesAt, erasedSelectedToggleEdgesAt,
    boundaryOutgoingCutEdgesAt_empty,
    erasedSelectedForwardCutEdgesAt_empty]
  simp only [Set.union_empty, Set.diff_empty]

theorem activeRetainedForwardEdgesAt_subset_switched
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) (T : Set V)
    (c : ActiveControlRequestAt U S K T) :
    retainedForwardEdgesAt T
        (selectedErasedCompression U S K (chosenRequest c.1)).path ⊆
      erasedSelectedSwitchedEdgesAt U S K T := by
  intro e he
  rw [erasedSelectedSwitchedEdgesAt,
    forward_diff_erasedSelectedForwardCutEdgesAt_eq_retained U S K T]
  exact Or.inr (Set.mem_iUnion.2 ⟨c, he⟩)

theorem boundary_noOutgoing_switchedAt
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) (T : Set V)
    {t : V} (ht : t ∈ T) :
    ¬ Alternating.HasOutgoing (erasedSelectedSwitchedEdgesAt U S K T) t := by
  rintro ⟨y, hty⟩
  rcases hty with hty | hty
  · apply hty.2
    exact Or.inr (Or.inr ⟨hty.1, ht⟩)
  · rw [forward_diff_erasedSelectedForwardCutEdgesAt_eq_retained
      U S K T] at hty
    exact boundary_noOutgoing_erasedSelectedRetainedForwardEdgesAt
      U S K T ht ⟨y, hty⟩

theorem erasedSelectedSwitchedEdgesAt_subset_adj
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) (T : Set V) :
    erasedSelectedSwitchedEdgesAt U S K T ⊆
      {e | Gamma.graph.Adj e.1 e.2} := by
  intro e he
  rcases he with he | he
  · exact residualLadderEdges_subset_adj U S he.1
  · exact erasedSelectedDirectionEdgesAt_subset_adj U S K T .forward he.1

theorem survivingResidual_forwardAt_incoming_unique
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) (T : Set V)
    {x y z : V}
    (hxz : (x, z) ∈ residualLadderEdges U S \
      erasedSelectedToggleEdgesAt U S K T)
    (hyz : (y, z) ∈ erasedSelectedRetainedForwardEdgesAt U S K T) :
    x = y := by
  exfalso
  apply hxz.2
  exact Or.inr (Or.inl ⟨hxz.1, (y, z), hyz, Or.inr rfl⟩)

theorem survivingResidual_forwardAt_outgoing_unique
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) (T : Set V)
    {x y z : V}
    (hxy : (x, y) ∈ residualLadderEdges U S \
      erasedSelectedToggleEdgesAt U S K T)
    (hxz : (x, z) ∈ erasedSelectedRetainedForwardEdgesAt U S K T) :
    y = z := by
  exfalso
  apply hxy.2
  exact Or.inr (Or.inl ⟨hxy.1, (x, z), hxz, Or.inl rfl⟩)

/-- A residual edge which survives connector-conflict deletion cannot have
the same head as an inserted forward edge.  This is the incoming half of
the cross-colour local-uniqueness repair. -/
theorem survivingResidual_forward_incoming_unique
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    {x y z : V}
    (hxz : (x, z) ∈ residualLadderEdges U S \
      erasedSelectedToggleEdges U S K)
    (hyz : (y, z) ∈ erasedSelectedRetainedForwardEdges U S K) :
    x = y := by
  exfalso
  apply hxz.2
  right
  left
  exact ⟨hxz.1, (y, z), hyz, Or.inr rfl⟩

/-- A residual edge which survives connector-conflict deletion cannot have
the same tail as an inserted forward edge.  This is the outgoing half of
the cross-colour local-uniqueness repair. -/
theorem survivingResidual_forward_outgoing_unique
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    {x y z : V}
    (hxy : (x, y) ∈ residualLadderEdges U S \
      erasedSelectedToggleEdges U S K)
    (hxz : (x, z) ∈ erasedSelectedRetainedForwardEdges U S K) :
    y = z := by
  exfalso
  apply hxy.2
  right
  left
  exact ⟨hxy.1, (x, z), hxz, Or.inl rfl⟩

theorem erasedSelectedSwitchedEdges_subset_adj
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) :
    erasedSelectedSwitchedEdges U S K ⊆
      {e | Gamma.graph.Adj e.1 e.2} := by
  intro e he
  rcases he with he | he
  · exact residualLadderEdges_subset_adj U S he.1
  · exact erasedSelectedDirectionEdges_subset_adj U S K .forward he.1

/-- Original isolated ladder vertices survive precisely when the repaired
switched relation does not use them.  In particular, an isolated grounded
parent used as a route attachment is not incorrectly re-added as a trivial
path. -/
def erasedSelectedSurvivingIsolated
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) : Set V :=
  Alternating.isolatedVertices L.ladder.paths \
    Alternating.RelationDecomposition.IncidentVertices
      (erasedSelectedSwitchedEdges U S K)

theorem erasedSelectedSurvivingIsolated_nonincident
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) :
    ∀ x ∈ erasedSelectedSurvivingIsolated U S K, ∀ y,
      (x, y) ∉ erasedSelectedSwitchedEdges U S K ∧
        (y, x) ∉ erasedSelectedSwitchedEdges U S K := by
  intro x hx y
  refine ⟨?_, ?_⟩
  · intro hxy
    exact hx.2 ⟨y, Or.inl hxy⟩
  · intro hyx
    exact hx.2 ⟨y, Or.inr hyx⟩

/-- Exact graph-level switch data of the erased simultaneous decoder. -/
def erasedSelectedSwitchData
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) : Alternating.SwitchData Gamma where
  edges := erasedSelectedSwitchedEdges U S K
  edges_in_graph := erasedSelectedSwitchedEdges_subset_adj U S K
  isolated := erasedSelectedSurvivingIsolated U S K

/-- The relation facts sufficient for exact decomposition of the erased
simultaneous switch.  Every field speaks about the literal constructed edge
relation. -/
structure Compatible
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) : Prop where
  biUnique : Relator.BiUnique
    (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdges U S K)
  noDirectedCycle :
    ¬ Alternating.ContainsDirectedCycle
      (erasedSelectedSwitchedEdges U S K)
  noReverseDirectedRay :
    ¬ Alternating.ContainsReverseDirectedRay
      (erasedSelectedSwitchedEdges U S K)
  isolated_nonincident :
    ∀ x ∈ erasedSelectedSurvivingIsolated U S K, ∀ y,
      (x, y) ∉ erasedSelectedSwitchedEdges U S K ∧
        (y, x) ∉ erasedSelectedSwitchedEdges U S K

/-- Exact warp realization once the literal erased relation has been shown
compatible.  Forward rays are retained. -/
theorem Compatible.exists_realization
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed L.lambda kappa}
    {S : Popular.PopularSeparator U}
    {K : GroundingSelection.Controls S}
    (h : Compatible U S K) :
    ∃ W : Set Gamma.DPath,
      Alternating.SwitchData.RealizedBy
        (erasedSelectedSwitchData U S K) W := by
  obtain ⟨W, hW, hE, hI⟩ :=
    Alternating.RayCompatibleRelationDecomposition.exists_warp_realizing_biUnique_with_isolated
      Gamma (erasedSelectedSwitchedEdges U S K)
      (erasedSelectedSurvivingIsolated U S K)
      (erasedSelectedSwitchedEdges_subset_adj U S K)
      h.biUnique h.noDirectedCycle h.noReverseDirectedRay
      h.isolated_nonincident
  exact ⟨W, hW, hE, hI⟩

end GroundingErasedDecode
end Erdos599
