/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureActualSegmentation
import ErdosProblems.Erdos599.HalfwayPostClosureOldRoofIncidence
import ErdosProblems.Erdos599.HalfwaySourceInsideRestriction

/-!
# The closed shortcut relation of the actual post-closure assignment

Assertion 9.31 keeps the later row only inside the closed set and replaces a
finite assigned route by one shortcut between its closed contacts.  In
particular, the forward corridors retained by the contact classification are
evidence for the shortcut, not edges of the final relation: their internal
vertices need not belong to the closed set.

This file forms the source-faithful shortcut union over all actual assignment
sources and adjoins it to the literal inside restriction `W[X]`.  Every edge
of the resulting relation has both endpoints in `X`.  Cross-source
biuniqueness and the remaining splice geometry are deliberately separate.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace PostClosureCompressorAssignment

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V} {z : V}
variable {Rlimit : LimitMoving931GlobalClosure C globalZ seed}
variable {T : PostClosureIntervalTransaction C globalZ seed z
  Rlimit.toDynamicMoving931GlobalClosure}

/-- The union of the globally classified shortcuts for every actual assigned
outside fragment.  No assigned forward corridor is retained here. -/
def actualPostClosureShortcutEdges (A : PostClosureCompressorAssignment T) :
    Set (V × V) :=
  ⋃ s, (A.actualClosedClassifiedContactSegmentation s).shortcutEdges

theorem mem_actualPostClosureShortcutEdges_iff
    (A : PostClosureCompressorAssignment T) {e : V × V} :
    e ∈ A.actualPostClosureShortcutEdges ↔
      ∃ s, e ∈ (A.actualClosedClassifiedContactSegmentation s).shortcutEdges := by
  simp only [actualPostClosureShortcutEdges, Set.mem_iUnion]

/-- Both endpoints of every actual shortcut are contacts in the final closed
set.  This is the precise closed-carrier fact that fails for retained forward
corridors. -/
theorem actualPostClosureShortcutEdges_endpoints_closed
    (A : PostClosureCompressorAssignment T) {e : V × V}
    (he : e ∈ A.actualPostClosureShortcutEdges) :
    e.1 ∈ Rlimit.closedSet ∧ e.2 ∈ Rlimit.closedSet := by
  rw [A.mem_actualPostClosureShortcutEdges_iff] at he
  obtain ⟨s, hs⟩ := he
  have hend :=
    (A.actualClosedClassifiedContactSegmentation s).endpoints_mem_contactSet hs
  exact ⟨A.actualClosedClassifiedContactSegmentation_contactSet_subset s hend.1,
    A.actualClosedClassifiedContactSegmentation_contactSet_subset s hend.2⟩

theorem actualPostClosureShortcutEdges_subset_closed_prod
    (A : PostClosureCompressorAssignment T) :
    A.actualPostClosureShortcutEdges ⊆ Rlimit.closedSet ×ˢ Rlimit.closedSet := by
  intro e he
  exact A.actualPostClosureShortcutEdges_endpoints_closed he

/-- Actual shortcuts are edges of the limiting-reference imaginary graph. -/
theorem actualPostClosureShortcutEdges_subset_imaginaryGraph
    (A : PostClosureCompressorAssignment T) :
    A.actualPostClosureShortcutEdges ⊆
      {e | (imaginaryGraph Gamma C.ladder.limitWarp kappa).Adj e.1 e.2} := by
  intro e he
  rw [A.mem_actualPostClosureShortcutEdges_iff] at he
  obtain ⟨s, hs⟩ := he
  exact (A.actualClosedClassifiedContactSegmentation s).shortcutEdges_subset_imaginaryGraph hs

/-- The relation appearing in the source construction: the literal later-row
inside restriction together with the classified shortcuts. -/
def actualPostClosureClosedEdges (A : PostClosureCompressorAssignment T) :
    Set (V × V) :=
  sourceInsideEdges T.interval.ambientInterval Rlimit.closedSet ∪
    A.actualPostClosureShortcutEdges

/-- Every edge of the actual inside-plus-shortcut relation has both endpoints
in the final closed set. -/
theorem actualPostClosureClosedEdges_endpoints_closed
    (A : PostClosureCompressorAssignment T) {e : V × V}
    (he : e ∈ A.actualPostClosureClosedEdges) :
    e.1 ∈ Rlimit.closedSet ∧ e.2 ∈ Rlimit.closedSet := by
  rcases he with he | he
  · exact he.2
  · exact A.actualPostClosureShortcutEdges_endpoints_closed he

theorem actualPostClosureClosedEdges_subset_closed_prod
    (A : PostClosureCompressorAssignment T) :
    A.actualPostClosureClosedEdges ⊆
      Rlimit.closedSet ×ˢ Rlimit.closedSet := by
  intro e he
  exact A.actualPostClosureClosedEdges_endpoints_closed he

/-- The actual inside-plus-shortcut relation is a subrelation of the global
limiting-reference imaginary graph. -/
theorem actualPostClosureClosedEdges_subset_imaginaryGraph
    (A : PostClosureCompressorAssignment T) :
    A.actualPostClosureClosedEdges ⊆
      {e | (imaginaryGraph Gamma C.ladder.limitWarp kappa).Adj e.1 e.2} := by
  rintro e (he | he)
  · exact original_adj_imaginaryGraph (familyEdges_subset_adj _ he.1)
  · exact A.actualPostClosureShortcutEdges_subset_imaginaryGraph he

/-- No shortcut of the actual closed relation enters the old stage roof. -/
theorem actualPostClosureShortcutEdge_head_not_mem_currentRoof
    (A : PostClosureCompressorAssignment T)
    {x y : V} (hxy : (x, y) ∈ A.actualPostClosureShortcutEdges) :
    y ∉ Gamma.roof C.newSlice := by
  rw [A.mem_actualPostClosureShortcutEdges_iff] at hxy
  obtain ⟨s, hxy⟩ := hxy
  exact A.segmentation_shortcut_head_not_mem_currentRoof s
    (A.actualClosedClassifiedContactSegmentation s)
    (A.actualClosedClassifiedContactSegmentation_contactSet_subset s) hxy

/-- Neither the literal inside row nor an actual shortcut enters the old
stage roof. -/
theorem actualPostClosureClosedEdge_head_not_mem_currentRoof
    (A : PostClosureCompressorAssignment T)
    {x y : V} (hxy : (x, y) ∈ A.actualPostClosureClosedEdges) :
    y ∉ Gamma.roof C.newSlice := by
  rcases hxy with hinside | hshortcut
  · exact T.intervalFamilyEdge_head_not_mem_currentRoof hinside.1
  · exact A.actualPostClosureShortcutEdge_head_not_mem_currentRoof hshortcut

/-- The source-faithful fresh relation creates no incoming edge at a current
blueprint vertex. -/
theorem actualPostClosureClosedEdges_noIncoming_current
    (A : PostClosureCompressorAssignment T)
    {currentClosed : Set V}
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent) :
    ∀ {x y : V}, x ∈ current.vertexSet →
      (y, x) ∈ A.actualPostClosureClosedEdges → False := by
  intro x y hx hxy
  exact (A.actualPostClosureClosedEdge_head_not_mem_currentRoof hxy)
    (hcurrent.vertices_roofed hx)

/-- The actual closed relation is edge-disjoint from every current blueprint
at the old slice. -/
theorem current_edgeSet_disjoint_actualPostClosureClosedEdges
    (A : PostClosureCompressorAssignment T)
    {currentClosed : Set V}
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent) :
    Disjoint current.edgeSet A.actualPostClosureClosedEdges := by
  rw [Set.disjoint_left]
  intro e heCurrent heFresh
  change e ∈ familyEdges (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa)
    current.paths at heCurrent
  have hend := familyEdges_subset_vertexSet_prod
    (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa) current.paths heCurrent
  exact (A.actualPostClosureClosedEdge_head_not_mem_currentRoof heFresh)
    (hcurrent.vertices_roofed hend.2)

/-! ## Exact boundary of the shortcut-only construction -/

/-- A finite mixed contact piece is either represented by its shortcut,
already lies wholly in the closed set, or is one of the two genuinely
endpoint-covered cases.  The latter two cases are the exact remaining
source/sink seam; they must not be silently replaced by the piece's forward
corridor. -/
theorem finitePiece_shortcut_or_closed_or_endpointCovered
    {Q : AltPath Gamma.graph} {X : Set V} {u v : V}
    (P : ClassifiedOrClosedFiniteContactPiece
      (Y := C.ladder.limitWarp) (kappa := kappa) Q X u v) :
    (u, v) ∈ P.shortcutEdges ∨ P.path.vertexSet ⊆ X ∨
      Nonempty (ClosedReferenceOwner C.ladder.limitWarp X u) ∨
      Nonempty (ClosedReferenceOwner C.ladder.limitWarp X v) := by
  cases P with
  | closed P => exact Or.inr (Or.inl P.contained)
  | classified P =>
      cases hclass : P.classification with
      | imaginary h =>
          left
          simp [ClassifiedOrClosedFiniteContactPiece.shortcutEdges,
            ClassifiedFiniteContactPiece.shortcutEdges, hclass]
      | initialCovered owner => exact Or.inr (Or.inr (Or.inl ⟨owner⟩))
      | terminalCovered owner => exact Or.inr (Or.inr (Or.inr ⟨owner⟩))

/-- A globally classified infinite tail either supplies the required
popular sink or exposes the remaining covered-initial obstruction. -/
theorem infiniteTail_popular_or_initialCovered
    {Q : AltPath Gamma.graph} {X : Set V} {u : V}
    (P : ClassifiedInfiniteContactTail
      (Y := C.ladder.limitWarp) (kappa := kappa)
      Q X C.persistent u) :
    IsPopular Gamma C.ladder.limitWarp C.persistent kappa u ∨
      Nonempty (ClosedReferenceOwner C.ladder.limitWarp X u) := by
  cases P.classification with
  | popular h => exact Or.inl h
  | initialCovered owner => exact Or.inr ⟨owner⟩

/-- A finite piece already known to lie in the closed set contributes all
of its forward edges to the literal row restriction `W[X]`. -/
theorem closedPiece_forwardEdges_subset_sourceInside
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference
        Rlimit.closedSet)})
    {u v : V}
    (P : ClosedFiniteContactPiece
      (A.assignment.produced.bracket.assignment.assigned s)
      Rlimit.closedSet u v) :
    P.path.directionEdges .forward ⊆
      sourceInsideEdges T.interval.ambientInterval Rlimit.closedSet := by
  intro e he
  have heParent := P.forwardEdges_subset_original he
  simp only [AltPath.directionEdges, Set.mem_iUnion] at heParent
  obtain ⟨lParent, hlParent, hdirParent, helParent⟩ := heParent
  have heRow : e ∈ familyEdges T.interval.ambientInterval :=
    A.toPostClosureProducedAssignment.assigned_forwardLink_edges_subset_intervalFamily
      s lParent hlParent hdirParent helParent
  simp only [AltPath.directionEdges, Set.mem_iUnion] at he
  obtain ⟨l, hl, _hdir, hel⟩ := he
  have hend := l.path.edgeSet_subset_support_prod hel
  have htail : e.1 ∈ Rlimit.closedSet :=
    P.contained (P.path.link_support_subset_vertexSet hl hend.1)
  have hhead : e.2 ∈ Rlimit.closedSet :=
    P.contained (P.path.link_support_subset_vertexSet hl hend.2)
  exact ⟨heRow, htail, hhead⟩

#print axioms actualPostClosureShortcutEdges_endpoints_closed
#print axioms actualPostClosureClosedEdges_endpoints_closed
#print axioms actualPostClosureClosedEdges_subset_imaginaryGraph
#print axioms actualPostClosureClosedEdge_head_not_mem_currentRoof
#print axioms current_edgeSet_disjoint_actualPostClosureClosedEdges
#print axioms finitePiece_shortcut_or_closed_or_endpointCovered
#print axioms infiniteTail_popular_or_initialCovered
#print axioms closedPiece_forwardEdges_subset_sourceInside

end PostClosureCompressorAssignment
end Erdos599.Blueprint.LinkageBlueprint
