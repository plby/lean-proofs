/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Halfway930OldSliceCut
import ErdosProblems.Erdos599.HalfwayOutsideMacroSurvivor
import ErdosProblems.Erdos599.HalfwayOldStageOutsideReference
import ErdosProblems.Erdos599.HalfwayOldStageSplicedBoundary

/-!
# The closed old-slice macro transaction

After the exceptional old-to-new interval components and every selected-
reference component meeting them have been swallowed by the joint closed
set, the honest outside part of the spliced interval row is literally the
honest outside part of the selected reference.  This equality is stronger
than the one-sided inclusion needed by the macro-assignment theorem.

It has two useful consequences which are recorded here.  First, there are
no uncovered outside-row initials, so the simultaneous assignment has no
sources and contributes no compressed edge.  Second, both uncovered cut
boundaries are empty, hence the canonical inside carrier is contained in
the actual closed set.  Thus the local relation has the roof, cardinality,
sink, and ray geometry required by the stage compiler without any invented
endpoint-location callback.
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

/-- The actual closed interval transaction, together with the literal
outside-row identity. -/
structure OldSliceMacroTransaction
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
    {W : LinkageBlueprint Gamma C.selectedReference kappa} {u : V}
    (P : OldSlice930IntervalTransaction C W u) where
  outside_eq :
    outsideReference P.interval.splicedIntervalRow P.closed.closedSet =
      outsideReference C.selectedReference P.closed.closedSet
  assignment : OutsideMacroFullAssignment
    (Y := C.selectedReference) (W := P.interval.splicedIntervalRow)
    (X := P.closed.closedSet)
  inside : CanonicalInsideCut
    (Y := C.selectedReference) (kappa := kappa)
      P.interval.splicedIntervalRow P.closed.closedSet

namespace OldSliceMacroTransaction

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {W : LinkageBlueprint Gamma C.selectedReference kappa}
variable {u : V} {P : OldSlice930IntervalTransaction C W u}

/-- Construct the concrete macro assignment and canonical inside cut from
the honest outside-row equality. -/
theorem exists_of_outside_eq
    (hout :
      outsideReference P.interval.splicedIntervalRow P.closed.closedSet =
        outsideReference C.selectedReference P.closed.closedSet) :
    Nonempty (OldSliceMacroTransaction P) := by
  let A : OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := P.interval.splicedIntervalRow)
      (X := P.closed.closedSet) :=
    (exists_outsideMacroFullAssignment
      P.interval.splicedIntervalRow_tight.1.isWarp
      P.interval.splicedIntervalRow_tight.1.finiteCharacter
      C.selectedReference_isWarp C.selectedReference_finiteCharacter
      (by rw [hout]) P.closed.reference_closed).some
  let I : CanonicalInsideCut
      (Y := C.selectedReference) (kappa := kappa)
      P.interval.splicedIntervalRow P.closed.closedSet :=
    canonicalInsideCutOfWarp P.interval.splicedIntervalRow
      P.closed.closedSet P.interval.splicedIntervalRow_tight.1.isWarp
  exact ⟨{ outside_eq := hout, assignment := A, inside := I }⟩

/-- The closed old-slice transaction supplies the outside-row identity, so
the concrete macro transaction is available without an additional
comparison hypothesis. -/
theorem exists_macroTransaction (P : OldSlice930IntervalTransaction C W u) :
    Nonempty (OldSliceMacroTransaction P) :=
  exists_of_outside_eq
    P.closed.outsideReference_splicedIntervalRow_eq_selectedReference

/-- The full local relation.  The assignment summand is retained in the
definition so this object has exactly the shape consumed by the generic
stage compiler. -/
def macroEdge (M : OldSliceMacroTransaction P) : Set (V × V) :=
  M.inside.insideFamily.edgeSet ∪
    assignedFiniteEdges
      (Zf := FracturedWarp.ofWarp
        (outsideReference P.interval.splicedIntervalRow P.closed.closedSet)
        (outsideReference_isWarp
          P.interval.splicedIntervalRow_tight.1.isWarp))
      M.assignment.assignment

/-- The selected simultaneous assignment has no source: every outside-row
initial is already an initial of the selected reference. -/
theorem no_assignment_source (M : OldSliceMacroTransaction P) :
    IsEmpty {z // z ∈ Gamma.initialSet
      (outsideReference P.interval.splicedIntervalRow P.closed.closedSet) \
        Gamma.initialSet C.selectedReference} := by
  constructor
  rintro ⟨x, hxout, hxnot⟩
  rw [M.outside_eq] at hxout
  exact hxnot (initialSet_outsideReference_subset hxout)

/-- Consequently the compressed assignment edge set is empty. -/
theorem assignedFiniteEdges_eq_empty (M : OldSliceMacroTransaction P) :
    assignedFiniteEdges
      (Zf := FracturedWarp.ofWarp
        (outsideReference P.interval.splicedIntervalRow P.closed.closedSet)
        (outsideReference_isWarp
          P.interval.splicedIntervalRow_tight.1.isWarp))
      M.assignment.assignment = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.2
  intro e he
  obtain ⟨s, _hterminal, _hs⟩ := he
  exact M.no_assignment_source.false s

/-- The local relation is literally the canonical inside relation. -/
theorem macroEdge_eq_inside (M : OldSliceMacroTransaction P) :
    M.macroEdge = M.inside.insideFamily.edgeSet := by
  rw [macroEdge, M.assignedFiniteEdges_eq_empty, Set.union_empty]

/-- Both uncovered cut boundaries are empty, so every carrier vertex lies
in the genuine joint closed set. -/
theorem carrier_subset_closedSet (M : OldSliceMacroTransaction P) :
    M.inside.insideFamily.vertexSet ⊆ P.closed.closedSet := by
  intro x hx
  rw [M.inside.vertexSet_eq] at hx
  rcases hx with (hxinternal | hxinitial) | hxterminal
  · exact hxinternal.2
  · have hxout : x ∈ Gamma.initialSet
        (outsideReference P.interval.splicedIntervalRow
          P.closed.closedSet) := by
      rw [← cutInitial_eq_initialSet_outsideReference
        P.interval.splicedIntervalRow_tight.1.isWarp
        P.interval.splicedIntervalRow_tight.1.finiteCharacter
        P.closed.interval_closed]
      exact hxinitial.1
    rw [M.outside_eq] at hxout
    exact False.elim (hxinitial.2
      (initialSet_outsideReference_subset hxout))
  · have hxout : x ∈ Gamma.terminalFrontier
        (outsideReference P.interval.splicedIntervalRow
          P.closed.closedSet) := by
      rw [← cutTerminal_eq_terminalFrontier_outsideReference
        P.interval.splicedIntervalRow_tight.1.isWarp
        P.interval.splicedIntervalRow_tight.1.finiteCharacter
        P.closed.interval_closed]
      exact hxterminal.1
    rw [M.outside_eq] at hxout
    exact False.elim (hxterminal.2
      (vertexSet_outsideReference_subset
        (by
          obtain ⟨p, hp, hterminal⟩ := hxout
          exact ⟨p, hp, Gamma.terminal_mem_support hterminal⟩)))

/-- The concrete carrier is roofed by the actual closed-set conclusion. -/
theorem carrier_subset_outerRoof (M : OldSliceMacroTransaction P) :
    M.inside.insideFamily.vertexSet ⊆ C.outerRoof :=
  M.carrier_subset_closedSet.trans P.closed.contained_in_roof

/-- The concrete carrier has the current-cardinal bound. -/
theorem mk_carrier_le (M : OldSliceMacroTransaction P) :
    #M.inside.insideFamily.vertexSet ≤ kappa :=
  (Cardinal.mk_subtype_mono M.carrier_subset_closedSet).trans
    P.closed.card_closedSet

/-- The exact relation is bi-unique. -/
theorem macroEdge_biUnique (M : OldSliceMacroTransaction P) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ M.macroEdge) := by
  rw [M.macroEdge_eq_inside]
  change Relator.BiUnique (fun x y ↦
    (x, y) ∈ familyEdges
      (Γ := imaginaryWeb Gamma C.selectedReference kappa)
        M.inside.insideFamily.paths)
  exact Alternating.IsWarp.familyEdges_biUnique M.inside.insideFamily.isWarp

/-- The canonical row rank strictly increases on the local relation. -/
theorem macroEdge_rank (M : OldSliceMacroTransaction P) {x y : V}
    (hxy : (x, y) ∈ M.macroEdge) :
    laterRowRank P.interval.splicedIntervalRow
        P.interval.splicedIntervalRow_tight.1.isWarp x <
      laterRowRank P.interval.splicedIntervalRow
        P.interval.splicedIntervalRow_tight.1.isWarp y := by
  rw [M.macroEdge_eq_inside] at hxy
  exact M.inside.inside_rank_laterRowRank
    P.interval.splicedIntervalRow_tight.1.isWarp hxy

/-- Every local sink lies on the later club frontier. -/
theorem sink_subset_newSlice (M : OldSliceMacroTransaction P) :
    {x | x ∈ M.inside.insideFamily.vertexSet ∧
      ¬ ∃ y, (x, y) ∈ M.macroEdge} ⊆ C.newSlice := by
  intro x hx
  apply M.inside.macroFullSinkBoundary M.assignment
    P.interval.splicedIntervalRow_tight.1.isWarp
    P.interval.splicedIntervalRow_tight.1.finiteCharacter
    P.closed.reference_closed
    (by rw [M.outside_eq]) P.closed.interval_closed
    P.interval.terminalFrontier_splicedIntervalRow_subset_newSlice
  simpa only [macroEdge] using hx

/-- The finite-character row excludes forward rays in the local relation. -/
theorem no_directedRay (M : OldSliceMacroTransaction P) :
    ¬ ContainsDirectedRay M.macroEdge := by
  exact M.inside.macroFullRelation_noDirectedRay M.assignment
    P.interval.splicedIntervalRow_tight.1.isWarp
    P.interval.splicedIntervalRow_tight.1.finiteCharacter
    (by rw [M.outside_eq])

/-- Hence the strong-ray field of the stage record holds vacuously. -/
theorem every_relation_ray_strong (M : OldSliceMacroTransaction P) :
    ∀ r : Ray (imaginaryGraph Gamma C.selectedReference kappa),
      r.edgeSet ⊆ M.macroEdge → (strongEdgeIndices r).Infinite := by
  exact M.inside.macroEveryRelationRayStrong M.assignment
    P.interval.splicedIntervalRow_tight.1.isWarp
    P.interval.splicedIntervalRow_tight.1.finiteCharacter
    (by rw [M.outside_eq])

end OldSliceMacroTransaction

#print axioms OldSliceMacroTransaction.exists_of_outside_eq
#print axioms OldSliceMacroTransaction.exists_macroTransaction
#print axioms OldSliceMacroTransaction.carrier_subset_closedSet
#print axioms OldSliceMacroTransaction.no_directedRay

end LinkageBlueprint
end Blueprint
end Erdos599
