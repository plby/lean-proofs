/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayLinkageFirstClosure
import ErdosProblems.Erdos599.HalfwayOutsideMacroSurvivor
import ErdosProblems.Erdos599.HalfwayLadderReference

/-!
# Absorbing marker-starting reference paths before the outside macro assignment

The selected ladder reference is not, in general, a subfamily of a linkage
whose initial set is contained in the original source.  Its marker-starting
members begin outside that source.  Consequently the condition that the whole
selected reference be retained in the later linkage is false in the public
half-way construction.

The dependency-correct replacement is local to the selected cut.  Retain the
source-starting part of the reference in the later linkage, put the initials
of the marker-starting part in the closing seed, and close under the whole
reference.  Every marker-starting component is then swallowed by the closed
set.  Thus every reference component which survives in the honest outside
subwarp is source-starting and belongs to the later linkage.

This file carries out that construction.  Its output contains the actual
closed set, the actual macro-owned simultaneous assignment, and the canonical
inside family; it is not a proposition-valued boundary adapter.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y W : Set Gamma.DPath}
variable {X : Set V} {kappa : Cardinal.{u}}

/-- If the source-starting reference paths are retained by `W` and the
initials of all remaining reference paths are absorbed by `X`, then the
honest outside reference is a subwarp of the honest outside row.

Only this pruned inclusion, rather than the generally false `Y ⊆ W`, is
used by the macro assignment and survivor-rank constructions. -/
theorem outsideReference_subset_of_sourceRetained_markerInitialsAbsorbed
    (hsource : {p | p ∈ Y ∧ p.initial ∈ Gamma.source} ⊆ W)
    (hmarker : Gamma.initialSet
      {p | p ∈ Y ∧ p.initial ∉ Gamma.source} ⊆ X) :
    outsideReference Y X ⊆ outsideReference W X := by
  intro p hp
  refine ⟨hsource ⟨hp.1, ?_⟩, hp.2⟩
  by_contra hpSource
  have hpInitial : p.initial ∈ Gamma.initialSet
      {q | q ∈ Y ∧ q.initial ∉ Gamma.source} :=
    ⟨p, ⟨hp.1, hpSource⟩, rfl⟩
  exact Set.disjoint_left.1 hp.2 p.initial_mem_support
    (hmarker hpInitial)

/-- Once the closing operation is path-closed under the reference, absorbing
the marker initials absorbs every vertex of every marker-starting component. -/
theorem markerStarting_vertexSet_subset_of_initials_and_closed
    (hmarker : Gamma.initialSet
      {p | p ∈ Y ∧ p.initial ∉ Gamma.source} ⊆ X)
    (hclosed : ClosedUnderPaths Gamma Y X) :
    Gamma.vertexSet {p | p ∈ Y ∧ p.initial ∉ Gamma.source} ⊆ X := by
  rintro x ⟨p, hp, hxp⟩
  apply hclosed p hp.1 ⟨p.initial, p.initial_mem_support, ?_⟩ hxp
  exact hmarker ⟨p, hp, rfl⟩

/-- Linkage-first closure data with the sound, split retention condition.
The whole reference remains a closure family, but only its source-starting
part is required to be a member of the later linkage. -/
structure MarkerAbsorbedMacroSeed extends
    LinkageFirstClosureSeed (Gamma := Gamma) (Y := Y) (kappa := kappa) where
  sourceReferenceRetained :
    {p | p ∈ Y ∧ p.initial ∈ Gamma.source} ⊆ later
  markerInitialsSeed : Gamma.initialSet
    {p | p ∈ Y ∧ p.initial ∉ Gamma.source} ⊆ initialSeed
  source_location :
    Gamma.initialSet later \ Gamma.initialSet Y ⊆ before ∩ innerRoof
  terminal_location :
    Gamma.terminalFrontier later \ Gamma.vertexSet Y ⊆
      before ∩ outerRoof

/-- The concrete result of the marker-absorbed closing operation.  Besides
the closure conclusions it stores the pruned outside-subwarp inclusion, the
selected macro assignment, and the canonical inside relation. -/
structure MarkerAbsorbedMacroRequest
    (S : MarkerAbsorbedMacroSeed
      (Gamma := Gamma) (Y := Y) (kappa := kappa)) where
  closureSet : Set V
  initialSeed_subset : S.initialSeed ⊆ closureSet
  closure_card : #closureSet ≤ kappa
  hammock_closed : HammockClosedUpTo Gamma Y closureSet
    S.before S.innerRoof S.outerRoof kappa
  large_closed : LargeHammockClosed Gamma Y closureSet
    S.before S.innerRoof S.outerRoof kappa
  preserving_target_paths : HasPreservingTargetPaths Gamma S.targetSlice
    closureSet S.targetSide S.Preserves
  reference_closed : ClosedUnderPaths Gamma Y closureSet
  later_closed : ClosedUnderPaths Gamma S.later closureSet
  contained_in_roof : ContainedInRoof closureSet S.outerRoof
  markerStarting_absorbed :
    Gamma.vertexSet {p | p ∈ Y ∧ p.initial ∉ Gamma.source} ⊆ closureSet
  outside_subset : outsideReference Y closureSet ⊆
    outsideReference S.later closureSet
  assignment : OutsideMacroFullAssignment
    (Y := Y) (W := S.later) (X := closureSet)
  inside : CanonicalInsideCut
    (Y := Y) (kappa := kappa) S.later closureSet

namespace MarkerAbsorbedMacroSeed

/-- Run the omega closure, absorb all marker-starting reference components,
and construct the actual macro assignment and inside relation. -/
theorem exists_request
    (S : MarkerAbsorbedMacroSeed
      (Gamma := Gamma) (Y := Y) (kappa := kappa)) :
    Nonempty (MarkerAbsorbedMacroRequest S) := by
  obtain ⟨X, hseed, hcard, hclosed, hlarge, htarget,
      hreference, hlater, hroof⟩ :=
    exists_assertions_9_22_to_9_25_with_rowClosure Gamma Y S.later
      kappa kappa S.before S.innerRoof S.outerRoof S.targetSlice
      S.targetSide S.initialSeed S.Preserves S.target_paths
      S.reference_isWarp S.later_isWarp S.reference_in_roof
      S.later_in_roof S.safe_in_roof S.kappa_infinite (le_refl kappa)
      S.before_card S.initial_card S.initial_in_roof
  have hmarkerInitial : Gamma.initialSet
      {p | p ∈ Y ∧ p.initial ∉ Gamma.source} ⊆ X :=
    S.markerInitialsSeed.trans hseed
  have hmarkerVertex :
      Gamma.vertexSet {p | p ∈ Y ∧ p.initial ∉ Gamma.source} ⊆ X :=
    markerStarting_vertexSet_subset_of_initials_and_closed
      hmarkerInitial hreference
  have hsub : outsideReference Y X ⊆ outsideReference S.later X :=
    outsideReference_subset_of_sourceRetained_markerInitialsAbsorbed
      S.sourceReferenceRetained hmarkerInitial
  let A : OutsideMacroFullAssignment
      (Y := Y) (W := S.later) (X := X) :=
    (exists_outsideMacroFullAssignment S.later_isWarp S.later_finite
      S.reference_isWarp S.reference_finite hsub hreference).some
  let I : CanonicalInsideCut
      (Y := Y) (kappa := kappa) S.later X :=
    canonicalInsideCutOfWarp S.later X S.later_isWarp
  exact ⟨{
    closureSet := X
    initialSeed_subset := hseed
    closure_card := hcard
    hammock_closed := hclosed
    large_closed := hlarge
    preserving_target_paths := htarget
    reference_closed := hreference
    later_closed := hlater
    contained_in_roof := hroof
    markerStarting_absorbed := hmarkerVertex
    outside_subset := hsub
    assignment := A
    inside := I }⟩

end MarkerAbsorbedMacroSeed

namespace MarkerAbsorbedMacroRequest

variable {S : MarkerAbsorbedMacroSeed
  (Gamma := Gamma) (Y := Y) (kappa := kappa)}

/-- Regard the macro assignment on the honest outside subwarp as the
bracket assignment on the canonical unfractured `FracturedWarp`.  This
retains the linkwise forward-edge provenance needed when the compressed
imaginary edges are removed by the global transaction. -/
def outsideBracketFracturedAssignment
    (R : MarkerAbsorbedMacroRequest S) :
    FracturedAssignmentPeel.BracketFracturedAssignment
      (FracturedWarp.ofWarp
        (outsideReference S.later R.closureSet)
        (outsideReference_isWarp S.later_isWarp)) Y where
  assignment := R.assignment.assignment
  bracket_safe := R.assignment.full.bracket_safe

@[simp] theorem outsideBracketFracturedAssignment_assignment
    (R : MarkerAbsorbedMacroRequest S) :
    R.outsideBracketFracturedAssignment.assignment =
      R.assignment.assignment := rfl

/-- The selected macro assignment has the literal finite/infinite Claim-2
classification needed by the subsequent transaction compiler. -/
theorem classified
    {persistent : Set V} (R : MarkerAbsorbedMacroRequest S) :
    (∀ s v, (R.assignment.assignment.assigned s).terminal? = some v →
        IsImaginaryEdge Gamma Y kappa s.1 v) ∧
      (∀ s, (R.assignment.assignment.assigned s).IsInfinite →
        IsPopular Gamma Y persistent kappa s.1) :=
  R.assignment.classified S.later_isWarp S.source_location S.terminal_location
    R.hammock_closed

/-- The actual inside-plus-macro relation is bi-unique. -/
theorem relation_biUnique (R : MarkerAbsorbedMacroRequest S) :
    Relator.BiUnique (fun x y ↦
      (x, y) ∈ R.inside.insideFamily.edgeSet ∪
        assignedFiniteEdges
          (Zf := FracturedWarp.ofWarp
            (outsideReference S.later R.closureSet)
            (outsideReference_isWarp S.later_isWarp))
          R.assignment.assignment) :=
  R.inside.macroFullRelation_biUnique R.assignment S.later_isWarp
    S.later_finite R.later_closed

/-- With the honest later-row endpoint geometry, the constructed local
relation is acyclic and has no reverse ray.  Both conclusions use the actual
row rank; no rank callback is accepted. -/
theorem relation_acyclic_and_no_reverse_ray
    (R : MarkerAbsorbedMacroRequest S)
    (hnontrivial : CanonicalInsideCut.AssignedRowPathsNontrivial
      R.assignment) :
    (¬ ContainsDirectedCycle
        (R.inside.insideFamily.edgeSet ∪
          assignedFiniteEdges
            (Zf := FracturedWarp.ofWarp
              (outsideReference S.later R.closureSet)
              (outsideReference_isWarp S.later_isWarp))
            R.assignment.assignment)) ∧
      (¬ ContainsReverseDirectedRay
        (R.inside.insideFamily.edgeSet ∪
          assignedFiniteEdges
            (Zf := FracturedWarp.ofWarp
              (outsideReference S.later R.closureSet)
              (outsideReference_isWarp S.later_isWarp))
            R.assignment.assignment)) := by
  exact ⟨R.inside.insideAssigned_acyclic R.assignment S.later_isWarp
      S.later_finite R.outside_subset hnontrivial,
    R.inside.insideAssigned_no_reverse_ray R.assignment S.later_isWarp
      S.later_finite R.outside_subset hnontrivial⟩

end MarkerAbsorbedMacroRequest

/-! ## Selected-ladder-reference spelling -/

/-- For the public selected reference, the two families in the generic
split are definitionally `sourceStarting` and `markerStarting`. -/
theorem selectedReference_outside_subset_of_split_retention
    {theta : Cardinal.{u}}
    (C : ClubStageGeometry Gamma Y kappa theta)
    {W : Set Gamma.DPath} {X : Set V}
    (hsource : ladderReference.sourceStarting
      (Gamma := Gamma) (L := C.ladder) (a := C.newStage) ⊆ W)
    (hmarker : Gamma.initialSet
      (ladderReference.markerStarting
        (Gamma := Gamma) (L := C.ladder) (a := C.newStage)) ⊆ X) :
    outsideReference C.selectedReference X ⊆ outsideReference W X := by
  exact outsideReference_subset_of_sourceRetained_markerInitialsAbsorbed
    hsource hmarker

end LinkageBlueprint
end Blueprint
end Erdos599
