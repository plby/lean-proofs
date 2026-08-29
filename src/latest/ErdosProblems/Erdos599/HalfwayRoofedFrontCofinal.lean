/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayRoofedFrontFinite
import ErdosProblems.Erdos599.HalfwayContactBoundary
import ErdosProblems.Erdos599.HalfwayCofinalBlueprintRelation

/-!
# Compiling the roofed front track into the cofinal scheduler

The simultaneous target-tail attachment resolves the terminal set of one
roofed front, but it deliberately does not claim that unrelated real edges
of the incoming blueprint survive.  This file records the exact two-track
interface needed after that construction.

The `front` track is finite, edge-real, and target-resolved.  The `stage`
track is the monotone survivor used by the final scheduler.  The sole bridge
between them is literal inclusion of the front real graph in the survivor
real graph.  In particular no equality of source initials and no compatibility
with an incoming old-real track is assumed.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating
open _root_.Erdos599.Alternating.RelationDecomposition

universe u v

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

private theorem walk_edgeSet_restrictGraphOnEdges_local
    {D E : Digraph V} : ∀ {a b : V} (p : Walk D a b)
      (h : ∀ e, e ∈ p.edgeSet → E.Adj e.1 e.2),
      (Walk.restrictGraphOnEdges p h).edgeSet = p.edgeSet
  | _, _, .nil, _ => rfl
  | _, _, .cons e p, h => by
      simp only [Walk.restrictGraphOnEdges, Walk.edgeSet_cons]
      congr 1
      exact walk_edgeSet_restrictGraphOnEdges_local p _

/-- Every carrier vertex of a finite edge-real blueprint whose terminals lie
in `B` has a real suffix to `B`.  No initial-set or ambient-source assertion
is needed. -/
theorem realLinksTo_of_mem_vertexSet_of_edgeReal
    (U : LinkageBlueprint Gamma Y kappa) {B : Set V} {x : V}
    (hfinite : (imaginaryWeb Gamma Y kappa).HasFiniteCharacter U.paths)
    (hreal : U.IsEdgeReal) (hterminal : U.terminalSet ⊆ B)
    (hx : x ∈ U.vertexSet) :
    U.RealLinksTo x B := by
  obtain ⟨p, hpU, hxp⟩ := hx
  obtain ⟨q, rfl⟩ := hfinite hpU
  let qr := U.realFinitePath hreal q hpU
  have hqrSupport : qr.support = q.support := by
    dsimp only [qr, realFinitePath]
    exact q.support_restrictGraphOnEdges _
  have hqrEdge : qr.edgeSet = q.edgeSet := by
    dsimp only [qr, realFinitePath, FinitePath.edgeSet]
    exact walk_edgeSet_restrictGraphOnEdges_local q.walk _
  apply realLinksTo_of_mem_completedRealVertices
  refine ⟨qr, hterminal ⟨.inl q, hpU, rfl⟩, ?_, ?_, ?_⟩
  · intro z hz
    have hzq : z ∈ q.support := by
      exact hqrSupport ▸ hz
    change z ∈ U.realPart.vertices
    rw [realPart_vertices]
    exact ⟨.inl q, hpU, hzq⟩
  · intro e he
    have heq : e ∈ q.edgeSet := by
      exact hqrEdge ▸ he
    exact U.mem_realPart_of_mem_edgeSet_of_original
      (Set.mem_iUnion.2 ⟨(.inl q :
        Path (imaginaryGraph Gamma Y kappa)),
        Set.mem_iUnion.2 ⟨hpU, heq⟩⟩)
      (hreal <| Set.mem_iUnion.2 ⟨(.inl q :
        Path (imaginaryGraph Gamma Y kappa)),
        Set.mem_iUnion.2 ⟨hpU, heq⟩⟩)
  · exact hqrSupport.symm ▸ hxp

/-- Initial-set specialization of
`realLinksTo_of_mem_vertexSet_of_edgeReal`. -/
theorem realLinksTo_of_mem_initialSet_of_edgeReal
    (U : LinkageBlueprint Gamma Y kappa) {B : Set V} {x : V}
    (hfinite : (imaginaryWeb Gamma Y kappa).HasFiniteCharacter U.paths)
    (hreal : U.IsEdgeReal) (hterminal : U.terminalSet ⊆ B)
    (hx : x ∈ U.initialSet) :
    U.RealLinksTo x B := by
  apply U.realLinksTo_of_mem_vertexSet_of_edgeReal
    hfinite hreal hterminal
  obtain ⟨p, hpU, hpstart⟩ := hx
  exact ⟨p, hpU, hpstart.symm ▸ p.initial_mem_support⟩

namespace ClosedOldSlice930MacroTransaction

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {W : LinkageBlueprint Gamma C.selectedReference kappa}
variable {z : V}

/-- The roofed-front target attachment discharges the target phase for the
scheduled vertex exactly when that vertex survives as a literal initial of
the roofed front.  The returned blueprint need not extend the incoming
blueprint. -/
theorem exists_targetResolvedRealLink
    (Q : ClosedOldSlice930MacroTransaction C W z)
    (hlower : CardinalInduction.UniversalCardinalInductionBelow V kappa)
    (hext : CardinalInduction.UniversalExtensionClauseAt V kappa)
    (hz : z ∈ Q.roofedFrontBlueprint.initialSet) :
    ∃ U : LinkageBlueprint Gamma C.selectedReference kappa,
      U.initialSet = Q.roofedFrontBlueprint.initialSet ∧
        U.terminalSet ⊆ Gamma.target ∧ U.IsEdgeReal ∧
        (imaginaryWeb Gamma C.selectedReference kappa).HasFiniteCharacter
          U.paths ∧ U.RealLinksTo z Gamma.target := by
  obtain ⟨U, hUinitial, hUterminal, hUreal, hUfinite⟩ :=
    Q.exists_finiteTargetResolvedRoofedFrontBlueprint hlower hext
  refine ⟨U, hUinitial, hUterminal, hUreal, hUfinite, ?_⟩
  apply U.realLinksTo_of_mem_initialSet_of_edgeReal
    hUfinite hUreal hUterminal
  exact hUinitial.symm ▸ hz

end ClosedOldSlice930MacroTransaction

variable {I : Type v}
variable [Preorder I] [Nonempty I] [IsDirectedOrder I]

/-- The minimal sound two-track output of a roofed-front recursion.

`front i` is the target-attached front selected at stage `i`; `stage i` is
the survivor used in the monotone union.  The construction must prove only
that the scheduled initial of the former and its real graph survive in the
latter. -/
structure CofinalRoofedFrontSurvivor
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (kappa : Cardinal.{u})
    (B : Set V) (I : Type v) [Preorder I] [Nonempty I]
    [IsDirectedOrder I] where
  stage : I → LinkageBlueprint Gamma Y kappa
  front : I → LinkageBlueprint Gamma Y kappa
  scheduled : I → V
  front_finite : ∀ i,
    (imaginaryWeb Gamma Y kappa).HasFiniteCharacter (front i).paths
  front_edgeReal : ∀ i, (front i).IsEdgeReal
  front_terminal : ∀ i, (front i).terminalSet ⊆ B
  scheduled_frontInitial : ∀ i, scheduled i ∈ (front i).initialSet
  front_survives : ∀ i,
    (front i).realPart.Extends (stage i).realPart
  realEdge_mono : Monotone fun i ↦ (stage i).realPart.edges
  carrier_mono : Monotone fun i ↦ (stage i).vertexSet
  countably_bounded : HasCountableUpperBounds I
  fair : ∀ x,
    x ∈ ⋃ i, (stage i).vertexSet →
    (¬ ∃ y, (x, y) ∈ ⋃ i, (stage i).realPart.edges) →
    x ∉ B → ∃ i, scheduled i = x

namespace CofinalRoofedFrontSurvivor

variable {B : Set V}

private theorem stage_resolved
    (R : CofinalRoofedFrontSurvivor Gamma Y kappa B I) (i : I) :
    (R.stage i).RealLinksTo (R.scheduled i) B := by
  apply realLinksTo_mono (R.front_survives i)
  exact (R.front i).realLinksTo_of_mem_initialSet_of_edgeReal
    (R.front_finite i) (R.front_edgeReal i) (R.front_terminal i)
    (R.scheduled_frontInitial i)

private noncomputable def chosenTargetPath
    (R : CofinalRoofedFrontSurvivor Gamma Y kappa B I) (i : I) :
    FinitePath Gamma.graph :=
  Classical.choose (R.stage_resolved i)

private theorem chosenTargetPath_spec
    (R : CofinalRoofedFrontSurvivor Gamma Y kappa B I) (i : I) :
    (R.chosenTargetPath i).start = R.scheduled i ∧
      (R.chosenTargetPath i).finish ∈ B ∧
      (R.chosenTargetPath i).support ⊆ (R.stage i).vertexSet ∧
      (R.chosenTargetPath i).edgeSet ⊆ (R.stage i).realPart.edges := by
  simpa only [chosenTargetPath, realPart_vertices] using
    (Classical.choose_spec (R.stage_resolved i))

/-- Compile the two-track survivor into the exact cofinal real-relation run.
The selected target path is the route carried by the front track, transported
through `front_survives`. -/
noncomputable def toCofinalBlueprintRelationRun
    (R : CofinalRoofedFrontSurvivor Gamma Y kappa B I) :
    CofinalBlueprintRelationRun Gamma Y kappa B I where
  stage := R.stage
  scheduled := R.scheduled
  realEdge_mono := R.realEdge_mono
  carrier_mono := R.carrier_mono
  countably_bounded := R.countably_bounded
  fair := R.fair
  targetPath := R.chosenTargetPath
  targetPath_start := fun i ↦ (R.chosenTargetPath_spec i).1
  targetPath_finish := fun i ↦ (R.chosenTargetPath_spec i).2.1
  targetPath_vertices := fun i ↦ (R.chosenTargetPath_spec i).2.2.1
  targetPath_edges := fun i ↦ (R.chosenTargetPath_spec i).2.2.2

end CofinalRoofedFrontSurvivor

namespace CofinalBlueprintRelationRun

variable {C : ClubStageGeometry Gamma Y kappa (Order.succ kappa)}

/-- The untouched selected-reference remainder is endpoint-pure once the
exact source boundary of an arbitrary cofinal real-part run is known. -/
theorem referenceEndpointPure_of_sourceBoundary
    (R : CofinalBlueprintRelationRun Gamma Y kappa Gamma.target I)
    (href : Y = C.selectedReference)
    (hsource :
      {x | x ∈ R.finalCarrier ∧ ¬ ∃ y, (y, x) ∈ R.finalEdge} ∪
        Gamma.initialSet
          (referencePathsMeeting Y C.newSlice \
            referencePathsMeeting Y R.finalCarrier) =
        Gamma.source) :
    ∀ p ∈
        (referencePathsMeeting Y C.newSlice \
          referencePathsMeeting Y R.finalCarrier),
      CardinalInduction.IsPathBetween Gamma Gamma.source C.newSlice p := by
  intro p hp
  have hpSource : p.initial ∈ Gamma.source := by
    rw [← hsource]
    exact Or.inr ⟨p, hp, rfl⟩
  have hpSelected : p ∈ C.selectedReference := href ▸ hp.1.1
  exact ladderReference.endpointPure_of_initial_mem_source
    C.normalized C.legal hpSelected hpSource

/-- Exact final root/sink equations and absence of a forward ray compile an
arbitrary cofinal blueprint run to the public club-frontier boundary. -/
theorem rankedClubFrontierBoundary_of_noDirectedRay
    (R : CofinalBlueprintRelationRun Gamma Y kappa Gamma.target I)
    {A0 : Set V}
    (href : Y = C.selectedReference)
    (hdesignatedSource : A0 ⊆ Gamma.source)
    (hdesignatedRoot : A0 ⊆
      {x | x ∈ R.finalCarrier ∧ ¬ ∃ y, (y, x) ∈ R.finalEdge})
    (hsource :
      {x | x ∈ R.finalCarrier ∧ ¬ ∃ y, (y, x) ∈ R.finalEdge} ∪
        Gamma.initialSet
          (referencePathsMeeting Y C.newSlice \
            referencePathsMeeting Y R.finalCarrier) =
        Gamma.source)
    (hterminal :
      {x | x ∈ R.finalCarrier ∧ ¬ ∃ y, (x, y) ∈ R.finalEdge} ∪
        Gamma.terminalFrontier
          (referencePathsMeeting Y C.newSlice \
            referencePathsMeeting Y R.finalCarrier) =
        C.newSlice)
    (hnoRay : ¬ ContainsDirectedRay R.finalEdge) :
    CardinalInduction.HalfwayScheduler.RankedClubFrontierBoundary C
      R.rankedFairGlobalRelation A0 := by
  refine {
    reference_isWarp := by
      rw [href]
      exact C.selectedReference_isWarp
    designated_source := hdesignatedSource
    designated_root := hdesignatedRoot
    source_cover := hsource
    terminal_frontier := hterminal
    blueprint_endpointPure := ?_
    reference_endpointPure := ?_ }
  · exact blueprintEndpointPure_of_boundary R.rankedFairGlobalRelation
      C.newSlice hnoRay hsource hterminal
  · exact R.referenceEndpointPure_of_sourceBoundary href hsource

end CofinalBlueprintRelationRun

#print axioms realLinksTo_of_mem_initialSet_of_edgeReal
#print axioms
  ClosedOldSlice930MacroTransaction.exists_targetResolvedRealLink
#print axioms CofinalRoofedFrontSurvivor.toCofinalBlueprintRelationRun
#print axioms
  CofinalBlueprintRelationRun.rankedClubFrontierBoundary_of_noDirectedRay

end LinkageBlueprint
end Blueprint
end Erdos599
