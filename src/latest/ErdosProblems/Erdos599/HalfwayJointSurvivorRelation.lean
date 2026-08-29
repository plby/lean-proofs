/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayMixedActiveAdvance
import ErdosProblems.Erdos599.Halfway930OldSliceMacroBridge

/-!
# The roofed joint old-real/front survivor relation

The canonical interval macro by itself does not retain the incoming
blueprint.  The first scheduled diamond is the minimal sound joint object:
its real relation retains every incoming real edge and every edge of the
selected front, while its carrier remains inside the later roof and the
joint closed set.  This file records those facts at relation level, without
claiming that the external target suffix is roofed.

The only source-boundary issue left by this local operation is stated as the
literal reference-front absorption condition.  It says that every
source-starting selected-reference component newly met by the front already
has its root in the cut.  Under precisely that switching/provenance fact, the
joint real relation has the source cover required by the global scheduler.
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

/-- The exact remaining reference-contact invariant for a scheduled front.
It is neither replaced by a cardinal estimate nor hidden in a whole-family
replacement record. -/
def SourceReferenceFrontAbsorbed
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
    {W : LinkageBlueprint Gamma C.selectedReference kappa} {z : V}
    (P : OldSlice930IntervalTransaction C W z) : Prop :=
  ∀ p ∈ C.selectedReference,
    p.initial ∈ Gamma.source →
    (p.support ∩ P.interval.front.support).Nonempty →
    p.initial ∈ P.cut.initialSet

/-- Minimal relation-level joint survivor.  Its relation is only the real
part of the first diamond; the ambient target suffix is intentionally kept
outside this roofed object. -/
structure RoofedJointSurvivorRelation
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
    {W : LinkageBlueprint Gamma C.selectedReference kappa} {z : V}
    (P : OldSlice930IntervalTransaction C W z)
    (hW : W.IsLinkageBlueprint C.oldSlice C.oldClosedSet C.persistent) where
  advance : OldSliceDiamondAdvance P hW

namespace RoofedJointSurvivorRelation

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {W : LinkageBlueprint Gamma C.selectedReference kappa}
variable {z : V} {P : OldSlice930IntervalTransaction C W z}
variable {hW : W.IsLinkageBlueprint C.oldSlice C.oldClosedSet C.persistent}

def blueprint (R : RoofedJointSurvivorRelation P hW) :
    LinkageBlueprint Gamma C.selectedReference kappa :=
  R.advance.result

def carrier (R : RoofedJointSurvivorRelation P hW) : Set V :=
  R.blueprint.realPart.vertices

def edge (R : RoofedJointSurvivorRelation P hW) : Set (V × V) :=
  R.blueprint.realPart.edges

@[simp] theorem carrier_eq (R : RoofedJointSurvivorRelation P hW) :
    R.carrier = R.blueprint.vertexSet :=
  rfl

@[simp] theorem edge_eq (R : RoofedJointSurvivorRelation P hW) :
    R.edge = R.blueprint.edgeSet ∩ {e | Gamma.graph.Adj e.1 e.2} :=
  rfl

/-- The concrete closed transaction always has a roofed joint survivor. -/
theorem exists_of_closedMacro
    (Q : ClosedOldSlice930MacroTransaction C W z)
    (hW : W.IsLinkageBlueprint C.oldSlice C.oldClosedSet C.persistent) :
    Nonempty (RoofedJointSurvivorRelation Q.intervalTransaction hW) := by
  obtain ⟨D⟩ := OldSliceDiamondAdvance.exists_diamondAdvance
    Q.intervalTransaction hW
  exact ⟨⟨D⟩⟩

theorem edge_in_graph (R : RoofedJointSurvivorRelation P hW) :
    R.edge ⊆ {e | Gamma.graph.Adj e.1 e.2} :=
  fun _ he ↦ he.2

theorem edge_endpoints (R : RoofedJointSurvivorRelation P hW)
    {e : V × V} (he : e ∈ R.edge) :
    e.1 ∈ R.carrier ∧ e.2 ∈ R.carrier := by
  exact edgeSet_endpoints_mem_vertexSet R.blueprint he.1

theorem edge_biUnique (R : RoofedJointSurvivorRelation P hW) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ R.edge) := by
  have hfull := Alternating.IsWarp.familyEdges_biUnique R.blueprint.isWarp
  constructor
  · intro x y t hxt hyt
    exact hfull.1 hxt.1 hyt.1
  · intro x y t hxy hxt
    exact hfull.2 hxy.1 hxt.1

theorem no_directedCycle (R : RoofedJointSurvivorRelation P hW) :
    ¬ ContainsDirectedCycle R.edge := by
  rintro ⟨cycle, hcycle⟩
  exact PathFilterComponents.DWeb.IsWarp.familyEdges_not_containsDirectedCycle
    R.blueprint.isWarp ⟨cycle, hcycle.trans Set.inter_subset_left⟩

theorem no_reverseDirectedRay (R : RoofedJointSurvivorRelation P hW) :
    ¬ ContainsReverseDirectedRay R.edge := by
  rintro ⟨ray, hray⟩
  exact
    PathFilterComponents.DWeb.IsWarp.familyEdges_not_containsReverseDirectedRay
      R.blueprint.isWarp ⟨ray, fun n ↦ Set.inter_subset_left (hray n)⟩

/-- Every incoming real vertex is present in the joint carrier. -/
theorem old_realVertices (R : RoofedJointSurvivorRelation P hW) :
    W.realPart.vertices ⊆ R.carrier :=
  R.advance.old_vertexSet_subset_result

/-- Every incoming real edge survives literally. -/
theorem old_realEdges (R : RoofedJointSurvivorRelation P hW) :
    W.realPart.edges ⊆ R.edge :=
  R.advance.old_realEdges_subset_result_realEdges

/-- Every selected-front edge is present and remains original. -/
theorem front_realEdges (R : RoofedJointSurvivorRelation P hW) :
    P.interval.front.edgeSet ⊆ R.edge :=
  R.advance.front_edgeSet_subset_result_realEdges

theorem carrier_roofed (R : RoofedJointSurvivorRelation P hW) :
    R.carrier ⊆ Gamma.roof C.newSlice :=
  R.advance.result_vertices_roofed

theorem carrier_closed (R : RoofedJointSurvivorRelation P hW) :
    R.carrier ⊆ P.closed.closedSet :=
  R.advance.result_vertices_closed

/-- The exact local switching/provenance condition implies source coverage
already at the real-relation level.  Dropping non-real edges can create more
roots, never fewer. -/
theorem covers_source
    (R : RoofedJointSurvivorRelation P hW)
    (habsorbed : SourceReferenceFrontAbsorbed P) :
    Gamma.source ⊆
      {x | x ∈ R.carrier ∧ ¬ ∃ y, (y, x) ∈ R.edge} ∪
        Gamma.initialSet
          (referencePathsMeeting C.selectedReference
              (C.oldSlice ∪ C.newSlice) \
            referencePathsMeeting C.selectedReference R.carrier) := by
  have hfull : Gamma.source ⊆
      R.blueprint.initialSet ∪
        R.blueprint.retainedReferenceInitials
          (C.oldSlice ∪ C.newSlice) :=
    R.advance.result_covers_source_iff_referenceFront.2 habsorbed
  intro x hx
  rcases hfull hx with hxInitial | hxReference
  · apply Or.inl
    rw [R.blueprint.initialSet_eq_no_incoming] at hxInitial
    refine ⟨hxInitial.1, ?_⟩
    rintro ⟨y, hyx⟩
    exact hxInitial.2 ⟨y, hyx.1⟩
  · exact Or.inr hxReference

end RoofedJointSurvivorRelation

#print axioms RoofedJointSurvivorRelation.exists_of_closedMacro
#print axioms RoofedJointSurvivorRelation.old_realEdges
#print axioms RoofedJointSurvivorRelation.front_realEdges
#print axioms RoofedJointSurvivorRelation.covers_source

end LinkageBlueprint
end Blueprint
end Erdos599
