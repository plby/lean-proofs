/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayInsideCutCarrierCore
import ErdosProblems.Erdos599.HalfwayOutsideMacroGlobalRelation

/-!
# Exact carrier and blueprint for the global outside-macro relation

The pure relation does not remember isolated attachment vertices.  Its
source-faithful carrier is the focused inside-cut carrier, which retains all
uncovered cut roots and sinks, together with every endpoint of a globally
classified outside edge.  The exact orientation constructor then realizes
the genuine limiting-reference relation without changing either its edge
set or this carrier.
-/

noncomputable section

open Cardinal Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Yglobal : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace ClubStageGeometry

variable (C : ClubStageGeometry Gamma Yglobal kappa (Order.succ kappa))

/-- Vertices incident with a globally classified outside edge. -/
noncomputable def outsideMacroRetainedIncidentCarrier
    {W : Set Gamma.DPath} {X : Set V}
    {before innerRoof outerRoof persistent : Set V}
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (A : OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := W) (X := X))
    (hW : Gamma.IsWarp W)
    (hsource : Gamma.initialSet W \ Gamma.initialSet C.selectedReference ⊆
      before ∩ innerRoof)
    (hterminal : Gamma.terminalFrontier W \
        Gamma.vertexSet C.selectedReference ⊆ before ∩ outerRoof)
    (hclosed : HammockClosedUpTo Gamma C.selectedReference X
      before innerRoof outerRoof kappa) : Set V :=
  {x | ∃ y,
    (x, y) ∈ C.outsideMacroRetainedEdges (persistent := persistent)
      hSafeRoof A hW hsource hterminal hclosed ∨
    (y, x) ∈ C.outsideMacroRetainedEdges (persistent := persistent)
      hSafeRoof A hW hsource hterminal hclosed}

/-- Exact carrier of the globally reclassified transaction. -/
noncomputable def outsideMacroGlobalCarrier
    {W : Set Gamma.DPath} {X : Set V}
    {before innerRoof outerRoof persistent : Set V}
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (A : OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := W) (X := X))
    (hW : Gamma.IsWarp W)
    (hsource : Gamma.initialSet W \ Gamma.initialSet C.selectedReference ⊆
      before ∩ innerRoof)
    (hterminal : Gamma.terminalFrontier W \
        Gamma.vertexSet C.selectedReference ⊆ before ∩ outerRoof)
    (hclosed : HammockClosedUpTo Gamma C.selectedReference X
      before innerRoof outerRoof kappa) : Set V :=
  FocusedInsideCut.carrier C.selectedReference W X ∪
    C.outsideMacroRetainedIncidentCarrier (persistent := persistent)
      hSafeRoof A hW hsource hterminal hclosed

/-- Every relation edge has both endpoints in the exact carrier. -/
theorem outsideMacroGlobalRelation_endpoints_mem_carrier
    {W : Set Gamma.DPath} {X : Set V}
    {before innerRoof outerRoof persistent : Set V}
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (A : OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := W) (X := X))
    (hW : Gamma.IsWarp W)
    (hsource : Gamma.initialSet W \ Gamma.initialSet C.selectedReference ⊆
      before ∩ innerRoof)
    (hterminal : Gamma.terminalFrontier W \
        Gamma.vertexSet C.selectedReference ⊆ before ∩ outerRoof)
    (hclosed : HammockClosedUpTo Gamma C.selectedReference X
      before innerRoof outerRoof kappa)
    (e : V × V)
    (he : e ∈ C.outsideMacroGlobalRelation (persistent := persistent)
      hSafeRoof A hW hsource hterminal hclosed) :
    e.1 ∈ C.outsideMacroGlobalCarrier (persistent := persistent)
        hSafeRoof A hW hsource hterminal hclosed ∧
      e.2 ∈ C.outsideMacroGlobalCarrier (persistent := persistent)
        hSafeRoof A hW hsource hterminal hclosed := by
  rcases he with he | he
  · have hend : e.1 ∈ FocusedInsideCut.carrier C.selectedReference W X ∧
        e.2 ∈ FocusedInsideCut.carrier C.selectedReference W X := by
      exact FocusedInsideCut.edge_endpoints W X he
    exact ⟨Or.inl hend.1, Or.inl hend.2⟩
  · exact ⟨Or.inr ⟨e.2, Or.inl he⟩,
      Or.inr ⟨e.1, Or.inr he⟩⟩

/-- The exact carrier still lies on the honest later row. -/
theorem outsideMacroGlobalCarrier_subset_row
    {W : Set Gamma.DPath} {X : Set V}
    {before innerRoof outerRoof persistent : Set V}
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (A : OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := W) (X := X))
    (hW : Gamma.IsWarp W)
    (hsub : outsideReference C.selectedReference X ⊆
      outsideReference W X)
    (hsource : Gamma.initialSet W \ Gamma.initialSet C.selectedReference ⊆
      before ∩ innerRoof)
    (hterminal : Gamma.terminalFrontier W \
        Gamma.vertexSet C.selectedReference ⊆ before ∩ outerRoof)
    (hclosed : HammockClosedUpTo Gamma C.selectedReference X
      before innerRoof outerRoof kappa) :
    C.outsideMacroGlobalCarrier (persistent := persistent)
        hSafeRoof A hW hsource hterminal hclosed ⊆ Gamma.vertexSet W := by
  intro x hx
  rcases hx with hx | hx
  · exact FocusedInsideCut.carrier_subset_vertexSet
      C.selectedReference W X hx
  · obtain ⟨y, hxy | hyx⟩ := hx
    · obtain ⟨p, hpW, hxp, _⟩ :=
        C.outsideMacroRetainedEdge_has_rowOwner hSafeRoof A hW hsub hsource
          hterminal hclosed hxy
      exact ⟨p, hpW, hxp⟩
    · obtain ⟨p, hpW, _, hxp⟩ :=
        C.outsideMacroRetainedEdge_has_rowOwner hSafeRoof A hW hsub hsource
          hterminal hclosed hyx
      exact ⟨p, hpW, hxp⟩

/-- Any honest boundary satisfied by the whole later row is inherited by the
exact global carrier.  This is the common source of both the roof and closure
fields in the moving `9.31` transaction. -/
theorem outsideMacroGlobalCarrier_subset_of_row_subset
    {W : Set Gamma.DPath} {X S : Set V}
    {before innerRoof outerRoof persistent : Set V}
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (A : OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := W) (X := X))
    (hW : Gamma.IsWarp W)
    (hsub : outsideReference C.selectedReference X ⊆
      outsideReference W X)
    (hsource : Gamma.initialSet W \ Gamma.initialSet C.selectedReference ⊆
      before ∩ innerRoof)
    (hterminal : Gamma.terminalFrontier W \
        Gamma.vertexSet C.selectedReference ⊆ before ∩ outerRoof)
    (hclosed : HammockClosedUpTo Gamma C.selectedReference X
      before innerRoof outerRoof kappa)
    (hrow : Gamma.vertexSet W ⊆ S) :
    C.outsideMacroGlobalCarrier (persistent := persistent)
        hSafeRoof A hW hsource hterminal hclosed ⊆ S :=
  (C.outsideMacroGlobalCarrier_subset_row hSafeRoof A hW hsub hsource
    hterminal hclosed).trans hrow

/-- A `kappa`-sized later row gives a `kappa`-sized exact carrier. -/
theorem mk_outsideMacroGlobalCarrier_le
    {W : Set Gamma.DPath} {X : Set V}
    {before innerRoof outerRoof persistent : Set V}
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (A : OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := W) (X := X))
    (hW : Gamma.IsWarp W)
    (hsub : outsideReference C.selectedReference X ⊆
      outsideReference W X)
    (hsource : Gamma.initialSet W \ Gamma.initialSet C.selectedReference ⊆
      before ∩ innerRoof)
    (hterminal : Gamma.terminalFrontier W \
        Gamma.vertexSet C.selectedReference ⊆ before ∩ outerRoof)
    (hclosed : HammockClosedUpTo Gamma C.selectedReference X
      before innerRoof outerRoof kappa)
    (hkappa : aleph0 ≤ kappa) (hWcard : #W ≤ kappa) :
    #(C.outsideMacroGlobalCarrier (persistent := persistent)
        hSafeRoof A hW hsource hterminal hclosed) ≤ kappa :=
  (Cardinal.mk_le_mk_of_subset
    (C.outsideMacroGlobalCarrier_subset_row hSafeRoof A hW hsub hsource
      hterminal hclosed)).trans
    (CardinalInduction.HalfwayFrontierHeight.mk_vertexSet_le_of_mk_family_le
      hkappa W hWcard)

/-- Exact global relation and carrier realized as a linkage blueprint over
the genuine limiting reference. -/
structure OutsideMacroGlobalCarrierGeometry
    {W : Set Gamma.DPath} {X : Set V}
    {before innerRoof outerRoof persistent : Set V}
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (A : OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := W) (X := X))
    (hW : Gamma.IsWarp W)
    (hsource : Gamma.initialSet W \ Gamma.initialSet C.selectedReference ⊆
      before ∩ innerRoof)
    (hterminal : Gamma.terminalFrontier W \
        Gamma.vertexSet C.selectedReference ⊆ before ∩ outerRoof)
    (hclosed : HammockClosedUpTo Gamma C.selectedReference X
      before innerRoof outerRoof kappa) where
  blueprint : LinkageBlueprint Gamma C.ladder.limitWarp kappa
  edgeSet_eq : blueprint.edgeSet =
    C.outsideMacroGlobalRelation (persistent := persistent)
      hSafeRoof A hW hsource hterminal hclosed
  vertexSet_eq : blueprint.vertexSet =
    C.outsideMacroGlobalCarrier (persistent := persistent)
      hSafeRoof A hW hsource hterminal hclosed

/-- Construct the exact carrier-preserving global blueprint. -/
theorem exists_outsideMacroGlobalCarrierGeometry
    {W : Set Gamma.DPath} {X : Set V}
    {before innerRoof outerRoof persistent : Set V}
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (A : OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := W) (X := X))
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hsub : outsideReference C.selectedReference X ⊆
      outsideReference W X)
    (hnontrivial : A.AssignedEndpointsNontrivial)
    (hsource : Gamma.initialSet W \ Gamma.initialSet C.selectedReference ⊆
      before ∩ innerRoof)
    (hterminal : Gamma.terminalFrontier W \
        Gamma.vertexSet C.selectedReference ⊆ before ∩ outerRoof)
    (hclosed : HammockClosedUpTo Gamma C.selectedReference X
      before innerRoof outerRoof kappa) :
    Nonempty (OutsideMacroGlobalCarrierGeometry (persistent := persistent)
      C hSafeRoof A hW hsource hterminal hclosed) := by
  let E := C.outsideMacroGlobalRelation (persistent := persistent)
    hSafeRoof A hW hsource hterminal hclosed
  let K := C.outsideMacroGlobalCarrier (persistent := persistent)
    hSafeRoof A hW hsource hterminal hclosed
  obtain ⟨O, hOE, hOK⟩ := exists_forwardOrientation_exact E K
    (C.outsideMacroGlobalRelation_subset_imaginaryGraph
      hSafeRoof A hW hsource hterminal hclosed)
    (C.outsideMacroGlobalRelation_endpoints_mem_carrier
      hSafeRoof A hW hsource hterminal hclosed)
    (C.outsideMacroGlobalRelation_biUnique hSafeRoof A hW hsub hsource
      hterminal hclosed)
    (C.outsideMacroGlobalRelation_acyclic hSafeRoof A hW hWfinite hsub
      hnontrivial hsource hterminal hclosed)
    (C.outsideMacroGlobalRelation_no_reverse_ray hSafeRoof A hW hWfinite hsub
      hnontrivial hsource hterminal hclosed)
  exact ⟨{
    blueprint := orientationBlueprint O
    edgeSet_eq := by rw [orientationBlueprint_edgeSet, hOE]
    vertexSet_eq := by rw [orientationBlueprint_vertexSet, hOK] }⟩

#print axioms exists_outsideMacroGlobalCarrierGeometry
#print axioms outsideMacroGlobalCarrier_subset_row

end ClubStageGeometry
end Erdos599.Blueprint.LinkageBlueprint
