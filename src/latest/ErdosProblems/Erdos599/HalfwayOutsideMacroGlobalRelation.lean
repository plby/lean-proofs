/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayOutsideMacroGlobalCompatibility
import ErdosProblems.Erdos599.HalfwayOutsideMacroRetainedBiunique

/-!
# The honest global inside-plus-outside macro relation

This module closes the purely relational part of the limiting-reference
reclassification.  The inside relation is the literal row relation on the
closing set.  The outside relation is the exact source-indexed classified
macro contribution.  Both are bi-unique, and their endpoints lie on opposite
sides of the closing set, so their union is bi-unique as well.

No blueprint carrier, source-cover, or terminal-boundary assertion is made:
isolated boundary vertices still have to be supplied by the moving-stage
geometry before this relation can become a scheduler successor.
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

/-- The actual globally classified inside-plus-outside macro relation. -/
noncomputable def outsideMacroGlobalRelation
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
      before innerRoof outerRoof kappa) : Set (V × V) :=
  outsideMacroInsideEdges W X ∪
    C.outsideMacroRetainedEdges (persistent := persistent)
      hSafeRoof A hW hsource hterminal hclosed

/-- The exact global relation is bi-unique; no compatibility premise is
accepted from the caller. -/
theorem outsideMacroGlobalRelation_biUnique
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
    Relator.BiUnique (fun x y ↦
      (x, y) ∈ C.outsideMacroGlobalRelation (persistent := persistent)
        hSafeRoof A hW hsource hterminal hclosed) := by
  have hinside := outsideMacroInsideEdges_biUnique
    (X := X) hW
  have houtside := C.outsideMacroRetainedEdges_biUnique
    (persistent := persistent) hSafeRoof A hW hsub hsource hterminal hclosed
  constructor
  · intro a b c hac hbc
    rcases hac with hac | hac <;> rcases hbc with hbc | hbc
    · exact hinside.1 hac hbc
    · exact C.outsideMacroInside_retained_cross_in hSafeRoof A hW hsource
        hterminal hclosed hac hbc
    · exact (C.outsideMacroInside_retained_cross_in hSafeRoof A hW hsource
        hterminal hclosed hbc hac).symm
    · exact houtside.1 hac hbc
  · intro a b c hab hac
    rcases hab with hab | hab <;> rcases hac with hac | hac
    · exact hinside.2 hab hac
    · exact C.outsideMacroInside_retained_cross_out hSafeRoof A hW hsource
        hterminal hclosed hab hac
    · exact (C.outsideMacroInside_retained_cross_out hSafeRoof A hW hsource
        hterminal hclosed hac hab).symm
    · exact houtside.2 hab hac

/-- Every edge of the exact global relation belongs to the imaginary graph
formed with the genuine limiting reference. -/
theorem outsideMacroGlobalRelation_subset_imaginaryGraph
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
      before innerRoof outerRoof kappa) :
    C.outsideMacroGlobalRelation (persistent := persistent)
        hSafeRoof A hW hsource hterminal hclosed ⊆
      {e | (imaginaryGraph Gamma C.ladder.limitWarp kappa).Adj e.1 e.2} := by
  rintro e (he | he)
  · exact Or.inl (familyEdges_subset_adj W he.1)
  · exact C.outsideMacroRetainedEdges_subset_imaginaryGraph hSafeRoof A hW
      hsource hterminal hclosed he

/-- The strict common row rank excludes directed cycles in the exact global
relation. -/
theorem outsideMacroGlobalRelation_acyclic
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
    ¬ ContainsDirectedCycle
      (C.outsideMacroGlobalRelation (persistent := persistent)
        hSafeRoof A hW hsource hterminal hclosed) :=
  C.outsideMacroInside_union_retained_acyclic hSafeRoof A hW hWfinite hsub
    hnontrivial hsource hterminal hclosed

/-- The same rank excludes reverse rays in the exact global relation. -/
theorem outsideMacroGlobalRelation_no_reverse_ray
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
    ¬ ContainsReverseDirectedRay
      (C.outsideMacroGlobalRelation (persistent := persistent)
        hSafeRoof A hW hsource hterminal hclosed) :=
  C.outsideMacroInside_union_retained_no_reverse_ray hSafeRoof A hW hWfinite
    hsub hnontrivial hsource hterminal hclosed

end ClubStageGeometry
end Erdos599.Blueprint.LinkageBlueprint
