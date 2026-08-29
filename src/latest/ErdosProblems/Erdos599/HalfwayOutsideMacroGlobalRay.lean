/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayOutsideMacroGlobalRelation

/-!
# Row ownership and forward-ray exclusion for the global macro relation

Every literal inside edge belongs to the honest later row.  A classified
outside edge either remains a literal forward row edge or is the shortcut
between the initial and terminal of one outside row member.  Thus both
endpoints of every edge in the combined relation have a common owner in the
finite-character warp `W`.  Warp disjointness then forces every hypothetical
directed ray to stay in one finite member.
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

private theorem familyEdge_has_owner
    {W : Set Gamma.DPath} {x y : V}
    (hxy : (x, y) ∈ familyEdges W) :
    ∃ p : Gamma.DPath, p ∈ W ∧ x ∈ p.support ∧ y ∈ p.support := by
  simp only [familyEdges, Set.mem_iUnion] at hxy
  obtain ⟨p, hpW, hep⟩ := hxy
  have hend := p.edgeSet_subset_support_prod hep
  exact ⟨p, hpW, hend.1, hend.2⟩

/-- Every edge of the concrete global relation has a common honest-row
owner. -/
theorem outsideMacroGlobalRelation_edge_has_rowOwner
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
    {x y : V}
    (hxy : (x, y) ∈ C.outsideMacroGlobalRelation
      (persistent := persistent) hSafeRoof A hW hsource hterminal hclosed) :
    ∃ p : Gamma.DPath, p ∈ W ∧ x ∈ p.support ∧ y ∈ p.support := by
  rcases hxy with hxy | hxy
  · exact familyEdge_has_owner hxy.1
  · rcases hxy with hxy | hxy
    · obtain ⟨s, v, hsv, hxy⟩ := hxy
      let K := C.outsideMacroFiniteClassification hSafeRoof A hW hsource
        hterminal hclosed s v hsv
      change (x, y) ∈ K.retainedEdges at hxy
      clear_value K
      cases K with
      | imaginary himaginary =>
          simp only [LimitingFiniteContactClassification.retainedEdges,
            Set.mem_singleton_iff] at hxy
          rcases hxy with ⟨rfl, rfl⟩
          let p : outsideReference W X :=
            initialPath (outsideReference W X) ⟨s.1, s.property.1⟩
          have hpterminal : Gamma.terminal? p.1 = some y :=
            A.assigned_terminal_macroRoot hW hsub s hsv
          refine ⟨p.1, p.2.1, ?_, Gamma.terminal_mem_support hpterminal⟩
          simpa only [p, initialPath_initial] using p.1.initial_mem_support
      | initialCovered howner =>
          exact familyEdge_has_owner
            (A.assigned_forwardEdges_subset_familyEdges s hxy)
      | terminalCovered howner =>
          exact familyEdge_has_owner
            (A.assigned_forwardEdges_subset_familyEdges s hxy)
    · obtain ⟨s, hinfinite, hxy⟩ := hxy
      let K := C.outsideMacroInfiniteClassification (persistent := persistent)
        hSafeRoof A hW hsource hterminal hclosed s hinfinite
      change (x, y) ∈ K.retainedEdges at hxy
      clear_value K
      cases K with
      | popular hpopular =>
          simp [LimitingInfiniteContactClassification.retainedEdges] at hxy
      | initialCovered howner =>
          exact familyEdge_has_owner
            (A.assigned_forwardEdges_subset_familyEdges s hxy)

/-- Finite character of the honest row excludes a directed ray in the
combined relation. -/
theorem outsideMacroGlobalRelation_no_directedRay
    {W : Set Gamma.DPath} {X : Set V}
    {before innerRoof outerRoof persistent : Set V}
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (A : OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := W) (X := X))
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hsub : outsideReference C.selectedReference X ⊆
      outsideReference W X)
    (hsource : Gamma.initialSet W \ Gamma.initialSet C.selectedReference ⊆
      before ∩ innerRoof)
    (hterminal : Gamma.terminalFrontier W \
        Gamma.vertexSet C.selectedReference ⊆ before ∩ outerRoof)
    (hclosed : HammockClosedUpTo Gamma C.selectedReference X
      before innerRoof outerRoof kappa) :
    ¬ ContainsDirectedRay
      (C.outsideMacroGlobalRelation (persistent := persistent)
        hSafeRoof A hW hsource hterminal hclosed) := by
  rintro ⟨R, hR⟩
  obtain ⟨p, hpW, hp0, _hp1⟩ :=
    C.outsideMacroGlobalRelation_edge_has_rowOwner hSafeRoof A hW hsub
      hsource hterminal hclosed (hR ⟨0, rfl⟩)
  have hall : ∀ n : Nat, R.vertex n ∈ p.support := by
    intro n
    induction n with
    | zero => exact hp0
    | succ n ih =>
        obtain ⟨q, hqW, hqn, hqnext⟩ :=
          C.outsideMacroGlobalRelation_edge_has_rowOwner hSafeRoof A hW hsub
            hsource hterminal hclosed (hR ⟨n, rfl⟩)
        have hpq : p = q :=
          DWeb.IsWarp.eq_of_mem_support hW hpW hqW ih hqn
        exact hpq ▸ hqnext
  obtain ⟨pf, rfl⟩ := hWfinite hpW
  exact pf.support_finite.not_infinite
    (Set.infinite_of_injective_forall_mem R.injective hall)

/-- Hence the strong-ray obligation of the relation compiler is vacuous for
this finite-character construction. -/
theorem outsideMacroGlobalRelation_every_ray_strong
    {W : Set Gamma.DPath} {X : Set V}
    {before innerRoof outerRoof persistent : Set V}
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (A : OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := W) (X := X))
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hsub : outsideReference C.selectedReference X ⊆
      outsideReference W X)
    (hsource : Gamma.initialSet W \ Gamma.initialSet C.selectedReference ⊆
      before ∩ innerRoof)
    (hterminal : Gamma.terminalFrontier W \
        Gamma.vertexSet C.selectedReference ⊆ before ∩ outerRoof)
    (hclosed : HammockClosedUpTo Gamma C.selectedReference X
      before innerRoof outerRoof kappa) :
    ∀ r : Ray (imaginaryGraph Gamma C.ladder.limitWarp kappa),
      r.edgeSet ⊆ C.outsideMacroGlobalRelation (persistent := persistent)
        hSafeRoof A hW hsource hterminal hclosed →
        (strongEdgeIndices r).Infinite := by
  intro r hr
  exfalso
  apply C.outsideMacroGlobalRelation_no_directedRay hSafeRoof A hW hWfinite
    hsub hsource hterminal hclosed
  let R : DirectedRay V := {
    vertex := r.toFun
    injective := r.injective }
  refine ⟨R, ?_⟩
  rintro e ⟨n, rfl⟩
  exact hr ⟨n, rfl⟩

end ClubStageGeometry
end Erdos599.Blueprint.LinkageBlueprint
