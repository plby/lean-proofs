/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularMarkedResidualColorIsolation

/-!
# Exact relation retained by finite toggle realization

The standard one-hole realization exposes the resulting augmentation but
forgets the relation from which its paths were decomposed.  The cyclowarp
construction in fact gives exact equality of edge relations and isolated
vertices.  This file retains those equalities so later fresh-component
arguments can recover route provenance.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularToggleExactRelation

open DWeb Alternating

universe u

variable {V : Type u}

private theorem left_mem_vertexSet_of_mem_familyEdges
    {G : DWeb V} {W : Set G.DPath} {x y : V}
    (hxy : (x, y) ∈ familyEdges W) : x ∈ G.vertexSet W := by
  simp only [familyEdges, Set.mem_iUnion] at hxy
  obtain ⟨p, hpW, hpEdge⟩ := hxy
  exact ⟨p, hpW, (p.edgeSet_subset_support_prod hpEdge).1⟩

private theorem right_mem_vertexSet_of_mem_familyEdges
    {G : DWeb V} {W : Set G.DPath} {x y : V}
    (hxy : (x, y) ∈ familyEdges W) : y ∈ G.vertexSet W := by
  simp only [familyEdges, Set.mem_iUnion] at hxy
  obtain ⟨p, hpW, hpEdge⟩ := hxy
  exact ⟨p, hpW, (p.edgeSet_subset_support_prod hpEdge).2⟩

private theorem walk_eq_nil_of_isPath_same_ends
    {D : Digraph V} {x : V} (w : DirectedPath.Walk D x x)
    (hw : w.IsPath) : w = .nil := by
  cases w with
  | nil => rfl
  | @cons _ y _ h q =>
      exact False.elim ((List.nodup_cons.mp hw).1 q.end_mem_support)

private theorem finitePath_eq_trivial_of_start_eq_finish
    {D : Digraph V} (p : DirectedPath.FinitePath D)
    (h : p.start = p.finish) :
    p = DirectedPath.FinitePath.trivial D p.start := by
  rcases p with ⟨start, finish, walk, isPath⟩
  dsimp at h ⊢
  subst finish
  have hw : walk = .nil := walk_eq_nil_of_isPath_same_ends walk isPath
  subst walk
  rfl

private theorem cyclowarp_vertexSet_avoids_of_edges_avoid
    {G : DWeb V} {S : Set V} (C : Cyclowarp G)
    (hEdges : C.edges ⊆ Sᶜ ×ˢ Sᶜ)
    (hIso : Disjoint S C.isolated) :
    Disjoint S (G.vertexSet C.pathPart) := by
  rw [Set.disjoint_left]
  intro x hxS hxC
  rcases hxC with ⟨p, hpC, hxp⟩
  rcases p with p | r
  · by_cases hxstart : x = p.start
    · by_cases hxfinish : x = p.finish
      · have hends : p.start = p.finish := hxstart.symm.trans hxfinish
        have hpEq : (Sum.inl p : G.DPath) = G.trivialPath p.start := by
          rw [finitePath_eq_trivial_of_start_eq_finish p hends]
          rfl
        have hiso : p.start ∈ C.isolated := by
          change G.trivialPath p.start ∈ C.paths
          rw [← hpEq]
          exact hpC
        exact Set.disjoint_left.1 hIso (hxstart ▸ hxS) hiso
      · obtain ⟨y, hxy⟩ :=
          Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
            p hxp hxfinish
        have hfamily : (x, y) ∈ familyEdges C.pathPart := by
          simp only [familyEdges, Set.mem_iUnion]
          exact ⟨Sum.inl p, hpC, hxy⟩
        have havoid := hEdges (Or.inl hfamily)
        exact havoid.1 hxS
    · obtain ⟨y, hyx⟩ :=
        Alternating.FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
          p hxp hxstart
      have hfamily : (y, x) ∈ familyEdges C.pathPart := by
        simp only [familyEdges, Set.mem_iUnion]
        exact ⟨Sum.inl p, hpC, hyx⟩
      have havoid := hEdges (Or.inl hfamily)
      exact havoid.2 hxS
  · rcases hxp with ⟨n, rfl⟩
    have hfamily : (r n, r (n + 1)) ∈ familyEdges C.pathPart := by
      simp only [familyEdges, Set.mem_iUnion]
      exact ⟨Sum.inr r, hpC, ⟨n, rfl⟩⟩
    have havoid := hEdges (Or.inl hfamily)
    exact havoid.1 hxS

private theorem not_hasOutgoing_familyEdges_of_outside_vertexSet
    {G : DWeb V} {J : Set G.DPath} {x : V}
    (hx : x ∉ G.vertexSet J) : ¬ HasOutgoing (familyEdges J) x := by
  rintro ⟨y, hxy⟩
  exact hx (left_mem_vertexSet_of_mem_familyEdges hxy)

private theorem not_hasIncoming_familyEdges_of_outside_vertexSet
    {G : DWeb V} {J : Set G.DPath} {x : V}
    (hx : x ∉ G.vertexSet J) : ¬ HasIncoming (familyEdges J) x := by
  rintro ⟨y, hyx⟩
  exact hx (right_mem_vertexSet_of_mem_familyEdges hyx)

private theorem edgeBalance_familyEdges_eq_zero_of_outside_vertexSet
    {G : DWeb V} {J : Set G.DPath} {x : V}
    (hx : x ∉ G.vertexSet J) : edgeBalance (familyEdges J) x = 0 := by
  have hout := not_hasOutgoing_familyEdges_of_outside_vertexSet hx
  have hin := not_hasIncoming_familyEdges_of_outside_vertexSet hx
  simp [edgeBalance, propInt, hout, hin]

/-- Exact-relation strengthening of the avoiding toggle realization. -/
theorem exists_onePointAugmentation_of_toggleCertificate_avoiding_exactRelation
    (G : DWeb V) {J : Set G.DPath} (hJ : G.IsCleanFiniteWarp J)
    {a b : V} (ha : a ∈ G.source \ G.initialSet J)
    (hb : b ∈ G.target \ G.terminalFrontier J) (hab : a ≠ b)
    (T : OneHoleToggleCertificate G J a b) (S : Set V)
    (hTavoid : T.edges ⊆ Sᶜ ×ˢ Sᶜ)
    (hJavoid : Disjoint S (G.vertexSet J)) :
    ∃ Jplus, G.IsOnePointAugmentation J Jplus ∧
      Disjoint S (G.vertexSet Jplus) ∧
      G.initialSet Jplus = insert a (G.initialSet J) ∧
      G.terminalFrontier Jplus = insert b (G.terminalFrontier J) ∧
      ∃ C : Cyclowarp G, Jplus = C.pathPart ∧
        C.edges = T.edges ∧ C.isolated = isolatedVertices J := by
  classical
  have haFresh : a ∉ G.vertexSet J :=
    fun haJ ↦ Set.disjoint_left.1 hJ.source_gap_disjoint_vertexSet ha haJ
  have hbFresh : b ∉ G.vertexSet J :=
    fun hbJ ↦ Set.disjoint_left.1 hJ.target_gap_disjoint_vertexSet hb hbJ
  have haBal : edgeBalance (familyEdges J) a = 0 :=
    edgeBalance_familyEdges_eq_zero_of_outside_vertexSet haFresh
  have hbBal : edgeBalance (familyEdges J) b = 0 :=
    edgeBalance_familyEdges_eq_zero_of_outside_vertexSet hbFresh
  have haNotIso : a ∉ isolatedVertices J :=
    fun haIso ↦ haFresh (isolatedVertices_subset_vertexSet J haIso)
  have hbNotIso : b ∉ isolatedVertices J :=
    fun hbIso ↦ hbFresh (isolatedVertices_subset_vertexSet J hbIso)
  obtain ⟨C, hCEdges, hCIso, hCfin⟩ :=
    RelationComponents.exists_cyclowarp_of_finite_componentSupports
      G T.edges (isolatedVertices J) T.edges_in_graph
      T.outgoing_unique T.incoming_unique T.finite_components
      T.old_isolated_not_incident
  have hinitial : G.initialSet C.pathPart =
      insert a (G.initialSet J) := by
    ext x
    rw [C.mem_initialSet_pathPart_iff_isolated_or_edgeBalance_eq_one hCfin]
    simp only [Set.mem_insert_iff]
    rw [mem_initialSet_iff_isolated_or_edgeBalance_eq_one
      hJ.isWarp hJ.hasFiniteCharacter, hCIso, hCEdges, T.balance_delta]
    by_cases hxa : x = a
    · subst x
      simp [propInt, haNotIso, haBal, hab]
    · by_cases hxb : x = b
      · subst x
        simp [propInt, hbNotIso, hbBal, hab.symm]
      · simp [propInt, hxa, hxb]
  have hterminal : G.terminalFrontier C.pathPart =
      insert b (G.terminalFrontier J) := by
    ext x
    rw [C.mem_terminalFrontier_pathPart_iff_isolated_or_edgeBalance_eq_neg_one
      hCfin]
    simp only [Set.mem_insert_iff]
    rw [mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one
      hJ.isWarp hJ.hasFiniteCharacter, hCIso, hCEdges, T.balance_delta]
    by_cases hxa : x = a
    · subst x
      simp [propInt, haNotIso, haBal, hab]
    · by_cases hxb : x = b
      · subst x
        simp [propInt, hbNotIso, hbBal, hab.symm]
      · simp [propInt, hxa, hxb]
  refine ⟨C.pathPart,
    ⟨a, ha, b, hb, C.pathPart_isWarp, hCfin, hinitial, hterminal⟩,
    ?_, hinitial, hterminal, C, rfl, hCEdges, hCIso⟩
  apply cyclowarp_vertexSet_avoids_of_edges_avoid C
  · rw [hCEdges]
    exact hTavoid
  · rw [hCIso]
    exact hJavoid.mono_right (isolatedVertices_subset_vertexSet J)

/-- A concrete reduced marked route can be realized without losing its
exact toggled edge relation. -/
theorem exists_onePointAugmentation_of_reducedRoute_avoiding_exactRelation
    (G : DWeb V) {J : Set G.DPath} (hJ : G.IsCleanFiniteWarp J)
    {a b : V} {l : List (OneHoleResidualState V)}
    (hl : IsReducedMarkedRoute G J a b l)
    (ha : a ∈ G.source \ G.initialSet J)
    (hb : b ∈ G.target \ G.terminalFrontier J) (hab : a ≠ b)
    (S : Set V)
    (hTavoid : oneHoleRouteToggledEdges G J l ⊆ Sᶜ ×ˢ Sᶜ)
    (hJavoid : Disjoint S (G.vertexSet J)) :
    ∃ Jplus, G.IsOnePointAugmentation J Jplus ∧
      Disjoint S (G.vertexSet Jplus) ∧
      G.initialSet Jplus = insert a (G.initialSet J) ∧
      G.terminalFrontier Jplus = insert b (G.terminalFrontier J) ∧
      ∃ C : Cyclowarp G, Jplus = C.pathPart ∧
        C.edges = oneHoleRouteToggledEdges G J l ∧
        C.isolated = isolatedVertices J := by
  let T : OneHoleToggleCertificate G J a b :=
    oneHoleToggleCertificateOfReducedRoute hJ ha hl
      (oneHoleRouteBalance G J a b l hJ ha hl)
  exact exists_onePointAugmentation_of_toggleCertificate_avoiding_exactRelation
    G hJ ha hb hab T S hTavoid hJavoid

#print axioms exists_onePointAugmentation_of_toggleCertificate_avoiding_exactRelation
#print axioms exists_onePointAugmentation_of_reducedRoute_avoiding_exactRelation

end SingularToggleExactRelation
end CardinalInduction
end Erdos599
