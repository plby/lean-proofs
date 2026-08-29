/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularMarkedResidualColorOrder

/-!
# Isolating the residual colour of a marked route

If a reduced route against `P ∪ L` never traverses an old edge of `P`
backwards, and the two old carriers are disjoint, then the same list is a
reduced marked route against `L` alone.  This is the colour-sensitive step
needed before applying the one-hole augmentation theorem to the residual
warp.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularMarkedResidualColorIsolation

open DWeb Alternating
open SingularMarkedResidualColorOrder

universe u

variable {V : Type u}

private theorem familyEdges_union
    (G : DWeb V) (P L : Set G.DPath) :
    familyEdges (P ∪ L) = familyEdges P ∪ familyEdges L := by
  ext e
  simp only [familyEdges, Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨p, hp | hp, he⟩
    · exact Or.inl ⟨p, hp, he⟩
    · exact Or.inr ⟨p, hp, he⟩
  · rintro (⟨p, hp, he⟩ | ⟨p, hp, he⟩)
    · exact ⟨p, Or.inl hp, he⟩
    · exact ⟨p, Or.inr hp, he⟩

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

/-- A residual-colour transition between vertices outside the designated
carrier is also a transition for the union family. -/
private theorem markedStep_union_of_residual
    {G : DWeb V} {P L : Set G.DPath}
    {s t : OneHoleResidualState V}
    (hs : s.vertex ∉ G.vertexSet P)
    (ht : t.vertex ∉ G.vertexSet P)
    (hst : G.OneHoleMarkedStep L s t) :
    G.OneHoleMarkedStep (P ∪ L) s t := by
  cases hss : s with
  | ready x =>
    cases htt : t with
    | ready y =>
      simp only [OneHoleMarkedStep, hss, htt] at hst ⊢
      have hxNotP : x ∉ G.vertexSet P := by simpa [hss] using hs
      have hyNotP : y ∉ G.vertexSet P := by simpa [htt] using ht
      rcases hst with hforward | hbackward
      · apply Or.inl
        refine ⟨hforward.1, ?_, ?_⟩
        · rw [familyEdges_union]
          rintro (heP | heL)
          · exact hxNotP (left_mem_vertexSet_of_mem_familyEdges heP)
          · exact hforward.2.1 heL
        · simpa only [G.vertexSet_union, Set.mem_union, not_or] using
            ⟨hyNotP, hforward.2.2⟩
      · apply Or.inr
        rw [familyEdges_union]
        exact Or.inr hbackward
    | pending y =>
      simp only [OneHoleMarkedStep, hss, htt] at hst ⊢
      have hxNotP : x ∉ G.vertexSet P := by simpa [hss] using hs
      refine ⟨hst.1, ?_, ?_⟩
      · rw [familyEdges_union]
        rintro (heP | heL)
        · exact hxNotP (left_mem_vertexSet_of_mem_familyEdges heP)
        · exact hst.2.1 heL
      · rw [G.vertexSet_union]
        exact Or.inr hst.2.2
  | pending x =>
    cases htt : t with
    | ready y =>
      simp only [OneHoleMarkedStep, hss, htt] at hst ⊢
      rw [familyEdges_union]
      exact Or.inr hst
    | pending y =>
      simp only [OneHoleMarkedStep, hss, htt] at hst

private theorem route_step_is_residual
    {G : DWeb V} {P L : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hdisjoint : Disjoint (G.vertexSet P) (G.vertexSet L))
    (hl : IsReducedMarkedRoute G (P ∪ L) a b l)
    (ha : a ∉ G.vertexSet P)
    (hnoP : Disjoint
      (oneHoleRouteBackwardEdges G (P ∪ L) l) (familyEdges P))
    (i : Fin (l.length - 1)) :
    G.OneHoleMarkedStep L (oneHoleRouteSource l i)
      (oneHoleRouteTarget l i) := by
  have hstep := oneHoleRoute_step hl.1.2.1 i
  rcases (oneHoleMarkedStep_iff_chosenDirection G (P ∪ L)
      (oneHoleRouteSource l i) (oneHoleRouteTarget l i)).1 hstep with
    hforward | hbackward
  · cases hs : oneHoleRouteSource l i with
    | pending x =>
      cases ht : oneHoleRouteTarget l i <;>
        simp [OneHoleChosenForwardStep, hs, ht] at hforward
    | ready x =>
      cases ht : oneHoleRouteTarget l i with
      | ready y =>
        simp only [OneHoleChosenForwardStep, hs, ht] at hforward
        apply Or.inl
        exact ⟨hforward.1, fun heL ↦ hforward.2.1 (by
          rw [familyEdges_union]
          exact Or.inr heL), fun hyL ↦ hforward.2.2 (by
          rw [G.vertexSet_union]
          exact Or.inr hyL)⟩
      | pending y =>
        simp only [OneHoleChosenForwardStep, hs, ht] at hforward
        refine ⟨hforward.1, fun heL ↦ hforward.2.1 (by
          rw [familyEdges_union]
          exact Or.inr heL), ?_⟩
        have hyNotP : y ∉ G.vertexSet P := by
          have htargetP :=
            route_state_vertices_avoid_designated hdisjoint hl ha hnoP
              (i.1 + 1) (by omega)
          change (oneHoleRouteTarget l i).vertex ∉ G.vertexSet P at htargetP
          rw [ht] at htargetP
          exact htargetP
        simpa only [G.vertexSet_union, Set.mem_union, hyNotP, false_or] using
          hforward.2.2
  · have heBackward :
        ((oneHoleRouteTarget l i).vertex,
          (oneHoleRouteSource l i).vertex) ∈
            oneHoleRouteBackwardEdges G (P ∪ L) l :=
      ⟨i, hbackward, rfl⟩
    have heNotP :
        ((oneHoleRouteTarget l i).vertex,
          (oneHoleRouteSource l i).vertex) ∉ familyEdges P := by
      intro heP
      exact Set.disjoint_left.1 hnoP heBackward heP
    have heL :
        ((oneHoleRouteTarget l i).vertex,
          (oneHoleRouteSource l i).vertex) ∈ familyEdges L :=
      (backwardEdges_subset_designated_union_residual G P L l
        heBackward).resolve_left heNotP
    cases hs : oneHoleRouteSource l i with
    | ready x =>
      cases ht : oneHoleRouteTarget l i with
      | ready y =>
        apply Or.inr
        simpa only [hs, ht, OneHoleResidualState.vertex_ready] using heL
      | pending y =>
        simp only [OneHoleChosenBackwardStep, hs, ht] at hbackward
    | pending x =>
      cases ht : oneHoleRouteTarget l i with
      | ready y =>
        simpa only [OneHoleMarkedStep, hs, ht, OneHoleResidualState.vertex_ready,
          OneHoleResidualState.vertex_pending] using heL
      | pending y =>
        simp only [OneHoleChosenBackwardStep, hs, ht] at hbackward

private theorem route_mem_avoids_designated
    {G : DWeb V} {P L : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hdisjoint : Disjoint (G.vertexSet P) (G.vertexSet L))
    (hl : IsReducedMarkedRoute G (P ∪ L) a b l)
    (ha : a ∉ G.vertexSet P)
    (hnoP : Disjoint
      (oneHoleRouteBackwardEdges G (P ∪ L) l) (familyEdges P))
    {s : OneHoleResidualState V} (hs : s ∈ l) :
    s.vertex ∉ G.vertexSet P := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
  exact route_state_vertices_avoid_designated hdisjoint hl ha hnoP i hi

/-- A reduced union-colour route which has no designated backward contact
is already a reduced route in the residual colour alone. -/
theorem isReducedMarkedRoute_residual_of_no_designated_backward
    {G : DWeb V} {P L : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hdisjoint : Disjoint (G.vertexSet P) (G.vertexSet L))
    (hl : IsReducedMarkedRoute G (P ∪ L) a b l)
    (ha : a ∉ G.vertexSet P)
    (hnoP : Disjoint
      (oneHoleRouteBackwardEdges G (P ∪ L) l) (familyEdges P)) :
    IsReducedMarkedRoute G L a b l := by
  refine ⟨⟨hl.1.1, ?_, hl.1.2.2.1, hl.1.2.2.2⟩, hl.2.1, ?_⟩
  · rw [List.isChain_iff_getElem]
    intro i hi
    let j : Fin (l.length - 1) := ⟨i, by omega⟩
    exact route_step_is_residual hdisjoint hl ha hnoP j
  · intro pre mid post s t hdecomp hmid hst
    apply hl.2.2 pre mid post s t hdecomp hmid
    apply markedStep_union_of_residual
    · apply route_mem_avoids_designated hdisjoint hl ha hnoP
      rw [hdecomp]
      simp
    · apply route_mem_avoids_designated hdisjoint hl ha hnoP
      rw [hdecomp]
      simp
    · exact hst

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

/-- The finite-component decomposition preserves a forbidden-carrier
condition when both the certified edge relation and the retained isolated
vertices avoid that carrier. -/
theorem exists_onePointAugmentation_of_toggleCertificate_avoiding_exact
    (G : DWeb V) {J : Set G.DPath} (hJ : G.IsCleanFiniteWarp J)
    {a b : V} (ha : a ∈ G.source \ G.initialSet J)
    (hb : b ∈ G.target \ G.terminalFrontier J) (hab : a ≠ b)
    (T : OneHoleToggleCertificate G J a b) (S : Set V)
    (hTavoid : T.edges ⊆ Sᶜ ×ˢ Sᶜ)
    (hJavoid : Disjoint S (G.vertexSet J)) :
    ∃ Jplus, G.IsOnePointAugmentation J Jplus ∧
      Disjoint S (G.vertexSet Jplus) ∧
      G.initialSet Jplus = insert a (G.initialSet J) ∧
      G.terminalFrontier Jplus = insert b (G.terminalFrontier J) := by
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
  have hinitial : G.initialSet C.pathPart = insert a (G.initialSet J) := by
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
  have hterminal :
      G.terminalFrontier C.pathPart = insert b (G.terminalFrontier J) := by
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
    ?_, hinitial, hterminal⟩
  · apply cyclowarp_vertexSet_avoids_of_edges_avoid C
    · rw [hCEdges]
      exact hTavoid
    · rw [hCIso]
      exact hJavoid.mono_right (isolatedVertices_subset_vertexSet J)

/-- Endpoint-erased convenience form of the avoiding decomposition. -/
theorem exists_onePointAugmentation_of_toggleCertificate_avoiding
    (G : DWeb V) {J : Set G.DPath} (hJ : G.IsCleanFiniteWarp J)
    {a b : V} (ha : a ∈ G.source \ G.initialSet J)
    (hb : b ∈ G.target \ G.terminalFrontier J) (hab : a ≠ b)
    (T : OneHoleToggleCertificate G J a b) (S : Set V)
    (hTavoid : T.edges ⊆ Sᶜ ×ˢ Sᶜ)
    (hJavoid : Disjoint S (G.vertexSet J)) :
    ∃ Jplus, G.IsOnePointAugmentation J Jplus ∧
      Disjoint S (G.vertexSet Jplus) := by
  obtain ⟨Jplus, hplus, havoid, _hinitial, _hterminal⟩ :=
    exists_onePointAugmentation_of_toggleCertificate_avoiding_exact
      G hJ ha hb hab T S hTavoid hJavoid
  exact ⟨Jplus, hplus, havoid⟩

private theorem toggledEdges_avoid_designated
    {G : DWeb V} {P L : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hdisjoint : Disjoint (G.vertexSet P) (G.vertexSet L))
    (hl : IsReducedMarkedRoute G (P ∪ L) a b l)
    (ha : a ∉ G.vertexSet P)
    (hnoP : Disjoint
      (oneHoleRouteBackwardEdges G (P ∪ L) l) (familyEdges P)) :
    oneHoleRouteToggledEdges G L l ⊆
      (G.vertexSet P)ᶜ ×ˢ (G.vertexSet P)ᶜ := by
  rintro e (heOld | heForward)
  · have hleft := left_mem_vertexSet_of_mem_familyEdges heOld.1
    have hright := right_mem_vertexSet_of_mem_familyEdges heOld.1
    exact ⟨fun hxP ↦ Set.disjoint_left.1 hdisjoint hxP hleft,
      fun hxP ↦ Set.disjoint_left.1 hdisjoint hxP hright⟩
  · rcases heForward with ⟨i, hi, rfl⟩
    exact ⟨
      route_state_vertices_avoid_designated hdisjoint hl ha hnoP
        i.1 (by omega),
      route_state_vertices_avoid_designated hdisjoint hl ha hnoP
        (i.1 + 1) (by omega)⟩

/-- In the no-designated-backward-contact branch, the one-hole operation is
a genuine augmentation of the residual colour, and its whole new carrier
still avoids the designated colour. -/
theorem exists_residual_onePointAugmentation_avoiding_designated
    {G : DWeb V} {P L : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hP_L : Disjoint (G.vertexSet P) (G.vertexSet L))
    (hL : G.IsCleanFiniteWarp L)
    (hl : IsReducedMarkedRoute G (P ∪ L) a b l)
    (haP : a ∉ G.vertexSet P)
    (hnoP : Disjoint
      (oneHoleRouteBackwardEdges G (P ∪ L) l) (familyEdges P))
    (ha : a ∈ G.source \ G.initialSet L)
    (hb : b ∈ G.target \ G.terminalFrontier L)
    (hab : a ≠ b) :
    ∃ Lplus, G.IsOnePointAugmentation L Lplus ∧
      Disjoint (G.vertexSet P) (G.vertexSet Lplus) := by
  have hlL : IsReducedMarkedRoute G L a b l :=
    isReducedMarkedRoute_residual_of_no_designated_backward
      hP_L hl haP hnoP
  let T : OneHoleToggleCertificate G L a b :=
    oneHoleToggleCertificateOfReducedRoute hL ha hlL
      (oneHoleRouteBalance G L a b l hL ha hlL)
  apply exists_onePointAugmentation_of_toggleCertificate_avoiding
    G hL ha hb hab T (G.vertexSet P)
  · change oneHoleRouteToggledEdges G L l ⊆
      (G.vertexSet P)ᶜ ×ˢ (G.vertexSet P)ᶜ
    exact toggledEdges_avoid_designated hP_L hl haP hnoP
  · exact hP_L

/-- Exact-endpoint form of the confined residual augmentation. -/
theorem exists_residual_onePointAugmentation_avoiding_designated_exact
    {G : DWeb V} {P L : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hP_L : Disjoint (G.vertexSet P) (G.vertexSet L))
    (hL : G.IsCleanFiniteWarp L)
    (hl : IsReducedMarkedRoute G (P ∪ L) a b l)
    (haP : a ∉ G.vertexSet P)
    (hnoP : Disjoint
      (oneHoleRouteBackwardEdges G (P ∪ L) l) (familyEdges P))
    (ha : a ∈ G.source \ G.initialSet L)
    (hb : b ∈ G.target \ G.terminalFrontier L)
    (hab : a ≠ b) :
    ∃ Lplus, G.IsOnePointAugmentation L Lplus ∧
      Disjoint (G.vertexSet P) (G.vertexSet Lplus) ∧
      G.initialSet Lplus = insert a (G.initialSet L) ∧
      G.terminalFrontier Lplus = insert b (G.terminalFrontier L) := by
  have hlL : IsReducedMarkedRoute G L a b l :=
    isReducedMarkedRoute_residual_of_no_designated_backward
      hP_L hl haP hnoP
  let T : OneHoleToggleCertificate G L a b :=
    oneHoleToggleCertificateOfReducedRoute hL ha hlL
      (oneHoleRouteBalance G L a b l hL ha hlL)
  apply exists_onePointAugmentation_of_toggleCertificate_avoiding_exact
    G hL ha hb hab T (G.vertexSet P)
  · change oneHoleRouteToggledEdges G L l ⊆
      (G.vertexSet P)ᶜ ×ˢ (G.vertexSet P)ᶜ
    exact toggledEdges_avoid_designated hP_L hl haP hnoP
  · exact hP_L

/-- The common-gap one-point augmentation can also be chosen to avoid an
arbitrary forbidden carrier, provided both the old warp and the common
endpoint avoid it. -/
theorem exists_avoiding_onePointAugmentation_of_common_gap_exact
    (G : DWeb V) {J : Set G.DPath} {S : Set V}
    (hJ : G.IsCleanFiniteWarp J)
    (hJavoid : Disjoint S (G.vertexSet J))
    {a : V} (haS : a ∉ S)
    (ha : a ∈ G.source \ G.initialSet J)
    (hb : a ∈ G.target \ G.terminalFrontier J) :
    ∃ Jplus, G.IsOnePointAugmentation J Jplus ∧
      Disjoint S (G.vertexSet Jplus) ∧
      G.terminalFrontier Jplus = insert a (G.terminalFrontier J) := by
  let q := DirectedPath.FinitePath.trivial G.graph a
  let Jplus : Set G.DPath := insert (.inl q : G.DPath) J
  refine ⟨Jplus, ?_, ?_, ?_⟩
  · refine ⟨a, ha, a, hb, ?_, ?_, ?_, ?_⟩
    · apply DWeb.IsWarp.insert_finite_of_disjoint G hJ.isWarp q
      rw [Set.disjoint_left]
      intro x hx hxJ
      have hxa : x = a := by simpa [q] using hx
      subst x
      exact Set.disjoint_left.1 hJ.source_gap_disjoint_vertexSet ha hxJ
    · exact G.hasFiniteCharacter_insert_finite hJ.hasFiniteCharacter q
    · exact G.initialSet_insert_finite J q
    · exact G.terminalFrontier_insert_finite J q
  · rw [Set.disjoint_left]
    intro x hxS hxPlus
    rcases hxPlus with ⟨p, hp, hxp⟩
    rcases hp with hp | hp
    · subst p
      have hxa : x = a := by
        change x ∈ (G.trivialPath a).support at hxp
        simpa only [G.support_trivialPath, Set.mem_singleton_iff] using hxp
      exact haS (hxa ▸ hxS)
    · exact Set.disjoint_left.1 hJavoid hxS ⟨p, hp, hxp⟩
  · exact G.terminalFrontier_insert_finite J q

/-- Endpoint-erased convenience form of the avoiding common-gap switch. -/
theorem exists_avoiding_onePointAugmentation_of_common_gap
    (G : DWeb V) {J : Set G.DPath} {S : Set V}
    (hJ : G.IsCleanFiniteWarp J)
    (hJavoid : Disjoint S (G.vertexSet J))
    {a : V} (haS : a ∉ S)
    (ha : a ∈ G.source \ G.initialSet J)
    (hb : a ∈ G.target \ G.terminalFrontier J) :
    ∃ Jplus, G.IsOnePointAugmentation J Jplus ∧
      Disjoint S (G.vertexSet Jplus) := by
  obtain ⟨Jplus, hplus, havoid, _hterminal⟩ :=
    exists_avoiding_onePointAugmentation_of_common_gap_exact
      G hJ hJavoid haS ha hb
  exact ⟨Jplus, hplus, havoid⟩

/-- Version including the common-gap case; no endpoint inequality is
needed. -/
theorem exists_residual_onePointAugmentation_avoiding_designated_or_common
    {G : DWeb V} {P L : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hP_L : Disjoint (G.vertexSet P) (G.vertexSet L))
    (hL : G.IsCleanFiniteWarp L)
    (hl : IsReducedMarkedRoute G (P ∪ L) a b l)
    (haP : a ∉ G.vertexSet P)
    (hnoP : Disjoint
      (oneHoleRouteBackwardEdges G (P ∪ L) l) (familyEdges P))
    (ha : a ∈ G.source \ G.initialSet L)
    (hb : b ∈ G.target \ G.terminalFrontier L) :
    ∃ Lplus, G.IsOnePointAugmentation L Lplus ∧
      Disjoint (G.vertexSet P) (G.vertexSet Lplus) := by
  by_cases hab : a = b
  · subst b
    exact exists_avoiding_onePointAugmentation_of_common_gap
      G hL hP_L haP ha hb
  · exact exists_residual_onePointAugmentation_avoiding_designated
      hP_L hL hl haP hnoP ha hb hab

/-- Uniform endpoint-retaining form: in both the distinct and common-gap
branches the specified endpoint `b` lies on the new terminal frontier. -/
theorem exists_residual_onePointAugmentation_avoiding_with_terminal
    {G : DWeb V} {P L : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hP_L : Disjoint (G.vertexSet P) (G.vertexSet L))
    (hL : G.IsCleanFiniteWarp L)
    (hl : IsReducedMarkedRoute G (P ∪ L) a b l)
    (haP : a ∉ G.vertexSet P)
    (hnoP : Disjoint
      (oneHoleRouteBackwardEdges G (P ∪ L) l) (familyEdges P))
    (ha : a ∈ G.source \ G.initialSet L)
    (hb : b ∈ G.target \ G.terminalFrontier L) :
    ∃ Lplus, G.IsOnePointAugmentation L Lplus ∧
      Disjoint (G.vertexSet P) (G.vertexSet Lplus) ∧
      b ∈ G.terminalFrontier Lplus := by
  by_cases hab : a = b
  · subst b
    obtain ⟨Lplus, hplus, havoid, hterminal⟩ :=
      exists_avoiding_onePointAugmentation_of_common_gap_exact
        G hL hP_L haP ha hb
    refine ⟨Lplus, hplus, havoid, ?_⟩
    rw [hterminal]
    exact Or.inl rfl
  · obtain ⟨Lplus, hplus, havoid, _hinitial, hterminal⟩ :=
      exists_residual_onePointAugmentation_avoiding_designated_exact
        hP_L hL hl haP hnoP ha hb hab
    refine ⟨Lplus, hplus, havoid, ?_⟩
    rw [hterminal]
    exact Or.inl rfl

#print axioms isReducedMarkedRoute_residual_of_no_designated_backward
#print axioms exists_onePointAugmentation_of_toggleCertificate_avoiding
#print axioms exists_residual_onePointAugmentation_avoiding_designated
#print axioms exists_residual_onePointAugmentation_avoiding_designated_exact
#print axioms exists_avoiding_onePointAugmentation_of_common_gap
#print axioms exists_residual_onePointAugmentation_avoiding_designated_or_common
#print axioms exists_residual_onePointAugmentation_avoiding_with_terminal

end SingularMarkedResidualColorIsolation
end CardinalInduction
end Erdos599
