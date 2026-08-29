/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularMarkedResidualColorIsolation
import ErdosProblems.Erdos599.SingularMaximalWaveTargetAbsorption

/-!
# A designated contact forced by maximal residual waves

The marked one-hole route against the disjoint union of a designated
linkage and a residual wave remembers more than the resulting uncoloured
augmentation.  This file develops the branch in which the route does not
cancel a designated edge.  In that branch the route is wholly supported in
the deleted residual and hence gives a genuine residual augmentation.  For
an essential part of a maximal residual wave this is impossible: the new
terminal is a target vertex outside the old roof.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularMarkedResidualDesignatedContact

open DWeb Alternating
open SingularMarkedResidualColorOrder SingularMarkedResidualExchange
  SingularResidualWaveExchange
open SingularMarkedResidualColorIsolation
  SingularMaximalWaveTargetAbsorption

universe u

variable {V : Type u}

private theorem walk_edgeSet_lift {D E : Digraph V}
    (hDE : ∀ {x y}, D.Adj x y → E.Adj x y) {a b : V}
    (p : DirectedPath.Walk D a b) :
    (p.lift hDE).edgeSet = p.edgeSet := by
  induction p with
  | nil => rfl
  | cons h p ih =>
      simp [DirectedPath.Walk.lift, DirectedPath.Walk.edgeSet_cons, ih]

private theorem edgeSet_liftDeletePath
    (G : DWeb V) (X : Set V) (p : (G.delete X).DPath) :
    (G.liftDeletePath X p).edgeSet = p.edgeSet := by
  rcases p with p | r
  · exact walk_edgeSet_lift _ p.walk
  · rfl

/-- Lifting a deletion family changes neither its directed edge relation
nor its support vertices. -/
theorem familyEdges_liftDeleteFamily
    (G : DWeb V) (X : Set V) (W : Set (G.delete X).DPath) :
    familyEdges (G.liftDeleteFamily X W) = familyEdges W := by
  ext e
  simp only [familyEdges, Set.mem_iUnion]
  constructor
  · rintro ⟨p, ⟨q, hqW, rfl⟩, hep⟩
    exact ⟨q, hqW, by simpa only [edgeSet_liftDeletePath] using hep⟩
  · rintro ⟨q, hqW, heq⟩
    exact ⟨G.liftDeletePath X q, ⟨q, hqW, rfl⟩,
      by simpa only [edgeSet_liftDeletePath] using heq⟩

private theorem familyEdges_union (G : DWeb V) (P L : Set G.DPath) :
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

/-- Every subfamily of a clean finite warp is again clean.  Cleanliness is
inherited because two members of the ambient warp which meet are equal. -/
theorem DWeb.IsCleanFiniteWarp.subfamily
    {G : DWeb V} {J Y : Set G.DPath}
    (hJ : G.IsCleanFiniteWarp J) (hY : Y ⊆ J) :
    G.IsCleanFiniteWarp Y := by
  have hYwarp : G.IsWarp Y := fun p hp q hq hpq ↦
    hJ.1 (hY hp) (hY hq) hpq
  have hYfin : G.HasFiniteCharacter Y := by
    intro p hp
    exact hJ.2.1 (hY hp)
  refine ⟨hYwarp, hYfin, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨⟨p, hpY, hxp⟩, hxSource⟩
      have hxInitialJ : x ∈ G.initialSet J := by
        rw [← hJ.2.2.1]
        exact ⟨⟨p, hY hpY, hxp⟩, hxSource⟩
      obtain ⟨q, hqJ, hqx⟩ := hxInitialJ
      have hpq : p = q := by
        apply DWeb.IsWarp.eq_of_mem_support hJ.isWarp (hY hpY) hqJ
        · exact hxp
        · exact hqx ▸ q.initial_mem_support
      subst q
      exact ⟨p, hpY, hqx⟩
    · rintro x ⟨p, hpY, rfl⟩
      exact ⟨⟨p, hpY, p.initial_mem_support⟩,
        DWeb.IsCleanFiniteWarp.initialSet_subset_source G hJ
          ⟨p, hY hpY, rfl⟩⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨⟨p, hpY, hxp⟩, hxTarget⟩
      have hxTerminalJ : x ∈ G.terminalFrontier J := by
        rw [← hJ.2.2.2]
        exact ⟨⟨p, hY hpY, hxp⟩, hxTarget⟩
      obtain ⟨q, hqJ, hqx⟩ := hxTerminalJ
      have hpq : p = q := by
        apply DWeb.IsWarp.eq_of_mem_support hJ.isWarp (hY hpY) hqJ
        · exact hxp
        · exact G.terminal_mem_support hqx
      subst q
      exact ⟨p, hpY, hqx⟩
    · rintro x ⟨p, hpY, hpx⟩
      exact ⟨⟨p, hpY, G.terminal_mem_support hpx⟩,
        DWeb.IsCleanFiniteWarp.terminalFrontier_subset_target G hJ
          ⟨p, hY hpY, hpx⟩⟩

/-- On states outside the left carrier, the marked residual relation for a
union agrees with the relation for the right colour alone. -/
theorem oneHoleMarkedStep_union_iff_right_of_avoids_left
    (G : DWeb V) (P L : Set G.DPath)
    (s t : OneHoleResidualState V)
    (hs : s.vertex ∉ G.vertexSet P)
    (ht : t.vertex ∉ G.vertexSet P) :
    G.OneHoleMarkedStep (P ∪ L) s t ↔ G.OneHoleMarkedStep L s t := by
  cases s with
  | ready x =>
      cases t with
      | ready y =>
          have hxyP : (x, y) ∉ familyEdges P := fun h ↦
            hs (familyEdges_subset_vertexSet_prod P h).1
          have hyxP : (y, x) ∉ familyEdges P := fun h ↦
            ht (familyEdges_subset_vertexSet_prod P h).1
          simp only [DWeb.OneHoleMarkedStep]
          rw [familyEdges_union]
          simp only [DWeb.OneHoleMarkedStep, G.vertexSet_union,
            Set.mem_union, OneHoleResidualState.vertex_ready] at hs ht ⊢
          tauto
      | pending y =>
          have hxyP : (x, y) ∉ familyEdges P := fun h ↦
            hs (familyEdges_subset_vertexSet_prod P h).1
          simp only [DWeb.OneHoleMarkedStep]
          rw [familyEdges_union]
          simp only [DWeb.OneHoleMarkedStep, G.vertexSet_union,
            Set.mem_union, OneHoleResidualState.vertex_ready,
            OneHoleResidualState.vertex_pending] at hs ht ⊢
          tauto
  | pending x =>
      cases t with
      | ready y =>
          have hyxP : (y, x) ∉ familyEdges P := fun h ↦
            hs (familyEdges_subset_vertexSet_prod P h).2
          simp only [DWeb.OneHoleMarkedStep]
          rw [familyEdges_union]
          simp only [DWeb.OneHoleMarkedStep,
            OneHoleResidualState.vertex_ready,
            OneHoleResidualState.vertex_pending] at hs ht ⊢
          simpa only [Set.mem_union, hyxP, false_or]
      | pending y => simp [DWeb.OneHoleMarkedStep]

/-- If a reduced route never uses a backward edge of the left colour, the
same list is a reduced route against the right colour alone. -/
theorem reducedMarkedRoute_right_of_no_left_backward
    {G : DWeb V} {P L : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hdisjoint : Disjoint (G.vertexSet P) (G.vertexSet L))
    (hl : IsReducedMarkedRoute G (P ∪ L) a b l)
    (ha : a ∉ G.vertexSet P)
    (hnoP : Disjoint
      (oneHoleRouteBackwardEdges G (P ∪ L) l) (familyEdges P)) :
    IsReducedMarkedRoute G L a b l := by
  have hindex : ∀ n (hn : n < l.length),
      l[n].vertex ∉ G.vertexSet P :=
    route_state_vertices_avoid_designated hdisjoint hl ha hnoP
  have hmem : ∀ s ∈ l, s.vertex ∉ G.vertexSet P := by
    intro s hs
    obtain ⟨n, hn, hns⟩ := List.getElem_of_mem hs
    subst s
    exact hindex n hn
  refine ⟨⟨hl.1.1, ?_, hl.1.2.2.1, hl.1.2.2.2⟩, hl.2.1, ?_⟩
  · exact (hl.1.2.1.imp_of_mem_imp fun s t hs ht hst ↦
      (oneHoleMarkedStep_union_iff_right_of_avoids_left
        G P L s t (hmem s hs) (hmem t ht)).1 hst)
  · intro pre mid post s t hdecomp hmid hst
    apply hl.2.2 pre mid post s t hdecomp hmid
    have hs : s.vertex ∉ G.vertexSet P := by
      apply hmem s
      rw [hdecomp]
      simp
    have ht : t.vertex ∉ G.vertexSet P := by
      apply hmem t
      rw [hdecomp]
      simp
    exact (oneHoleMarkedStep_union_iff_right_of_avoids_left
      G P L s t hs ht).2 hst

/-- If the carrier deletion of `P` is hindered, the marked route against the
finite essential part of a maximal residual hindrance must cancel at least
one old edge of `P`.  Otherwise colour isolation gives an avoiding residual
augmentation, whose new target terminal contradicts maximal-wave target
absorption. -/
theorem exists_maximalResidualRoute_with_designatedBackwardContact
    {G : DWeb V} (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    {A : Set V} (hA : A ⊆ G.source)
    {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (hresidual : (G.delete (G.vertexSet P)).IsHindered) :
    ∃ M : (G.delete (G.vertexSet P)).Wave,
      IsMax M ∧ (G.delete (G.vertexSet P)).IsHindrance M.1 ∧
      let U := (G.delete (G.vertexSet P)).essentialWarpPart M.1
      (G.delete (G.vertexSet P)).IsHindrance U ∧
      (G.delete (G.vertexSet P)).HasFiniteCharacter U ∧
      ∃ a b : V, ∃ l : List (OneHoleResidualState V),
        a ∈ (G.delete (G.vertexSet P)).source \
          (G.delete (G.vertexSet P)).initialSet U ∧
        b ∈ G.target \
          (G.delete (G.vertexSet P)).terminalFrontier U ∧
        IsReducedMarkedRoute
          (G.retarget
            (G.target ∪
              (G.delete (G.vertexSet P)).terminalFrontier U))
          (P ∪ G.liftDeleteFamily (G.vertexSet P) U) a b l ∧
        ¬ Disjoint
          (oneHoleRouteBackwardEdges
            (G.retarget
              (G.target ∪
                (G.delete (G.vertexSet P)).terminalFrontier U))
            (P ∪ G.liftDeleteFamily (G.vertexSet P) U) l)
          (familyEdges P) := by
  obtain ⟨M, hMmax, hMh, hU, hUfin, a, b, l, ha, hb, hl⟩ :=
    exists_maximalHindrance_markedRoute_of_residual_hindered
      hNorm hG hA hP hresidual
  let X := G.vertexSet P
  let H := G.delete X
  let U := H.essentialWarpPart M.1
  let L := G.liftDeleteFamily X U
  let C := G.target ∪ H.terminalFrontier U
  let K := G.retarget C
  have hclean : K.IsCleanFiniteWarp (P ∪ L) :=
    combinedWarp_isCleanFiniteWarp hNorm hA hP hU hUfin
  have hLclean : K.IsCleanFiniteWarp L :=
    DWeb.IsCleanFiniteWarp.subfamily hclean Set.subset_union_right
  have hLavoid : Disjoint (G.vertexSet L) X :=
    G.vertexSet_liftDeleteFamily_disjoint hU.1.2.1
  have hP_L : Disjoint (K.vertexSet P) (K.vertexSet L) := by
    change Disjoint X (G.vertexSet L)
    exact hLavoid.symm
  have haP : a ∉ K.vertexSet P := by
    exact ha.1.2
  refine ⟨M, hMmax, hMh, hU, hUfin, a, b, l, ha, hb, hl, ?_⟩
  intro hnoP
  have hbNotX : b ∉ X := by
    have hbState := route_state_vertices_avoid_designated
      hP_L hl haP hnoP (l.length - 1) (by
        have hpos : 0 < l.length := List.length_pos_iff.mpr hl.1.1
        omega)
    rw [oneHoleRoute_last hl] at hbState
    exact hbState
  have haK : a ∈ K.source \ K.initialSet L := by
    refine ⟨ha.1.1, ?_⟩
    change a ∉ G.initialSet L
    rw [G.initialSet_liftDeleteFamily]
    exact ha.2
  have hbK : b ∈ K.target \ K.terminalFrontier L := by
    refine ⟨Or.inl hb.1, ?_⟩
    change b ∉ G.terminalFrontier L
    rw [G.terminalFrontier_liftDeleteFamily]
    exact hb.2
  have hbH : b ∈ H.target := ⟨hb.1, hbNotX⟩
  obtain ⟨Lplus, hplus, hplusAvoid, hbLplus⟩ :=
    exists_residual_onePointAugmentation_avoiding_with_terminal
      hP_L hLclean hl haP hnoP haK hbK
  change Set G.DPath at Lplus
  change Disjoint (G.vertexSet P) (G.vertexSet Lplus) at hplusAvoid
  change b ∈ G.terminalFrontier Lplus at hbLplus
  let W : Set H.DPath :=
    G.restrictDeleteFamily X Lplus hplusAvoid.symm
  have hW : H.IsWave W := by
    exact residualWave_of_avoiding_onePointAugmentation
      G X hU.1 hplus hplusAvoid
  have hbW : b ∈ H.terminalFrontier W := by
    change b ∈ (G.delete X).terminalFrontier
      (G.restrictDeleteFamily X Lplus hplusAvoid.symm)
    rw [G.terminalFrontier_restrictDeleteFamily]
    exact hbLplus
  exact (not_exists_wave_with_fresh_target_terminal_of_isMax
    M hMmax hbH hb.2) ⟨W, hW, hbW⟩

#print axioms familyEdges_liftDeleteFamily
#print axioms DWeb.IsCleanFiniteWarp.subfamily
#print axioms oneHoleMarkedStep_union_iff_right_of_avoids_left
#print axioms reducedMarkedRoute_right_of_no_left_backward
#print axioms exists_maximalResidualRoute_with_designatedBackwardContact

end SingularMarkedResidualDesignatedContact
end CardinalInduction
end Erdos599
