/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.OneHoleSearch

/-!
# The blocking branch of the one-hole residual search

The residual search reaches vertices from an uncovered source by unused
edges in the forward direction and old warp edges in the backward direction.
If it reaches no uncovered target, the last reachable vertex on each old
path is a separator.  This file proves that boundary assertion independently
of the contact-normalization needed by the augmenting branch.
-/

namespace Erdos599
namespace DWeb

open Set DirectedPath
open Alternating

universe u

variable {V : Type u}

namespace DirectedPath.Walk

private theorem suffix_total_local {α : Type*} {a b l : List α}
    (ha : a <:+ l) (hb : b <:+ l) : a <:+ b ∨ b <:+ a := by
  wlog hlen : a.length ≤ b.length generalizing a b
  · exact Or.symm (this hb ha (Nat.le_of_not_ge hlen))
  · apply Or.inl
    have har := ha.reverse
    have hbr := hb.reverse
    rw [List.prefix_iff_eq_take] at har hbr
    apply List.reverse_prefix.mp
    rw [List.prefix_iff_eq_take]
    rw [List.length_reverse] at har hbr ⊢
    rw [har, hbr, List.take_take, Nat.min_eq_left hlen]

private theorem singleton_end_suffix {D : Digraph V} {a b : V}
    (w : Walk D a b) : [b] <:+ w.support := by
  induction w with
  | nil => exact List.suffix_rfl
  | @cons a c b hac w ih =>
      exact ih.trans (by simpa using List.suffix_cons a w.support)

/-- Backward closure along every edge of a finite walk propagates membership
from any vertex of the walk to its initial vertex. -/
private theorem start_mem_of_meets_of_backwardClosed
    (G : DWeb V) (J : Set G.DPath) {R : Set V}
    (hback : ∀ {x y}, (x, y) ∈ familyEdges J → y ∈ R → x ∈ R)
    {a b : V} (w : Walk G.graph a b)
    (hedges : w.edgeSet ⊆ familyEdges J) (hmeets : w.Meets R) :
    a ∈ R := by
  induction w with
  | @nil u =>
      rcases hmeets with ⟨x, hx, hxR⟩
      have hxu : x = u := by
        simpa only [DirectedPath.Walk.support_nil, List.mem_singleton] using hx
      exact hxu ▸ hxR
  | @cons a c b hac w ih =>
      rcases hmeets with ⟨x, hx, hxR⟩
      simp only [DirectedPath.Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hxR
      · apply hback (hedges (by
          simp only [DirectedPath.Walk.edgeSet_cons, Set.mem_union,
            Set.mem_singleton_iff]
          exact Or.inl rfl))
        apply ih
        · intro e he
          apply hedges
          simp only [DirectedPath.Walk.edgeSet_cons, Set.mem_union]
          exact Or.inr he
        · exact ⟨x, hx, hxR⟩

/-- An edge of a walk determines the suffix beginning with that edge. -/
private theorem exists_cons_suffix_of_mem_edgeSet
    {D : Digraph V} {a b x y : V} (w : Walk D a b)
    (hxy : (x, y) ∈ w.edgeSet) :
    ∃ (h : D.Adj x y) (r : Walk D y b),
      (Walk.cons h r).support <:+ w.support := by
  induction w with
  | nil => simp at hxy
  | @cons a c b hac w ih =>
      simp only [DirectedPath.Walk.edgeSet_cons, Set.mem_union,
        Set.mem_singleton_iff] at hxy
      rcases hxy with hxy | hxy
      · have hxa : x = a := congrArg Prod.fst hxy
        have hyc : y = c := congrArg Prod.snd hxy
        subst x
        subst y
        exact ⟨hac, w, List.suffix_rfl⟩
      · obtain ⟨h, r, hr⟩ := ih hxy
        exact ⟨h, r, hr.trans (by simpa using List.suffix_cons a w.support)⟩

/-- The start vertex satisfying the defining properties of a last hit is
unique. -/
private theorem LastHit.startpoint_eq {D : Digraph V} {a b : V}
    {w : Walk D a b} {R : Set V} (L M : w.LastHit R) :
    L.startpoint = M.startpoint := by
  rcases suffix_total_local L.support_suffix M.support_suffix with hLM | hML
  · have hm : L.startpoint ∈ M.walk.support :=
      hLM.subset L.walk.start_mem_support
    have hm' : L.startpoint = M.startpoint ∨
        L.startpoint ∈ M.walk.support.tail := by
      have hhead : M.startpoint ∈ M.walk.support.head? := by
        rw [List.head?_eq_head M.walk.support_ne_nil, M.walk.head_support]
        simp
      have hs := List.eq_cons_of_mem_head? hhead
      rw [hs] at hm ⊢
      simpa using hm
    rcases hm' with h | h
    · exact h
    · exact False.elim (M.no_mem_after h L.startpoint_mem)
  · have hl : M.startpoint ∈ L.walk.support :=
      hML.subset M.walk.start_mem_support
    have hl' : M.startpoint = L.startpoint ∨
        M.startpoint ∈ L.walk.support.tail := by
      have hhead : L.startpoint ∈ L.walk.support.head? := by
        rw [List.head?_eq_head L.walk.support_ne_nil, L.walk.head_support]
        simp
      have hs := List.eq_cons_of_mem_head? hhead
      rw [hs] at hl ⊢
      simpa using hl
    rcases hl' with h | h
    · exact h.symm
    · exact False.elim (L.no_mem_after h M.startpoint_mem)

end DirectedPath.Walk

/-- If an old path edge leaves a backward-closed set, its tail is exactly
the last vertex of that set on the old path. -/
theorem lastHitCut_eq_of_mem_edge_boundary (G : DWeb V)
    (J : Set G.DPath) (hfin : G.HasFiniteCharacter J) (R : Set V)
    (hback : ∀ {x y}, (x, y) ∈ familyEdges J → y ∈ R → x ∈ R)
    (p : J) {x y : V} (hxy : (x, y) ∈ p.1.edgeSet)
    (hx : x ∈ R) (hy : y ∉ R) :
    G.lastHitCut J hfin R p = x := by
  let q := G.finiteMemberPath J hfin p
  have hpq : p.1 = .inl q := G.finiteMemberPath_eq J hfin p
  have hxyq : (x, y) ∈ q.edgeSet := by
    rw [hpq] at hxy
    exact hxy
  obtain ⟨h, r, hsuffix⟩ :=
    DirectedPath.Walk.exists_cons_suffix_of_mem_edgeSet q.walk hxyq
  have hconsEdges : (Walk.cons h r).edgeSet ⊆ q.edgeSet :=
    DirectedPath.Walk.edgeSet_subset_of_support_suffix
      (Walk.cons h r) q.walk hsuffix
  have hqEdges : q.edgeSet ⊆ familyEdges J := by
    intro e he
    simp only [familyEdges, Set.mem_iUnion]
    exact ⟨p.1, p.2, by simpa [hpq] using he⟩
  have hrEdges : r.edgeSet ⊆ familyEdges J := by
    intro e he
    apply hqEdges (hconsEdges ?_)
    simp only [Walk.edgeSet_cons, Set.mem_union]
    exact Or.inr he
  have hrNoMeet : ¬ r.Meets R := by
    intro hr
    exact hy (DirectedPath.Walk.start_mem_of_meets_of_backwardClosed
      G J hback r hrEdges hr)
  have hmeet : q.walk.Meets R := by
    exact ⟨x, (q.edgeSet_subset_support_prod hxyq).1, hx⟩
  let C : q.walk.LastHit R := {
    startpoint := x
    walk := Walk.cons h r
    startpoint_mem := hx
    support_suffix := hsuffix
    no_mem_after := by
      intro z hz hzR
      apply hrNoMeet
      exact ⟨z, by simpa using hz, hzR⟩ }
  dsimp only [lastHitCut]
  split_ifs with hm
  · exact DirectedPath.Walk.LastHit.startpoint_eq
      (q.walk.lastHit R hm) C
  · exact False.elim (hm hmeet)

/-- If the terminal vertex of an old finite path is in a set, it is that
path's last hit of the set. -/
theorem lastHitCut_eq_of_terminal_mem (G : DWeb V)
    (J : Set G.DPath) (hfin : G.HasFiniteCharacter J) (R : Set V)
    (p : J) {b : V} (hterminal : G.terminal? p.1 = some b)
    (hb : b ∈ R) :
    G.lastHitCut J hfin R p = b := by
  let q := G.finiteMemberPath J hfin p
  have hpq : p.1 = .inl q := G.finiteMemberPath_eq J hfin p
  have hfinish : q.finish = b := by
    rw [hpq] at hterminal
    exact Option.some.inj hterminal
  subst b
  have hmeet : q.walk.Meets R :=
    ⟨q.finish, q.finish_mem_support, hb⟩
  have hsingletonSuffix :
      (Walk.nil : Walk G.graph q.finish q.finish).support <:+ q.walk.support :=
    DirectedPath.Walk.singleton_end_suffix q.walk
  let C : q.walk.LastHit R := {
    startpoint := q.finish
    walk := .nil
    startpoint_mem := hb
    support_suffix := hsingletonSuffix
    no_mem_after := by simp }
  dsimp only [lastHitCut]
  split_ifs with hm
  · exact DirectedPath.Walk.LastHit.startpoint_eq
      (q.walk.lastHit R hm) C
  · exact False.elim (hm hmeet)

/-- Meeting a member of the old warp forces its initial vertex to be
reachable, because all old edges may be traversed backwards. -/
theorem initial_mem_of_member_meets_backwardClosed (G : DWeb V)
    (J : Set G.DPath) (hfin : G.HasFiniteCharacter J) (R : Set V)
    (hback : ∀ {x y}, (x, y) ∈ familyEdges J → y ∈ R → x ∈ R)
    (p : J) (hmeets : ∃ x ∈ p.1.support, x ∈ R) :
    p.1.initial ∈ R := by
  let q := G.finiteMemberPath J hfin p
  have hpq : p.1 = .inl q := G.finiteMemberPath_eq J hfin p
  have hqEdges : q.edgeSet ⊆ familyEdges J := by
    intro e he
    simp only [familyEdges, Set.mem_iUnion]
    exact ⟨p.1, p.2, by simpa [hpq] using he⟩
  rw [hpq]
  apply DirectedPath.Walk.start_mem_of_meets_of_backwardClosed
    G J hback q.walk hqEdges
  rcases hmeets with ⟨x, hx, hxR⟩
  rw [hpq] at hx
  exact ⟨x, hx, hxR⟩

/-! ## The contact-marked reachable set -/

/-- A pending marked state can only be created at a vertex of the old
warp. -/
theorem oneHole_vertexSet_of_pending_reachable (G : DWeb V)
    (J : Set G.DPath) {x : V}
    (hx : (.pending x : OneHoleResidualState V) ∈
      G.OneHoleMarkedStateReachable J) :
    x ∈ G.vertexSet J := by
  rcases hx with ⟨a, ha, hax⟩
  cases hax with
  | tail _ hstep =>
      cases ‹OneHoleResidualState V› with
      | ready y => exact hstep.2.2
      | pending y => exact hstep.elim

/-- An old edge pointing to any marked-reachable vertex can be cancelled;
its tail is therefore ready-reachable. -/
theorem oneHole_ready_of_familyEdge_to_marked (G : DWeb V)
    (J : Set G.DPath) {x y : V}
    (hy : y ∈ G.OneHoleMarkedReachable J)
    (hxy : (x, y) ∈ familyEdges J) :
    x ∈ G.OneHoleReadyReachable J := by
  rcases hy with ⟨s, hs, hsv⟩
  cases s with
  | ready z =>
      have hzy : z = y := hsv
      subst y
      exact G.oneHole_ready_backward J hs hxy
  | pending z =>
      have hzy : z = y := hsv
      subst y
      exact G.oneHole_pending_cancel J hs hxy

/-- In particular, the marked-reachable vertex set is backward closed along
old warp edges. -/
theorem oneHole_markedReachable_backward_of_familyEdge (G : DWeb V)
    (J : Set G.DPath) {x y : V}
    (hy : y ∈ G.OneHoleMarkedReachable J)
    (hxy : (x, y) ∈ familyEdges J) :
    x ∈ G.OneHoleMarkedReachable J :=
  G.oneHole_readyReachable_subset_markedReachable J
    (G.oneHole_ready_of_familyEdge_to_marked J hy hxy)

/-- If the contact-marked residual search contains no uncovered target, its
vertex projection has the exact last-hit blocking boundary. -/
theorem isOneHoleBlockingSet_oneHoleMarkedReachable_of_no_targetGap
    (G : DWeb V) (J : Set G.DPath) (hJ : G.IsCleanFiniteWarp J)
    (hnoTargetGap : Disjoint
      (G.target \ G.terminalFrontier J) (G.OneHoleMarkedReachable J)) :
    G.IsOneHoleBlockingSet J hJ.hasFiniteCharacter
      (G.OneHoleMarkedReachable J) := by
  let R := G.OneHoleMarkedReachable J
  let boundary := Set.range (G.lastHitCut J hJ.hasFiniteCharacter R)
  change G.source ⊆ R ∪ boundary ∧
    (∀ {x y}, G.graph.Adj x y → x ∈ R → y ∉ R → x ∈ boundary) ∧
    G.target ∩ R ⊆ boundary
  have hback : ∀ {x y}, (x, y) ∈ familyEdges J → y ∈ R → x ∈ R := by
    intro x y hxy hy
    exact G.oneHole_markedReachable_backward_of_familyEdge J hy hxy
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    by_cases haInit : a ∈ G.initialSet J
    · obtain ⟨p, hpJ, hpa⟩ := haInit
      let pJ : J := ⟨p, hpJ⟩
      rcases G.lastHitCut_mem_or_eq_initial J hJ.hasFiniteCharacter R pJ with
        hcutR | hcutEq
      · apply Or.inl
        rw [← hpa]
        apply G.initial_mem_of_member_meets_backwardClosed
          J hJ.hasFiniteCharacter R hback pJ
        exact ⟨G.lastHitCut J hJ.hasFiniteCharacter R pJ,
          G.lastHitCut_mem_support J hJ.hasFiniteCharacter R pJ, hcutR⟩
      · apply Or.inr
        refine ⟨pJ, ?_⟩
        exact hcutEq.trans hpa
    · apply Or.inl
      apply G.oneHole_readyReachable_subset_markedReachable J
      exact G.oneHole_sourceGap_subset_readyReachable J ⟨ha, haInit⟩
  · intro x y hxy hx hy
    by_cases hfamily : (x, y) ∈ familyEdges J
    · simp only [familyEdges, Set.mem_iUnion] at hfamily
      obtain ⟨p, hpJ, hpedge⟩ := hfamily
      let pJ : J := ⟨p, hpJ⟩
      refine ⟨pJ, ?_⟩
      exact G.lastHitCut_eq_of_mem_edge_boundary J hJ.hasFiniteCharacter R
        hback pJ hpedge hx hy
    · have hxNotReady : x ∉ G.OneHoleReadyReachable J := by
        intro hxReady
        exact hy (G.oneHole_ready_forward J hxReady hxy hfamily)
      rcases hx with ⟨s, hs, hsv⟩
      cases s with
      | ready z =>
          have hzx : z = x := hsv
          subst x
          exact False.elim (hxNotReady hs)
      | pending z =>
          have hzx : z = x := hsv
          subst x
          have hxJ : z ∈ G.vertexSet J :=
            G.oneHole_vertexSet_of_pending_reachable J hs
          obtain ⟨p, hpJ, hzp⟩ := hxJ
          let pJ : J := ⟨p, hpJ⟩
          let q := G.finiteMemberPath J hJ.hasFiniteCharacter pJ
          have hpq : p = .inl q :=
            G.finiteMemberPath_eq J hJ.hasFiniteCharacter pJ
          have hzq : z ∈ q.support := by
            rw [hpq] at hzp
            exact hzp
          by_cases hzfinish : z = q.finish
          · refine ⟨pJ, ?_⟩
            apply G.lastHitCut_eq_of_terminal_mem J hJ.hasFiniteCharacter R
              pJ (b := z)
            · change G.terminal? p = some z
              rw [hpq]
              simp [hzfinish]
            · exact ⟨.pending z, hs, rfl⟩
          · obtain ⟨w, hzwq⟩ :=
              _root_.Erdos599.Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
                q hzq hzfinish
            have hzwp : (z, w) ∈ p.edgeSet := by
              rw [hpq]
              exact hzwq
            have hzwFamily : (z, w) ∈ familyEdges J := by
              simp only [familyEdges, Set.mem_iUnion]
              exact ⟨p, hpJ, hzwp⟩
            have hwNot : w ∉ R := by
              intro hw
              exact hxNotReady
                (G.oneHole_ready_of_familyEdge_to_marked J hw hzwFamily)
            refine ⟨pJ, ?_⟩
            exact G.lastHitCut_eq_of_mem_edge_boundary J
              hJ.hasFiniteCharacter R hback pJ hzwp
              ⟨.pending z, hs, rfl⟩ hwNot
  · rintro b ⟨hbTarget, hbR⟩
    have hbFrontier : b ∈ G.terminalFrontier J := by
      by_contra hbNot
      exact Set.disjoint_left.1 hnoTargetGap ⟨hbTarget, hbNot⟩ hbR
    obtain ⟨p, hpJ, hpterminal⟩ := hbFrontier
    let pJ : J := ⟨p, hpJ⟩
    refine ⟨pJ, ?_⟩
    exact G.lastHitCut_eq_of_terminal_mem J hJ.hasFiniteCharacter R
      pJ hpterminal hbR

/-- If the residual reachable set contains no uncovered target, its last-hit
cut is a blocking certificate. -/
theorem isOneHoleBlockingSet_oneHoleReachable_of_no_targetGap
    (G : DWeb V) (J : Set G.DPath) (hJ : G.IsCleanFiniteWarp J)
    (hnoTargetGap : Disjoint
      (G.target \ G.terminalFrontier J) (G.OneHoleReachable J)) :
    G.IsOneHoleBlockingSet J hJ.hasFiniteCharacter
      (G.OneHoleReachable J) := by
  let R := G.OneHoleReachable J
  let boundary := Set.range (G.lastHitCut J hJ.hasFiniteCharacter R)
  change G.source ⊆ R ∪ boundary ∧
    (∀ {x y}, G.graph.Adj x y → x ∈ R → y ∉ R → x ∈ boundary) ∧
    G.target ∩ R ⊆ boundary
  have hback : ∀ {x y}, (x, y) ∈ familyEdges J → y ∈ R → x ∈ R := by
    intro x y hxy hy
    exact G.oneHole_reachable_backward_of_familyEdge J hy hxy
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    by_cases haInit : a ∈ G.initialSet J
    · obtain ⟨p, hpJ, hpa⟩ := haInit
      let pJ : J := ⟨p, hpJ⟩
      rcases G.lastHitCut_mem_or_eq_initial J hJ.hasFiniteCharacter R pJ with
        hcutR | hcutEq
      · apply Or.inl
        rw [← hpa]
        apply G.initial_mem_of_member_meets_backwardClosed
          J hJ.hasFiniteCharacter R hback pJ
        exact ⟨G.lastHitCut J hJ.hasFiniteCharacter R pJ,
          G.lastHitCut_mem_support J hJ.hasFiniteCharacter R pJ, hcutR⟩
      · apply Or.inr
        refine ⟨pJ, ?_⟩
        exact hcutEq.trans hpa
    · exact Or.inl (G.oneHole_sourceGap_subset_reachable J ⟨ha, haInit⟩)
  · intro x y hxy hx hy
    have hfamily : (x, y) ∈ familyEdges J :=
      G.oneHole_familyEdge_of_reachable_edge_not_reachable J hx hxy hy
    simp only [familyEdges, Set.mem_iUnion] at hfamily
    obtain ⟨p, hpJ, hpedge⟩ := hfamily
    let pJ : J := ⟨p, hpJ⟩
    refine ⟨pJ, ?_⟩
    exact G.lastHitCut_eq_of_mem_edge_boundary J hJ.hasFiniteCharacter R
      hback pJ hpedge hx hy
  · rintro b ⟨hbTarget, hbR⟩
    have hbFrontier : b ∈ G.terminalFrontier J := by
      by_contra hbNot
      exact Set.disjoint_left.1 hnoTargetGap ⟨hbTarget, hbNot⟩ hbR
    obtain ⟨p, hpJ, hpterminal⟩ := hbFrontier
    let pJ : J := ⟨p, hpJ⟩
    refine ⟨pJ, ?_⟩
    exact G.lastHitCut_eq_of_terminal_mem J hJ.hasFiniteCharacter R
      pJ hpterminal hbR

end DWeb
end Erdos599
