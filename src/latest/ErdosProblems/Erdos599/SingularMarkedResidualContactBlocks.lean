/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularMarkedResidualColorOrder
import ErdosProblems.Erdos599.SingularMarkedResidualTouchedPaths

/-!
# Residual isolation outside the first and last designated contacts

The first and last designated backward contacts cut a marked two-colour
route into three pieces.  Every backward step strictly before the first
contact and strictly after the last contact has the residual colour.  The
route vertices before the first contact, and the targets of transitions
after the last contact, avoid the designated carrier as well.

Thus the only designated-carrier boundary states of the two outer pieces
are the pending source of the first cancellation and the ready source of
the first transition after the last cancellation.  These are the exact
seams required by the finite colour-preserving switch.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularMarkedResidualContactBlocks

open DWeb Alternating
open SingularMarkedResidualColorOrder
open SingularMarkedResidualTouchedPaths

universe u

variable {V : Type u}

private theorem familyEdges_mono_right
    (G : DWeb V) (P L : Set G.DPath) :
    familyEdges L ⊆ familyEdges (P ∪ L) := by
  intro e he
  simp only [familyEdges, Set.mem_iUnion] at he ⊢
  obtain ⟨p, hpL, hpEdge⟩ := he
  exact ⟨p, Or.inr hpL, hpEdge⟩

/-- A designated cancellation has a unique owner in the designated warp.
The statement retains the actual path and edge membership, rather than only
the locally unique incoming/outgoing endpoint. -/
theorem exists_unique_designatedContactOwner
    {G : DWeb V} {P L : Set G.DPath}
    {l : List (OneHoleResidualState V)}
    (hP : G.IsWarp P) {i : Fin (l.length - 1)}
    (hi : IsDesignatedBackwardContact G P L l i) :
    ∃! p : G.DPath, p ∈ P ∧
      ((oneHoleRouteTarget l i).vertex,
        (oneHoleRouteSource l i).vertex) ∈ p.edgeSet := by
  have hiEdge := hi.2
  simp only [familyEdges, Set.mem_iUnion] at hiEdge
  obtain ⟨p, hpP, hpEdge⟩ := hiEdge
  refine ⟨p, ⟨hpP, hpEdge⟩, ?_⟩
  rintro q ⟨hqP, hqEdge⟩
  have hpq : p = q := DWeb.IsWarp.eq_of_mem_support hP hpP hqP
    (p.edgeSet_subset_support_prod hpEdge).1
    (q.edgeSet_subset_support_prod hqEdge).1
  exact hpq.symm

/-- The unique owner of every designated cancellation belongs to the finite
touched designated subfamily. -/
theorem designatedContactOwner_mem_touched
    {G : DWeb V} {P L : Set G.DPath}
    {l : List (OneHoleResidualState V)}
    {i : Fin (l.length - 1)}
    (_hi : IsDesignatedBackwardContact G P L l i)
    {p : G.DPath} (hpP : p ∈ P)
    (hpEdge : ((oneHoleRouteTarget l i).vertex,
        (oneHoleRouteSource l i).vertex) ∈ p.edgeSet) :
    p ∈ touchedDesignatedPaths G P l := by
  refine ⟨hpP, (oneHoleRouteTarget l i).vertex,
    (p.edgeSet_subset_support_prod hpEdge).1, ?_⟩
  apply state_vertex_mem_routeVertexSet
  exact List.getElem_mem (show i.1 + 1 < l.length by omega)

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

/-- Every backward transition strictly before the first designated contact
has the residual colour. -/
theorem backwardStep_mem_residual_before_first
    {G : DWeb V} {P L : Set G.DPath}
    {l : List (OneHoleResidualState V)}
    {i r : Fin (l.length - 1)}
    (hfirst : ∀ r', r' < i →
      ¬ IsDesignatedBackwardContact G P L l r')
    (hri : r < i)
    (hr : OneHoleChosenBackwardStep G (P ∪ L)
      (oneHoleRouteSource l r) (oneHoleRouteTarget l r)) :
    ((oneHoleRouteTarget l r).vertex,
      (oneHoleRouteSource l r).vertex) ∈ familyEdges L := by
  have he : ((oneHoleRouteTarget l r).vertex,
      (oneHoleRouteSource l r).vertex) ∈
      oneHoleRouteBackwardEdges G (P ∪ L) l := ⟨r, hr, rfl⟩
  rcases backwardEdges_subset_designated_union_residual G P L l he with
    heP | heL
  · exact False.elim (hfirst r hri ⟨hr, heP⟩)
  · exact heL

/-- Every backward transition strictly after the last designated contact
has the residual colour. -/
theorem backwardStep_mem_residual_after_last
    {G : DWeb V} {P L : Set G.DPath}
    {l : List (OneHoleResidualState V)}
    {j r : Fin (l.length - 1)}
    (hlast : ∀ r', j < r' →
      ¬ IsDesignatedBackwardContact G P L l r')
    (hjr : j < r)
    (hr : OneHoleChosenBackwardStep G (P ∪ L)
      (oneHoleRouteSource l r) (oneHoleRouteTarget l r)) :
    ((oneHoleRouteTarget l r).vertex,
      (oneHoleRouteSource l r).vertex) ∈ familyEdges L := by
  have he : ((oneHoleRouteTarget l r).vertex,
      (oneHoleRouteSource l r).vertex) ∈
      oneHoleRouteBackwardEdges G (P ∪ L) l := ⟨r, hr, rfl⟩
  rcases backwardEdges_subset_designated_union_residual G P L l he with
    heP | heL
  · exact False.elim (hlast r hjr ⟨hr, heP⟩)
  · exact heL

private theorem routeTarget_avoids_designated_before_first
    {G : DWeb V} {P L : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hdisjoint : Disjoint (G.vertexSet P) (G.vertexSet L))
    (hl : IsReducedMarkedRoute G (P ∪ L) a b l)
    {i r : Fin (l.length - 1)}
    (hfirst : ∀ r', r' < i →
      ¬ IsDesignatedBackwardContact G P L l r')
    (hnextBefore : r.1 + 1 < i.1) :
    (oneHoleRouteTarget l r).vertex ∉ G.vertexSet P := by
  have hri : r < i := by omega
  have hstep := oneHoleRoute_step hl.1.2.1 r
  rcases (oneHoleMarkedStep_iff_chosenDirection G (P ∪ L)
      (oneHoleRouteSource l r) (oneHoleRouteTarget l r)).1 hstep with
    hforward | hbackward
  · cases hs : oneHoleRouteSource l r with
    | pending x =>
      cases ht : oneHoleRouteTarget l r <;>
        simp [OneHoleChosenForwardStep, hs, ht] at hforward
    | ready x =>
      cases ht : oneHoleRouteTarget l r with
      | ready y =>
        simp only [OneHoleChosenForwardStep, hs, ht] at hforward
        intro hyP
        obtain ⟨p, hpP, hyp⟩ := hyP
        exact hforward.2.2 ⟨p, Or.inl hpP, hyp⟩
      | pending y =>
        have hsBound : r.1 + 1 < l.length - 1 := by omega
        let s : Fin (l.length - 1) := ⟨r.1 + 1, hsBound⟩
        have hsi : s < i := by
          change r.1 + 1 < i.1
          exact hnextBefore
        have hsourceNext : oneHoleRouteSource l s = .pending y := by
          change l[r.1 + 1] = .pending y
          exact ht
        have hnextStep := oneHoleRoute_step hl.1.2.1 s
        have hnextBackward : OneHoleChosenBackwardStep G (P ∪ L)
            (oneHoleRouteSource l s) (oneHoleRouteTarget l s) := by
          rcases (oneHoleMarkedStep_iff_chosenDirection G (P ∪ L)
              (oneHoleRouteSource l s) (oneHoleRouteTarget l s)).1
              hnextStep with hnForward | hnBackward
          · cases htNext : oneHoleRouteTarget l s <;>
              simp [OneHoleChosenForwardStep, hsourceNext, htNext] at hnForward
          · exact hnBackward
        have heL := backwardStep_mem_residual_before_first
          hfirst hsi hnextBackward
        have hyL : y ∈ G.vertexSet L := by
          have hmem := right_mem_vertexSet_of_mem_familyEdges heL
          rw [hsourceNext] at hmem
          exact hmem
        exact fun hyP ↦ Set.disjoint_left.1 hdisjoint hyP hyL
  · have heL := backwardStep_mem_residual_before_first
      hfirst hri hbackward
    exact fun hyP ↦ Set.disjoint_left.1 hdisjoint hyP
      (left_mem_vertexSet_of_mem_familyEdges heL)

/-- Every route state strictly before the first designated cancellation
avoids the designated carrier.  The source state of the first cancellation
is deliberately excluded: it is the pending boundary contact. -/
theorem routeState_avoids_designated_before_first
    {G : DWeb V} {P L : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hdisjoint : Disjoint (G.vertexSet P) (G.vertexSet L))
    (hl : IsReducedMarkedRoute G (P ∪ L) a b l)
    (ha : a ∉ G.vertexSet P)
    {i : Fin (l.length - 1)}
    (hfirst : ∀ r, r < i →
      ¬ IsDesignatedBackwardContact G P L l r) :
    ∀ n (hn : n < l.length), n < i.1 →
      l[n].vertex ∉ G.vertexSet P := by
  intro n hn hni
  by_cases hn0 : n = 0
  · subst n
    rw [oneHoleRoute_first hl]
    exact ha
  · have hrBound : n - 1 < l.length - 1 := by omega
    let r : Fin (l.length - 1) := ⟨n - 1, hrBound⟩
    have htarget : oneHoleRouteTarget l r = l[n] := by
      change l[(n - 1) + 1] = l[n]
      congr 1
      omega
    rw [← htarget]
    apply routeTarget_avoids_designated_before_first hdisjoint hl hfirst
    change (n - 1) + 1 < i.1
    omega

/-- A forward transition whose target still lies strictly before the first
designated cancellation has both endpoints outside the designated carrier.
The unique predecessor transition of the first contact is excluded because
it is precisely the incoming boundary crossing. -/
theorem forwardStep_avoids_designated_before_first
    {G : DWeb V} {P L : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hdisjoint : Disjoint (G.vertexSet P) (G.vertexSet L))
    (hl : IsReducedMarkedRoute G (P ∪ L) a b l)
    (ha : a ∉ G.vertexSet P)
    {i r : Fin (l.length - 1)}
    (hfirst : ∀ r', r' < i →
      ¬ IsDesignatedBackwardContact G P L l r')
    (hnextBefore : r.1 + 1 < i.1)
    (_hr : OneHoleChosenForwardStep G (P ∪ L)
      (oneHoleRouteSource l r) (oneHoleRouteTarget l r)) :
    ((oneHoleRouteSource l r).vertex,
      (oneHoleRouteTarget l r).vertex) ∈
      (G.vertexSet P)ᶜ ×ˢ (G.vertexSet P)ᶜ := by
  constructor
  · exact routeState_avoids_designated_before_first
      hdisjoint hl ha hfirst r.1 (by omega) (by omega)
  · have hstate := routeState_avoids_designated_before_first
      hdisjoint hl ha hfirst (r.1 + 1) (by omega) hnextBefore
    change l[r.1 + 1].vertex ∉ G.vertexSet P at hstate
    exact hstate

/-- Targets of all transitions strictly after the last designated
cancellation avoid the designated carrier.  In particular, after the first
forward transition leaving the last contact, the remaining suffix is wholly
outside the designated carrier except for possible inserted edges crossing
its boundary. -/
theorem routeTarget_avoids_designated_after_last
    {G : DWeb V} {P L : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hdisjoint : Disjoint (G.vertexSet P) (G.vertexSet L))
    (hl : IsReducedMarkedRoute G (P ∪ L) a b l)
    {j r : Fin (l.length - 1)}
    (hlast : ∀ r', j < r' →
      ¬ IsDesignatedBackwardContact G P L l r')
    (hjr : j < r) :
    (oneHoleRouteTarget l r).vertex ∉ G.vertexSet P := by
  have hstep := oneHoleRoute_step hl.1.2.1 r
  rcases (oneHoleMarkedStep_iff_chosenDirection G (P ∪ L)
      (oneHoleRouteSource l r) (oneHoleRouteTarget l r)).1 hstep with
    hforward | hbackward
  · cases hs : oneHoleRouteSource l r with
    | pending x =>
      cases ht : oneHoleRouteTarget l r <;>
        simp [OneHoleChosenForwardStep, hs, ht] at hforward
    | ready x =>
      cases ht : oneHoleRouteTarget l r with
      | ready y =>
        simp only [OneHoleChosenForwardStep, hs, ht] at hforward
        intro hyP
        obtain ⟨p, hpP, hyp⟩ := hyP
        exact hforward.2.2 ⟨p, Or.inl hpP, hyp⟩
      | pending y =>
        by_cases hlastTransition : r.1 + 1 = l.length - 1
        · have htLast : l[l.length - 1] = .pending y := by
            change l[r.1 + 1] = .pending y at ht
            simpa only [hlastTransition] using ht
          have hcontra :
              (OneHoleResidualState.ready b : OneHoleResidualState V) =
                .pending y := (oneHoleRoute_last hl).symm.trans htLast
          cases hcontra
        · have hsBound : r.1 + 1 < l.length - 1 := by omega
          let s : Fin (l.length - 1) := ⟨r.1 + 1, hsBound⟩
          have hjs : j < s := by
            change j.1 < r.1 + 1
            exact Nat.lt_succ_of_le (Nat.le_of_lt hjr)
          have hsourceNext : oneHoleRouteSource l s = .pending y := by
            change l[r.1 + 1] = .pending y
            exact ht
          have hnextStep := oneHoleRoute_step hl.1.2.1 s
          have hnextBackward : OneHoleChosenBackwardStep G (P ∪ L)
              (oneHoleRouteSource l s) (oneHoleRouteTarget l s) := by
            rcases (oneHoleMarkedStep_iff_chosenDirection G (P ∪ L)
                (oneHoleRouteSource l s) (oneHoleRouteTarget l s)).1
                hnextStep with hnForward | hnBackward
            · cases htNext : oneHoleRouteTarget l s <;>
                simp [OneHoleChosenForwardStep, hsourceNext, htNext] at hnForward
            · exact hnBackward
          have heL := backwardStep_mem_residual_after_last
            hlast hjs hnextBackward
          have hyL : y ∈ G.vertexSet L := by
            have hmem := right_mem_vertexSet_of_mem_familyEdges heL
            rw [hsourceNext] at hmem
            exact hmem
          exact fun hyP ↦ Set.disjoint_left.1 hdisjoint hyP hyL
  · have heL := backwardStep_mem_residual_after_last hlast hjr hbackward
    exact fun hyP ↦ Set.disjoint_left.1 hdisjoint hyP
      (left_mem_vertexSet_of_mem_familyEdges heL)

/-- A forward transition strictly beyond the immediate successor of the
last designated cancellation has both endpoints outside the designated
carrier.  The immediate successor is excluded because it is the outgoing
boundary crossing. -/
theorem forwardStep_avoids_designated_after_last
    {G : DWeb V} {P L : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hdisjoint : Disjoint (G.vertexSet P) (G.vertexSet L))
    (hl : IsReducedMarkedRoute G (P ∪ L) a b l)
    {j r : Fin (l.length - 1)}
    (hlast : ∀ r', j < r' →
      ¬ IsDesignatedBackwardContact G P L l r')
    (hstrict : j.1 + 1 < r.1)
    (_hr : OneHoleChosenForwardStep G (P ∪ L)
      (oneHoleRouteSource l r) (oneHoleRouteTarget l r)) :
    ((oneHoleRouteSource l r).vertex,
      (oneHoleRouteTarget l r).vertex) ∈
      (G.vertexSet P)ᶜ ×ˢ (G.vertexSet P)ᶜ := by
  have hrPos : 0 < r.1 := by omega
  have hqBound : r.1 - 1 < l.length - 1 := by omega
  let q : Fin (l.length - 1) := ⟨r.1 - 1, hqBound⟩
  have hjq : j < q := by
    change j.1 < r.1 - 1
    omega
  have hsourceEq : oneHoleRouteSource l r = oneHoleRouteTarget l q := by
    change l[r.1] = l[(r.1 - 1) + 1]
    congr 1
    omega
  constructor
  · rw [hsourceEq]
    exact routeTarget_avoids_designated_after_last
      hdisjoint hl hlast hjq
  · exact routeTarget_avoids_designated_after_last
      hdisjoint hl hlast (by omega)

private theorem markedStep_residual_strictly_before_first
    {G : DWeb V} {P L : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hdisjoint : Disjoint (G.vertexSet P) (G.vertexSet L))
    (hl : IsReducedMarkedRoute G (P ∪ L) a b l)
    (ha : a ∉ G.vertexSet P)
    {i r : Fin (l.length - 1)}
    (hfirst : ∀ r', r' < i →
      ¬ IsDesignatedBackwardContact G P L l r')
    (hnextBefore : r.1 + 1 < i.1) :
    G.OneHoleMarkedStep L
      (oneHoleRouteSource l r) (oneHoleRouteTarget l r) := by
  have htargetAvoid :
      (oneHoleRouteTarget l r).vertex ∉ G.vertexSet P := by
    have hstate := routeState_avoids_designated_before_first
      hdisjoint hl ha hfirst (r.1 + 1) (by omega) hnextBefore
    change l[r.1 + 1].vertex ∉ G.vertexSet P at hstate
    exact hstate
  have hstep := oneHoleRoute_step hl.1.2.1 r
  rcases (oneHoleMarkedStep_iff_chosenDirection G (P ∪ L)
      (oneHoleRouteSource l r) (oneHoleRouteTarget l r)).1 hstep with
    hforward | hbackward
  · cases hs : oneHoleRouteSource l r <;>
      cases ht : oneHoleRouteTarget l r <;>
      simp only [OneHoleChosenForwardStep, hs, ht,
        OneHoleResidualState.vertex_ready,
        OneHoleResidualState.vertex_pending] at hforward htargetAvoid ⊢
    · exact Or.inl ⟨hforward.1,
        fun heL ↦ hforward.2.1 (familyEdges_mono_right G P L heL),
        fun hyL ↦ hforward.2.2 (by
          rw [G.vertexSet_union]
          exact Or.inr hyL)⟩
    · refine ⟨hforward.1,
        fun heL ↦ hforward.2.1 (familyEdges_mono_right G P L heL), ?_⟩
      have hmem := hforward.2.2
      rw [G.vertexSet_union] at hmem
      rcases hmem with hyP | hyL
      · exact False.elim (htargetAvoid hyP)
      · exact hyL
  · have hri : r < i := by omega
    have heL := backwardStep_mem_residual_before_first
      hfirst hri hbackward
    cases hs : oneHoleRouteSource l r <;>
      cases ht : oneHoleRouteTarget l r <;>
      simp only [OneHoleChosenBackwardStep, hs, ht] at hbackward heL ⊢
    · exact Or.inr heL
    · exact heL

private theorem markedStep_residual_after_last
    {G : DWeb V} {P L : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hdisjoint : Disjoint (G.vertexSet P) (G.vertexSet L))
    (hl : IsReducedMarkedRoute G (P ∪ L) a b l)
    {j r : Fin (l.length - 1)}
    (hlast : ∀ r', j < r' →
      ¬ IsDesignatedBackwardContact G P L l r')
    (hjr : j < r) :
    G.OneHoleMarkedStep L
      (oneHoleRouteSource l r) (oneHoleRouteTarget l r) := by
  have htargetAvoid := routeTarget_avoids_designated_after_last
    hdisjoint hl hlast hjr
  have hstep := oneHoleRoute_step hl.1.2.1 r
  rcases (oneHoleMarkedStep_iff_chosenDirection G (P ∪ L)
      (oneHoleRouteSource l r) (oneHoleRouteTarget l r)).1 hstep with
    hforward | hbackward
  · cases hs : oneHoleRouteSource l r <;>
      cases ht : oneHoleRouteTarget l r <;>
      simp only [OneHoleChosenForwardStep, hs, ht,
        OneHoleResidualState.vertex_ready,
        OneHoleResidualState.vertex_pending] at hforward htargetAvoid ⊢
    · exact Or.inl ⟨hforward.1,
        fun heL ↦ hforward.2.1 (familyEdges_mono_right G P L heL),
        fun hyL ↦ hforward.2.2 (by
          rw [G.vertexSet_union]
          exact Or.inr hyL)⟩
    · refine ⟨hforward.1,
        fun heL ↦ hforward.2.1 (familyEdges_mono_right G P L heL), ?_⟩
      have hmem := hforward.2.2
      rw [G.vertexSet_union] at hmem
      rcases hmem with hyP | hyL
      · exact False.elim (htargetAvoid hyP)
      · exact hyL
  · have heL := backwardStep_mem_residual_after_last hlast hjr hbackward
    cases hs : oneHoleRouteSource l r <;>
      cases ht : oneHoleRouteTarget l r <;>
      simp only [OneHoleChosenBackwardStep, hs, ht] at hbackward heL ⊢
    · exact Or.inr heL
    · exact heL

/-- A pending route state which is not the first state has a canonical
predecessor transition, and that transition is forward.  A backward marked
transition always has a ready target, so it cannot end at the displayed
pending state. -/
theorem exists_predecessorForward_of_source_pending
    {G : DWeb V} {J : Set G.DPath} {a b x : V}
    {l : List (OneHoleResidualState V)}
    (hl : IsReducedMarkedRoute G J a b l)
    {i : Fin (l.length - 1)}
    (hsource : oneHoleRouteSource l i = .pending x) :
    ∃ r : Fin (l.length - 1), r < i ∧
      oneHoleRouteTarget l r = oneHoleRouteSource l i ∧
      OneHoleChosenForwardStep G J
        (oneHoleRouteSource l r) (oneHoleRouteTarget l r) := by
  have hiPos : 0 < i.1 := by
    by_contra hnot
    have hi0 : i.1 = 0 := by omega
    have hfirstState : oneHoleRouteSource l i = .ready a := by
      change l[i.1] = .ready a
      simpa only [hi0] using oneHoleRoute_first hl
    have hcontra :
        (OneHoleResidualState.ready a : OneHoleResidualState V) =
          .pending x := hfirstState.symm.trans hsource
    cases hcontra
  have hrBound : i.1 - 1 < l.length - 1 := by omega
  let r : Fin (l.length - 1) := ⟨i.1 - 1, hrBound⟩
  have hri : r < i := by
    change i.1 - 1 < i.1
    omega
  have htarget : oneHoleRouteTarget l r = oneHoleRouteSource l i := by
    change l[(i.1 - 1) + 1] = l[i.1]
    congr 1
    omega
  have hstep := oneHoleRoute_step hl.1.2.1 r
  rcases (oneHoleMarkedStep_iff_chosenDirection G J
      (oneHoleRouteSource l r) (oneHoleRouteTarget l r)).1 hstep with
    hforward | hbackward
  · exact ⟨r, hri, htarget, hforward⟩
  · cases hs : oneHoleRouteSource l r <;>
      simp [OneHoleChosenBackwardStep, htarget, hsource, hs] at hbackward

/-- The route prefix ending at the incoming designated seam is a genuine
residual marked reachability macro after its final pending tag is changed to
ready.  Taking a shortest representative gives a reduced residual route
from the original missing residual source to the seam vertex. -/
theorem exists_reducedResidualPrefixRoute
    {G : DWeb V} {P L : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hdisjoint : Disjoint (G.vertexSet P) (G.vertexSet L))
    (hl : IsReducedMarkedRoute G (P ∪ L) a b l)
    (ha : a ∉ G.vertexSet P)
    {i : Fin (l.length - 1)}
    (hi : IsDesignatedBackwardContact G P L l i)
    (hfirst : ∀ r, r < i →
      ¬ IsDesignatedBackwardContact G P L l r) :
    ∃ x : V, oneHoleRouteSource l i = .pending x ∧
      ∃ prefixRoute : List (OneHoleResidualState V),
        IsReducedMarkedRoute G L a x prefixRoute := by
  obtain ⟨x, hsource⟩ :=
    first_designatedBackwardContact_source_pending
      hdisjoint hl ha hi hfirst
  obtain ⟨r, hri, htargetR, hforwardR⟩ :=
    exists_predecessorForward_of_source_pending hl hsource
  have hreachBefore : ∀ n (hn : n < i.1),
      Relation.ReflTransGen (G.OneHoleMarkedStep L)
        (.ready a) l[n] := by
    intro n hn
    induction n with
    | zero =>
        rw [oneHoleRoute_first hl]
    | succ n ih =>
        have hnBefore : n < i.1 := by omega
        have hnBound : n < l.length - 1 := by omega
        let s : Fin (l.length - 1) := ⟨n, hnBound⟩
        have hstepL := markedStep_residual_strictly_before_first
          hdisjoint hl ha hfirst (r := s) (by omega)
        have hsourceS : oneHoleRouteSource l s = l[n] := rfl
        have htargetS : oneHoleRouteTarget l s = l[n + 1] := by rfl
        rw [hsourceS, htargetS] at hstepL
        exact (ih hnBefore).trans (Relation.ReflTransGen.single hstepL)
  have hreachR : Relation.ReflTransGen (G.OneHoleMarkedStep L)
      (.ready a) (oneHoleRouteSource l r) := by
    change Relation.ReflTransGen (G.OneHoleMarkedStep L)
      (.ready a) l[r.1]
    exact hreachBefore r.1 hri
  have hxP : x ∈ G.vertexSet P := by
    have hmem := right_mem_vertexSet_of_mem_familyEdges hi.2
    rw [hsource] at hmem
    exact hmem
  have hxNotL : x ∉ G.vertexSet L := fun hxL ↦
    Set.disjoint_left.1 hdisjoint hxP hxL
  have hfinalL : G.OneHoleMarkedStep L
      (oneHoleRouteSource l r) (.ready x) := by
    cases hs : oneHoleRouteSource l r with
    | pending z =>
        simp [OneHoleChosenForwardStep, hs] at hforwardR
    | ready z =>
        have hforwardR' : OneHoleChosenForwardStep G (P ∪ L)
            (.ready z) (.pending x) := by
          simpa only [OneHoleChosenForwardStep, hs, htargetR,
            hsource] using hforwardR
        simp only [OneHoleChosenForwardStep] at hforwardR'
        simp only [OneHoleMarkedStep]
        exact Or.inl ⟨hforwardR'.1,
          fun heL ↦ hforwardR'.2.1
            (familyEdges_mono_right G P L heL), hxNotL⟩
  have hreach : Relation.ReflTransGen (G.OneHoleMarkedStep L)
      (.ready a) (.ready x) :=
    hreachR.trans (Relation.ReflTransGen.single hfinalL)
  obtain ⟨prefixRoute, hprefix⟩ := exists_reduced_markedRoute G L hreach
  exact ⟨x, hsource, prefixRoute, hprefix⟩

/-- The route suffix after the last designated cancellation is a genuine
residual marked reachability macro.  Its first state is the ready endpoint
of the last cancelled designated edge, and a shortest representative is a
reduced residual route to the original fresh target. -/
theorem exists_reducedResidualSuffixRoute
    {G : DWeb V} {P L : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hdisjoint : Disjoint (G.vertexSet P) (G.vertexSet L))
    (hl : IsReducedMarkedRoute G (P ∪ L) a b l)
    (hb : b ∉ G.vertexSet P)
    {j : Fin (l.length - 1)}
    (hj : IsDesignatedBackwardContact G P L l j)
    (hlast : ∀ r, j < r →
      ¬ IsDesignatedBackwardContact G P L l r) :
    ∃ y : V, oneHoleRouteTarget l j = .ready y ∧
      ∃ suffixRoute : List (OneHoleResidualState V),
        IsReducedMarkedRoute G L y b suffixRoute := by
  obtain ⟨k, hjk, hsourceK, _hforwardK⟩ :=
    last_designatedBackwardContact_next_forward
      hdisjoint hl hb hj hlast
  have htargetReady : ∃ y, oneHoleRouteTarget l j = .ready y := by
    cases hs : oneHoleRouteSource l j <;>
      cases ht : oneHoleRouteTarget l j <;>
      simp [IsDesignatedBackwardContact, OneHoleChosenBackwardStep,
        hs, ht] at hj ⊢
  obtain ⟨y, htargetY⟩ := htargetReady
  have hsourceY : oneHoleRouteSource l k = .ready y :=
    hsourceK.trans htargetY
  have hreachFrom : ∀ n (hkn : k.1 ≤ n) (hn : n < l.length),
      Relation.ReflTransGen (G.OneHoleMarkedStep L)
        l[k.1] l[n] := by
    intro n hkn hn
    induction n, hkn using Nat.le_induction with
    | base => exact Relation.ReflTransGen.refl
    | @succ n hkn ih =>
        have hnBound : n < l.length - 1 := by omega
        let r : Fin (l.length - 1) := ⟨n, hnBound⟩
        have hjr : j < r := lt_of_lt_of_le hjk hkn
        have hstepL := markedStep_residual_after_last
          hdisjoint hl hlast hjr
        have hsourceR : oneHoleRouteSource l r = l[n] := rfl
        have htargetR : oneHoleRouteTarget l r = l[n + 1] := by rfl
        rw [hsourceR, htargetR] at hstepL
        exact (ih (by omega)).trans (Relation.ReflTransGen.single hstepL)
  have hlastPos : l.length - 1 < l.length := by
    have hpos := List.length_pos_iff.mpr hl.1.1
    omega
  have hkLast : k.1 ≤ l.length - 1 := by omega
  have hreach := hreachFrom (l.length - 1) hkLast hlastPos
  have hreach' : Relation.ReflTransGen (G.OneHoleMarkedStep L)
      (.ready y) (.ready b) := by
    rw [← hsourceY, ← oneHoleRoute_last hl]
    exact hreach
  obtain ⟨suffixRoute, hsuffix⟩ := exists_reduced_markedRoute G L hreach'
  exact ⟨y, htargetY, suffixRoute, hsuffix⟩

/-- Canonical two-sided residual macro decomposition of a mixed-contact
route.  The central interval contains every designated cancellation; the
two outer intervals have honest reduced-route representatives against the
residual colour alone. -/
theorem exists_reducedResidualOuterRoutes
    {G : DWeb V} {P L : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hdisjoint : Disjoint (G.vertexSet P) (G.vertexSet L))
    (hl : IsReducedMarkedRoute G (P ∪ L) a b l)
    (ha : a ∉ G.vertexSet P) (hb : b ∉ G.vertexSet P)
    (hcontact : ¬ Disjoint
      (oneHoleRouteBackwardEdges G (P ∪ L) l) (familyEdges P)) :
    ∃ i j : Fin (l.length - 1), ∃ x y : V,
      IsDesignatedBackwardContact G P L l i ∧
      (∀ i', i' < i →
        ¬ IsDesignatedBackwardContact G P L l i') ∧
      oneHoleRouteSource l i = .pending x ∧
      IsDesignatedBackwardContact G P L l j ∧
      (∀ j', j < j' →
        ¬ IsDesignatedBackwardContact G P L l j') ∧
      i ≤ j ∧ oneHoleRouteTarget l j = .ready y ∧
      ∃ prefixRoute suffixRoute : List (OneHoleResidualState V),
        IsReducedMarkedRoute G L a x prefixRoute ∧
        IsReducedMarkedRoute G L y b suffixRoute := by
  obtain ⟨i, j, _k, _x, hi, hfirst, hsource, hj, hlast,
      hij, _hjk, _hsourceK, _hforwardK⟩ :=
    exists_orderedDesignatedContactBlock
      hdisjoint hl ha hb hcontact
  obtain ⟨x, hsourceX, prefixRoute, hprefix⟩ :=
    exists_reducedResidualPrefixRoute
      hdisjoint hl ha hi hfirst
  obtain ⟨y, htargetY, suffixRoute, hsuffix⟩ :=
    exists_reducedResidualSuffixRoute
      hdisjoint hl hb hj hlast
  exact ⟨i, j, x, y, hi, hfirst, hsourceX, hj, hlast, hij,
    htargetY, prefixRoute, suffixRoute, hprefix, hsuffix⟩

/-- Exact two-sided boundary of the finite mixed-colour window.  The route
enters the designated carrier by a forward edge immediately before the
first designated cancellation, and leaves it by a forward edge immediately
after the last designated cancellation.  The outside endpoints of these
two crossing edges avoid the designated carrier. -/
theorem exists_orderedDesignatedContactWindow
    {G : DWeb V} {P L : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hdisjoint : Disjoint (G.vertexSet P) (G.vertexSet L))
    (hl : IsReducedMarkedRoute G (P ∪ L) a b l)
    (ha : a ∉ G.vertexSet P) (hb : b ∉ G.vertexSet P)
    (hcontact : ¬ Disjoint
      (oneHoleRouteBackwardEdges G (P ∪ L) l) (familyEdges P)) :
    ∃ r i j k : Fin (l.length - 1), ∃ x : V,
      r < i ∧ i ≤ j ∧ j < k ∧
      oneHoleRouteTarget l r = oneHoleRouteSource l i ∧
      oneHoleRouteSource l i = .pending x ∧
      OneHoleChosenForwardStep G (P ∪ L)
        (oneHoleRouteSource l r) (oneHoleRouteTarget l r) ∧
      IsDesignatedBackwardContact G P L l i ∧
      IsDesignatedBackwardContact G P L l j ∧
      oneHoleRouteSource l k = oneHoleRouteTarget l j ∧
      OneHoleChosenForwardStep G (P ∪ L)
        (oneHoleRouteSource l k) (oneHoleRouteTarget l k) ∧
      (oneHoleRouteSource l r).vertex ∉ G.vertexSet P ∧
      (oneHoleRouteTarget l r).vertex ∈ G.vertexSet P ∧
      (oneHoleRouteSource l k).vertex ∈ G.vertexSet P ∧
      (oneHoleRouteTarget l k).vertex ∉ G.vertexSet P := by
  obtain ⟨i, j, k, x, hi, hfirst, hsource, hj, hlast,
      hij, hjk, hsourceK, hforwardK⟩ :=
    exists_orderedDesignatedContactBlock
      hdisjoint hl ha hb hcontact
  obtain ⟨r, hri, htargetR, hforwardR⟩ :=
    exists_predecessorForward_of_source_pending hl hsource
  have hsourceRAvoid :
      (oneHoleRouteSource l r).vertex ∉ G.vertexSet P := by
    exact routeState_avoids_designated_before_first
      hdisjoint hl ha hfirst r.1 (by omega) hri
  have htargetRMem :
      (oneHoleRouteTarget l r).vertex ∈ G.vertexSet P := by
    have hxP := right_mem_vertexSet_of_mem_familyEdges hi.2
    rw [htargetR]
    exact hxP
  have hsourceKMem :
      (oneHoleRouteSource l k).vertex ∈ G.vertexSet P := by
    have hyP := left_mem_vertexSet_of_mem_familyEdges hj.2
    rw [hsourceK]
    exact hyP
  have htargetKAvoid :
      (oneHoleRouteTarget l k).vertex ∉ G.vertexSet P :=
    routeTarget_avoids_designated_after_last
      hdisjoint hl hlast hjk
  exact ⟨r, i, j, k, x, hri, hij, hjk, htargetR, hsource,
    hforwardR, hi, hj, hsourceK, hforwardK, hsourceRAvoid,
    htargetRMem, hsourceKMem, htargetKAvoid⟩

/-- The outer route pieces of the canonical first/last contact block are
residual-coloured, with their designated-carrier boundary states exposed.
This strengthens `exists_orderedDesignatedContactBlock` by adding the exact
facts needed to realize the two outer macros independently of the finite
mixed block. -/
theorem exists_orderedDesignatedContactBlock_with_residual_outerPieces
    {G : DWeb V} {P L : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hdisjoint : Disjoint (G.vertexSet P) (G.vertexSet L))
    (hl : IsReducedMarkedRoute G (P ∪ L) a b l)
    (ha : a ∉ G.vertexSet P) (hb : b ∉ G.vertexSet P)
    (hcontact : ¬ Disjoint
      (oneHoleRouteBackwardEdges G (P ∪ L) l) (familyEdges P)) :
    ∃ i j k : Fin (l.length - 1), ∃ x : V,
      IsDesignatedBackwardContact G P L l i ∧
      (∀ i', i' < i →
        ¬ IsDesignatedBackwardContact G P L l i') ∧
      oneHoleRouteSource l i = .pending x ∧
      IsDesignatedBackwardContact G P L l j ∧
      (∀ j', j < j' →
        ¬ IsDesignatedBackwardContact G P L l j') ∧
      i ≤ j ∧ j < k ∧
      oneHoleRouteSource l k = oneHoleRouteTarget l j ∧
      OneHoleChosenForwardStep G (P ∪ L)
        (oneHoleRouteSource l k) (oneHoleRouteTarget l k) ∧
      (∀ r, r < i →
        OneHoleChosenBackwardStep G (P ∪ L)
            (oneHoleRouteSource l r) (oneHoleRouteTarget l r) →
          ((oneHoleRouteTarget l r).vertex,
            (oneHoleRouteSource l r).vertex) ∈ familyEdges L) ∧
      (∀ r, j < r →
        OneHoleChosenBackwardStep G (P ∪ L)
            (oneHoleRouteSource l r) (oneHoleRouteTarget l r) →
          ((oneHoleRouteTarget l r).vertex,
            (oneHoleRouteSource l r).vertex) ∈ familyEdges L) ∧
      (∀ n (hn : n < l.length), n < i.1 →
        l[n].vertex ∉ G.vertexSet P) ∧
      (∀ r, j < r →
        (oneHoleRouteTarget l r).vertex ∉ G.vertexSet P) := by
  obtain ⟨i, j, k, x, hi, hfirst, hsource, hj, hlast,
      hij, hjk, hsourceK, hforwardK⟩ :=
    exists_orderedDesignatedContactBlock
      hdisjoint hl ha hb hcontact
  refine ⟨i, j, k, x, hi, hfirst, hsource, hj, hlast,
    hij, hjk, hsourceK, hforwardK, ?_, ?_, ?_, ?_⟩
  · intro r hri hr
    exact backwardStep_mem_residual_before_first hfirst hri hr
  · intro r hjr hr
    exact backwardStep_mem_residual_after_last hlast hjr hr
  · exact routeState_avoids_designated_before_first
      hdisjoint hl ha hfirst
  · intro r hjr
    exact routeTarget_avoids_designated_after_last
      hdisjoint hl hlast hjr

#print axioms backwardStep_mem_residual_before_first
#print axioms backwardStep_mem_residual_after_last
#print axioms exists_unique_designatedContactOwner
#print axioms designatedContactOwner_mem_touched
#print axioms routeState_avoids_designated_before_first
#print axioms forwardStep_avoids_designated_before_first
#print axioms routeTarget_avoids_designated_after_last
#print axioms forwardStep_avoids_designated_after_last
#print axioms exists_predecessorForward_of_source_pending
#print axioms exists_reducedResidualPrefixRoute
#print axioms exists_reducedResidualSuffixRoute
#print axioms exists_reducedResidualOuterRoutes
#print axioms exists_orderedDesignatedContactWindow
#print axioms exists_orderedDesignatedContactBlock_with_residual_outerPieces

end SingularMarkedResidualContactBlocks
end CardinalInduction
end Erdos599
