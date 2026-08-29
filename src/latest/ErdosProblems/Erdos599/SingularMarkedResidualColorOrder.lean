/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularMarkedResidualExchange

/-!
# Colour order along a marked residual route

For the combined old family `P ∪ L`, every chosen backward transition has
a unique old colour when the two carriers are disjoint.  More importantly,
if a reduced route uses no backward edge of `P`, then it never even visits
the carrier of `P`.  A forward transition into an old carrier creates a
pending state; the next transition must cancel an incoming old-family edge,
so disjointness forces that contact to have the same colour.

This is the first order-sensitive fact which is lost by the uncoloured
one-point-augmentation endpoint equations.  It permits the no-designated-
contact branch to be realized entirely inside the residual colour.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularMarkedResidualColorOrder

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

/-- Every backward edge of a route against a two-colour union has one of the
two old colours. -/
theorem backwardEdges_subset_designated_union_residual
    (G : DWeb V) (P L : Set G.DPath)
    (l : List (OneHoleResidualState V)) :
    oneHoleRouteBackwardEdges G (P ∪ L) l ⊆
      familyEdges P ∪ familyEdges L := by
  rw [← familyEdges_union]
  exact oneHoleRouteBackwardEdges_subset_familyEdges G (P ∪ L) l

/-- Carrier disjointness makes the two backward colours exclusive. -/
theorem disjoint_familyEdges_of_disjoint_vertexSet
    {G : DWeb V} {P L : Set G.DPath}
    (hdisjoint : Disjoint (G.vertexSet P) (G.vertexSet L)) :
    Disjoint (familyEdges P) (familyEdges L) := by
  rw [Set.disjoint_left]
  intro e heP heL
  exact Set.disjoint_left.1 hdisjoint
    (left_mem_vertexSet_of_mem_familyEdges heP)
    (left_mem_vertexSet_of_mem_familyEdges heL)

private theorem backwardEdge_mem_residual_of_not_mem_designated
    {G : DWeb V} {P L : Set G.DPath}
    {l : List (OneHoleResidualState V)} {e : V × V}
    (he : e ∈ oneHoleRouteBackwardEdges G (P ∪ L) l)
    (heP : e ∉ familyEdges P) : e ∈ familyEdges L := by
  exact (backwardEdges_subset_designated_union_residual G P L l he).resolve_left heP

private theorem target_vertex_avoids_designated
    {G : DWeb V} {P L : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hdisjoint : Disjoint (G.vertexSet P) (G.vertexSet L))
    (hl : IsReducedMarkedRoute G (P ∪ L) a b l)
    (hnoP : Disjoint
      (oneHoleRouteBackwardEdges G (P ∪ L) l) (familyEdges P))
    (i : Fin (l.length - 1)) :
    (oneHoleRouteTarget l i).vertex ∉ G.vertexSet P := by
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
        intro hyP
        obtain ⟨p, hpP, hyp⟩ := hyP
        exact hforward.2.2 ⟨p, Or.inl hpP, hyp⟩
      | pending y =>
        have hiNext : i.1 + 1 < l.length - 1 := by
          by_contra hnot
          have hilast : i.1 + 1 = l.length - 1 := by
            have hi : i.1 < l.length - 1 := i.2
            omega
          have hlast := oneHoleRoute_last hl
          change l[i.1 + 1] = .pending y at ht
          have htLast : l[l.length - 1] = .pending y := by
            simpa only [hilast] using ht
          have hcontra :
              (OneHoleResidualState.ready b : OneHoleResidualState V) =
                .pending y := hlast.symm.trans htLast
          cases hcontra
        let j : Fin (l.length - 1) := ⟨i.1 + 1, hiNext⟩
        have hsourceNext : oneHoleRouteSource l j = .pending y := by
          change l[i.1 + 1] = .pending y
          exact ht
        have hnextStep := oneHoleRoute_step hl.1.2.1 j
        have hnextBackward : OneHoleChosenBackwardStep G (P ∪ L)
            (oneHoleRouteSource l j) (oneHoleRouteTarget l j) := by
          rcases (oneHoleMarkedStep_iff_chosenDirection G (P ∪ L)
              (oneHoleRouteSource l j) (oneHoleRouteTarget l j)).1 hnextStep with
            hnForward | hnBackward
          · cases htNext : oneHoleRouteTarget l j <;>
              simp [OneHoleChosenForwardStep, hsourceNext, htNext] at hnForward
          · exact hnBackward
        have heBackward :
            ((oneHoleRouteTarget l j).vertex, y) ∈
              oneHoleRouteBackwardEdges G (P ∪ L) l := by
          refine ⟨j, hnextBackward, ?_⟩
          simp [hsourceNext]
        have heNotP :
            ((oneHoleRouteTarget l j).vertex, y) ∉ familyEdges P := by
          intro heP
          exact Set.disjoint_left.1 hnoP heBackward heP
        have heL : ((oneHoleRouteTarget l j).vertex, y) ∈ familyEdges L :=
          backwardEdge_mem_residual_of_not_mem_designated heBackward heNotP
        exact fun hyP ↦ Set.disjoint_left.1 hdisjoint hyP
          (right_mem_vertexSet_of_mem_familyEdges heL)
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
    have heL := backwardEdge_mem_residual_of_not_mem_designated
      heBackward heNotP
    exact fun hyP ↦ Set.disjoint_left.1 hdisjoint hyP
      (left_mem_vertexSet_of_mem_familyEdges heL)

/-- If the marked route never cancels a designated-colour edge, then every
state vertex on the route avoids the designated carrier.  In particular,
all contacts and all inserted forward edges belong to the residual exchange
region. -/
theorem route_state_vertices_avoid_designated
    {G : DWeb V} {P L : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hdisjoint : Disjoint (G.vertexSet P) (G.vertexSet L))
    (hl : IsReducedMarkedRoute G (P ∪ L) a b l)
    (ha : a ∉ G.vertexSet P)
    (hnoP : Disjoint
      (oneHoleRouteBackwardEdges G (P ∪ L) l) (familyEdges P)) :
    ∀ n (hn : n < l.length), l[n].vertex ∉ G.vertexSet P := by
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    rw [oneHoleRoute_first hl]
    exact ha
  · have hnPred : n - 1 < l.length - 1 := by omega
    let i : Fin (l.length - 1) := ⟨n - 1, hnPred⟩
    have htarget : oneHoleRouteTarget l i = l[n] := by
      change l[(n - 1) + 1] = l[n]
      congr 1
      omega
    rw [← htarget]
    exact target_vertex_avoids_designated hdisjoint hl hnoP i

/-- Consequently every inserted forward edge of the marked toggle has both
ends outside the designated carrier. -/
theorem forwardEdges_avoid_designated
    {G : DWeb V} {P L : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hdisjoint : Disjoint (G.vertexSet P) (G.vertexSet L))
    (hl : IsReducedMarkedRoute G (P ∪ L) a b l)
    (ha : a ∉ G.vertexSet P)
    (hnoP : Disjoint
      (oneHoleRouteBackwardEdges G (P ∪ L) l) (familyEdges P)) :
    oneHoleRouteForwardEdges G (P ∪ L) l ⊆
      (G.vertexSet P)ᶜ ×ˢ (G.vertexSet P)ᶜ := by
  rintro e ⟨i, hi, rfl⟩
  constructor
  · exact route_state_vertices_avoid_designated hdisjoint hl ha hnoP
      i.1 (by omega)
  · exact route_state_vertices_avoid_designated hdisjoint hl ha hnoP
      (i.1 + 1) (by omega)

/-! ## The first and last designated-colour cancellations -/

/-- A route transition which cancels an old designated-colour edge. -/
def IsDesignatedBackwardContact
    (G : DWeb V) (P L : Set G.DPath)
    (l : List (OneHoleResidualState V))
    (i : Fin (l.length - 1)) : Prop :=
  OneHoleChosenBackwardStep G (P ∪ L)
      (oneHoleRouteSource l i) (oneHoleRouteTarget l i) ∧
    ((oneHoleRouteTarget l i).vertex,
      (oneHoleRouteSource l i).vertex) ∈ familyEdges P

/-- A designated backward contact exists exactly when the route's deleted
old edges meet the designated colour. -/
theorem exists_designatedBackwardContact_iff
    (G : DWeb V) (P L : Set G.DPath)
    (l : List (OneHoleResidualState V)) :
    (∃ i, IsDesignatedBackwardContact G P L l i) ↔
      ¬ Disjoint (oneHoleRouteBackwardEdges G (P ∪ L) l)
        (familyEdges P) := by
  constructor
  · rintro ⟨i, hi⟩ hdisjoint
    exact Set.disjoint_left.1 hdisjoint
      ⟨i, hi.1, rfl⟩ hi.2
  · intro hnot
    obtain ⟨e, heBackward, heP⟩ := Set.not_disjoint_iff.1 hnot
    obtain ⟨i, hi, rfl⟩ := heBackward
    exact ⟨i, hi, heP⟩

/-- The first cancellation of a designated-colour edge, with the exact
order fact needed to cut a marked route into an initial residual-only block
and the first mixed block. -/
theorem exists_first_designatedBackwardContact
    {G : DWeb V} {P L : Set G.DPath}
    {l : List (OneHoleResidualState V)}
    (hexists : ∃ i, IsDesignatedBackwardContact G P L l i) :
    ∃ i, IsDesignatedBackwardContact G P L l i ∧
      ∀ j, j < i → ¬ IsDesignatedBackwardContact G P L l j := by
  classical
  let S : Finset (Fin (l.length - 1)) :=
    Finset.univ.filter (IsDesignatedBackwardContact G P L l)
  have hSne : S.Nonempty := by
    obtain ⟨i, hi⟩ := hexists
    exact ⟨i, by simp [S, hi]⟩
  let i : Fin (l.length - 1) := S.min' hSne
  have hiS : i ∈ S := Finset.min'_mem S hSne
  refine ⟨i, (Finset.mem_filter.1 hiS).2, ?_⟩
  intro j hji hj
  have hjS : j ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ j, hj⟩
  exact (not_lt_of_ge (Finset.min'_le S j hjS)) hji

/-- The last cancellation of a designated-colour edge, with the exact
order fact needed to isolate the final mixed block ending at the original
target. -/
theorem exists_last_designatedBackwardContact
    {G : DWeb V} {P L : Set G.DPath}
    {l : List (OneHoleResidualState V)}
    (hexists : ∃ i, IsDesignatedBackwardContact G P L l i) :
    ∃ i, IsDesignatedBackwardContact G P L l i ∧
      ∀ j, i < j → ¬ IsDesignatedBackwardContact G P L l j := by
  classical
  let S : Finset (Fin (l.length - 1)) :=
    Finset.univ.filter (IsDesignatedBackwardContact G P L l)
  have hSne : S.Nonempty := by
    obtain ⟨i, hi⟩ := hexists
    exact ⟨i, by simp [S, hi]⟩
  let i : Fin (l.length - 1) := S.max' hSne
  have hiS : i ∈ S := Finset.max'_mem S hSne
  refine ⟨i, (Finset.mem_filter.1 hiS).2, ?_⟩
  intro j hij hj
  have hjS : j ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ j, hj⟩
  exact (not_lt_of_ge (Finset.le_max' S j hjS)) hij

/-- At the first designated cancellation the route is in a pending state.
It cannot already be ready on the designated carrier: at position zero this
would contradict freshness of the route source, while at a later position
the preceding transition would either enter the old union by a forward
ready step or would already be an earlier designated cancellation. -/
theorem first_designatedBackwardContact_source_pending
    {G : DWeb V} {P L : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hdisjoint : Disjoint (G.vertexSet P) (G.vertexSet L))
    (hl : IsReducedMarkedRoute G (P ∪ L) a b l)
    (ha : a ∉ G.vertexSet P)
    {i : Fin (l.length - 1)}
    (hi : IsDesignatedBackwardContact G P L l i)
    (hfirst : ∀ j, j < i →
      ¬ IsDesignatedBackwardContact G P L l j) :
    ∃ x, oneHoleRouteSource l i = .pending x := by
  cases hs : oneHoleRouteSource l i with
  | pending x => exact ⟨x, rfl⟩
  | ready x =>
    have hxP : x ∈ G.vertexSet P := by
      exact right_mem_vertexSet_of_mem_familyEdges (hs ▸ hi.2)
    by_cases hi0 : i.1 = 0
    · have hsource0 : oneHoleRouteSource l i = .ready a := by
        change l[i.1] = .ready a
        simpa only [hi0] using oneHoleRoute_first hl
      have hstate :
          (OneHoleResidualState.ready a : OneHoleResidualState V) =
            .ready x := hsource0.symm.trans hs
      have hax : a = x := OneHoleResidualState.ready.inj hstate
      exact False.elim (ha (hax ▸ hxP))
    · have hjBound : i.1 - 1 < l.length - 1 := by omega
      let j : Fin (l.length - 1) := ⟨i.1 - 1, hjBound⟩
      have hji : j < i := by
        dsimp only [j]
        change i.1 - 1 < i.1
        omega
      have htargetPrev : oneHoleRouteTarget l j = .ready x := by
        change l[(i.1 - 1) + 1] = .ready x
        change l[i.1] = .ready x at hs
        have hpred : i.1 - 1 + 1 = i.1 := by omega
        simpa only [hpred] using hs
      have hstep := oneHoleRoute_step hl.1.2.1 j
      rcases (oneHoleMarkedStep_iff_chosenDirection G (P ∪ L)
          (oneHoleRouteSource l j) (oneHoleRouteTarget l j)).1 hstep with
        hforward | hbackward
      · cases hsourcePrev : oneHoleRouteSource l j with
        | pending y =>
          simp [OneHoleChosenForwardStep, hsourcePrev] at hforward
        | ready y =>
          simp only [OneHoleChosenForwardStep, hsourcePrev,
            htargetPrev] at hforward
          obtain ⟨p, hpP, hpx⟩ := hxP
          exact False.elim (hforward.2.2 ⟨p, Or.inl hpP, hpx⟩)
      · have heBackward :
            ((oneHoleRouteTarget l j).vertex,
              (oneHoleRouteSource l j).vertex) ∈
                oneHoleRouteBackwardEdges G (P ∪ L) l :=
          ⟨j, hbackward, rfl⟩
        rcases backwardEdges_subset_designated_union_residual
            G P L l heBackward with heP | heL
        · exact False.elim (hfirst j hji ⟨hbackward, heP⟩)
        · have hxL : x ∈ G.vertexSet L := by
            have hmem := left_mem_vertexSet_of_mem_familyEdges heL
            rw [htargetPrev] at hmem
            exact hmem
          exact False.elim (Set.disjoint_left.1 hdisjoint hxP hxL)

/-- After the last designated cancellation the next route transition exists
and is forward, provided the final route vertex is outside the designated
carrier.  A later backward transition would either have the designated
colour, contradicting lastness, or the residual colour, contradicting the
carrier disjointness at its source. -/
theorem last_designatedBackwardContact_next_forward
    {G : DWeb V} {P L : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hdisjoint : Disjoint (G.vertexSet P) (G.vertexSet L))
    (hl : IsReducedMarkedRoute G (P ∪ L) a b l)
    (hb : b ∉ G.vertexSet P)
    {i : Fin (l.length - 1)}
    (hi : IsDesignatedBackwardContact G P L l i)
    (hlast : ∀ j, i < j →
      ¬ IsDesignatedBackwardContact G P L l j) :
    ∃ j : Fin (l.length - 1), i < j ∧
      oneHoleRouteSource l j = oneHoleRouteTarget l i ∧
      OneHoleChosenForwardStep G (P ∪ L)
        (oneHoleRouteSource l j) (oneHoleRouteTarget l j) := by
  have htargetReady : ∃ x, oneHoleRouteTarget l i = .ready x := by
    cases hs : oneHoleRouteSource l i <;>
      cases ht : oneHoleRouteTarget l i <;>
      simp [IsDesignatedBackwardContact, OneHoleChosenBackwardStep,
        hs, ht] at hi ⊢
  obtain ⟨x, htarget⟩ := htargetReady
  have hxP : x ∈ G.vertexSet P := by
    exact left_mem_vertexSet_of_mem_familyEdges (htarget ▸ hi.2)
  have hiNext : i.1 + 1 < l.length - 1 := by
    by_contra hnot
    have hilast : i.1 + 1 = l.length - 1 := by omega
    have htLast : l[l.length - 1] = .ready x := by
      change l[i.1 + 1] = .ready x at htarget
      simpa only [hilast] using htarget
    have hstate :
        (OneHoleResidualState.ready b : OneHoleResidualState V) =
          .ready x := (oneHoleRoute_last hl).symm.trans htLast
    have hbx : b = x := OneHoleResidualState.ready.inj hstate
    exact hb (hbx ▸ hxP)
  let j : Fin (l.length - 1) := ⟨i.1 + 1, hiNext⟩
  have hij : i < j := by
    change i.1 < i.1 + 1
    omega
  have hsourceNext : oneHoleRouteSource l j = oneHoleRouteTarget l i := by
    change l[i.1 + 1] = l[i.1 + 1]
    rfl
  have hstep := oneHoleRoute_step hl.1.2.1 j
  rcases (oneHoleMarkedStep_iff_chosenDirection G (P ∪ L)
      (oneHoleRouteSource l j) (oneHoleRouteTarget l j)).1 hstep with
    hforward | hbackward
  · exact ⟨j, hij, hsourceNext, hforward⟩
  · have heBackward :
        ((oneHoleRouteTarget l j).vertex,
          (oneHoleRouteSource l j).vertex) ∈
            oneHoleRouteBackwardEdges G (P ∪ L) l :=
      ⟨j, hbackward, rfl⟩
    rcases backwardEdges_subset_designated_union_residual
        G P L l heBackward with heP | heL
    · exact False.elim (hlast j hij ⟨hbackward, heP⟩)
    · have hxL : x ∈ G.vertexSet L := by
        have hmem := right_mem_vertexSet_of_mem_familyEdges heL
        rw [hsourceNext, htarget] at hmem
        exact hmem
      exact False.elim (Set.disjoint_left.1 hdisjoint hxP hxL)

/-- A nonempty designated-colour block has canonical first and last
cancellations.  The first cancellation starts in a pending state, while the
last one is followed by a forward transition towards the fresh route
target.  This packages the finite-order geometry needed by a selective
two-colour switch without choosing arbitrary contact indices. -/
theorem exists_orderedDesignatedContactBlock
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
        (oneHoleRouteSource l k) (oneHoleRouteTarget l k) := by
  have hexists : ∃ i, IsDesignatedBackwardContact G P L l i :=
    (exists_designatedBackwardContact_iff G P L l).2 hcontact
  obtain ⟨i, hi, hfirst⟩ :=
    exists_first_designatedBackwardContact hexists
  obtain ⟨j, hj, hlast⟩ :=
    exists_last_designatedBackwardContact hexists
  obtain ⟨x, hsourcePending⟩ :=
    first_designatedBackwardContact_source_pending
      hdisjoint hl ha hi hfirst
  obtain ⟨k, hjk, hsourceK, hforwardK⟩ :=
    last_designatedBackwardContact_next_forward
      hdisjoint hl hb hj hlast
  have hij : i ≤ j := by
    by_contra hnot
    have hji : j < i := lt_of_not_ge hnot
    exact hfirst j hji hj
  exact ⟨i, j, k, x, hi, hfirst, hsourcePending, hj, hlast,
    hij, hjk, hsourceK, hforwardK⟩

#print axioms backwardEdges_subset_designated_union_residual
#print axioms disjoint_familyEdges_of_disjoint_vertexSet
#print axioms route_state_vertices_avoid_designated
#print axioms forwardEdges_avoid_designated
#print axioms exists_designatedBackwardContact_iff
#print axioms exists_first_designatedBackwardContact
#print axioms exists_last_designatedBackwardContact
#print axioms first_designatedBackwardContact_source_pending
#print axioms last_designatedBackwardContact_next_forward
#print axioms exists_orderedDesignatedContactBlock

end SingularMarkedResidualColorOrder
end CardinalInduction
end Erdos599
