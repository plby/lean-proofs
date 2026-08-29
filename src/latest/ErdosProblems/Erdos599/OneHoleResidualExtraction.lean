/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.OneHoleChain
import ErdosProblems.Erdos599.OneHoleFiniteModification
import ErdosProblems.Erdos599.FiniteEdgeBalance
import ErdosProblems.Erdos599.SafeSwitching
import ErdosProblems.Erdos599.OneHoleReroute

/-!
# Realizing a finite marked one-hole residual route

A marked route acts on the old warp by deleting every family edge traversed
backwards and inserting every unused edge traversed forwards.  The resulting
locally bi-unique relation can split across several new paths, so in general
it is not represented by one compatible alternating trace.  This file proves
the exact invariant statement: the finite symmetric difference has finite
components and the required one-point boundary, hence decomposes into an
honest one-point augmentation.
-/

namespace Erdos599
namespace DWeb

open Set DirectedPath
open Alternating

universe u

variable {V : Type u}

/-- A directed edge, bundled as the corresponding one-edge finite path. -/
private def oneHoleEdgePath {D : Digraph V} {x y : V}
    (hxy : D.Adj x y) (hne : x ≠ y) : FinitePath D where
  start := x
  finish := y
  walk := .cons hxy .nil
  isPath := by
    simp only [Walk.IsPath, Walk.support_cons, Walk.support_nil]
    simp [hne]

@[simp] private theorem oneHoleEdgePath_start {D : Digraph V} {x y : V}
    (hxy : D.Adj x y) (hne : x ≠ y) :
    (oneHoleEdgePath hxy hne).start = x := rfl

@[simp] private theorem oneHoleEdgePath_finish {D : Digraph V} {x y : V}
    (hxy : D.Adj x y) (hne : x ≠ y) :
    (oneHoleEdgePath hxy hne).finish = y := rfl

@[simp] private theorem oneHoleEdgePath_support {D : Digraph V} {x y : V}
    (hxy : D.Adj x y) (hne : x ≠ y) :
    (oneHoleEdgePath hxy hne).support = {x, y} := by
  ext z
  simp [oneHoleEdgePath, FinitePath.support]

@[simp] private theorem oneHoleEdgePath_edgeSet {D : Digraph V} {x y : V}
    (hxy : D.Adj x y) (hne : x ≠ y) :
    (oneHoleEdgePath hxy hne).edgeSet = {(x, y)} := by
  ext e
  simp [oneHoleEdgePath, FinitePath.edgeSet, Walk.edgeSet]

/-- A non-reflexive one-step marked residual chain from an uncovered source
to an uncovered target is a single forward switching link.  This is the
base case used by the finite run-compression induction below. -/
theorem oneHoleResidualExtraction_of_single_ready_step
    (G : DWeb V) {J : Set G.DPath} (hJ : G.IsCleanFiniteWarp J)
    {a b : V} (ha : a ∈ G.source \ G.initialSet J)
    (hb : b ∈ G.target \ G.terminalFrontier J)
    (hne : a ≠ b)
    (hstep : G.OneHoleMarkedStep J (.ready a) (.ready b)) :
    ∃ Q : FiniteTrace G.graph,
      IsSwitchingAlternating J (.finite Q) ∧
        (AltPath.finite Q).initial = a ∧
          (AltPath.finite Q).terminal? = some b := by
  have haOutside : a ∉ G.vertexSet J :=
    fun haJ ↦ Set.disjoint_left.1 hJ.source_gap_disjoint_vertexSet ha haJ
  have hbOutside : b ∉ G.vertexSet J :=
    fun hbJ ↦ Set.disjoint_left.1 hJ.target_gap_disjoint_vertexSet hb hbJ
  rcases hstep with hforward | hbackward
  · rcases hforward with ⟨hab, habOff, _hbOutside⟩
    let q : FinitePath G.graph := oneHoleEdgePath hab hne
    let l : Link G.graph := ⟨q, .forward, hne⟩
    let Q : FiniteTrace G.graph := FiniteTrace.singleton l
    refine ⟨Q, ?_, ?_, ?_⟩
    · refine ⟨⟨hJ.isWarp, ?_, ?_, ?_⟩, ?_, ?_⟩
      · intro k hk hback
        change k ∈ (AltPath.single l).links at hk
        have hkl : k = l := by simpa using hk
        subst k
        simp [l] at hback
      · intro _
        change a ∉ G.vertexSet J
        exact haOutside
      · intro t ht _hlast
        have htb : t = b := by
          change some b = some t at ht
          exact (Option.some.inj ht).symm
        exact htb ▸ hbOutside
      · intro k hk hkforward
        change k ∈ (AltPath.single l).links at hk
        have hkl : k = l := by simpa using hk
        subst k
        rw [Set.disjoint_left]
        intro e heq heJ
        have he : e = (a, b) := by simpa [l, q] using heq
        exact habOff (he ▸ heJ)
      · intro x hx
        rcases hx with ⟨hxForward, hxJ⟩
        have hxq : x ∈ q.support := by
          simp only [AltPath.directionVertices, Set.mem_iUnion] at hxForward
          rcases hxForward with ⟨k, hk, hkdir, hxk⟩
          change k ∈ (AltPath.single l).links at hk
          have hkl : k = l := by simpa using hk
          subst k
          exact hxk
        rw [oneHoleEdgePath_support] at hxq
        rcases hxq with rfl | rfl
        · exact False.elim (haOutside hxJ)
        · exact False.elim (hbOutside hxJ)
    · rfl
    · rfl
  · simp only [familyEdges, Set.mem_iUnion] at hbackward
    rcases hbackward with ⟨p, hpJ, hpedge⟩
    exact False.elim
      (haOutside ⟨p, hpJ, (p.edgeSet_subset_support_prod hpedge).2⟩)

/-! ## Edges toggled by a reduced marked route -/

/-- The state at the source of the `i`th transition of a finite route. -/
def oneHoleRouteSource (l : List (OneHoleResidualState V))
    (i : Fin (l.length - 1)) : OneHoleResidualState V :=
  l[i.1]'(by omega)

/-- The state at the target of the `i`th transition of a finite route. -/
def oneHoleRouteTarget (l : List (OneHoleResidualState V))
    (i : Fin (l.length - 1)) : OneHoleResidualState V :=
  l[i.1 + 1]'(by omega)

theorem oneHoleRoute_step {G : DWeb V} {J : Set G.DPath}
    {l : List (OneHoleResidualState V)}
    (hl : l.IsChain (G.OneHoleMarkedStep J))
    (i : Fin (l.length - 1)) :
    G.OneHoleMarkedStep J (oneHoleRouteSource l i)
      (oneHoleRouteTarget l i) := by
  exact hl.getElem i.1 (by omega)

/-- Ordered list positions expose an explicit prefix/middle/suffix
decomposition. -/
private theorem list_eq_append_getElem_append_getElem
    {α : Type*} (l : List α) {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) (hij : i < j) :
    ∃ pre mid post,
      l = pre ++ l[i] :: mid ++ l[j] :: post := by
  let k := j - i - 1
  refine ⟨l.take i, (l.drop (i + 1)).take k, l.drop (j + 1), ?_⟩
  have hk : k + (i + 1) = j := by
    dsimp [k]
    omega
  have htail : l.drop (i + 1) =
      (l.drop (i + 1)).take k ++ l[j] :: l.drop (j + 1) := by
    calc
      l.drop (i + 1) = (l.drop (i + 1)).take k ++
          (l.drop (i + 1)).drop k :=
        ((l.drop (i + 1)).take_append_drop k).symm
      _ = (l.drop (i + 1)).take k ++ l.drop j := by
        rw [List.drop_drop]
        congr 2
        omega
      _ = (l.drop (i + 1)).take k ++ l[j] :: l.drop (j + 1) := by
        rw [List.drop_eq_getElem_cons hj]
  calc
    l = l.take (i + 1) ++ l.drop (i + 1) :=
      (l.take_append_drop (i + 1)).symm
    _ = (l.take i ++ [l[i]]) ++ l.drop (i + 1) := by
      rw [List.take_concat_get' l i hi]
    _ = l.take i ++ l[i] :: (l.drop (i + 1)) := by simp
    _ = l.take i ++ l[i] ::
        ((l.drop (i + 1)).take k ++ l[j] :: l.drop (j + 1)) := by
      exact congrArg (fun t ↦ l.take i ++ l[i] :: t) htail
    _ = l.take i ++ l[i] :: (l.drop (i + 1)).take k ++
        l[j] :: l.drop (j + 1) := by simp

/-- An earlier position and a later transition expose a decomposition in
which the two states of that transition remain adjacent. -/
private theorem list_eq_append_getElem_append_transition
    {α : Type*} (l : List α) {q i : ℕ}
    (hq : q < l.length) (hi : i + 1 < l.length) (hqi : q < i) :
    ∃ pre mid post,
      l = pre ++ l[q] :: mid ++ l[i] :: l[i + 1] :: post := by
  let k := i - q - 1
  refine ⟨l.take q, (l.drop (q + 1)).take k, l.drop (i + 2), ?_⟩
  have hk : k + (q + 1) = i := by
    dsimp [k]
    omega
  have hit : i < l.length := by omega
  have htail : l.drop (q + 1) =
      (l.drop (q + 1)).take k ++
        l[i] :: l[i + 1] :: l.drop (i + 2) := by
    calc
      l.drop (q + 1) = (l.drop (q + 1)).take k ++
          (l.drop (q + 1)).drop k :=
        ((l.drop (q + 1)).take_append_drop k).symm
      _ = (l.drop (q + 1)).take k ++ l.drop i := by
        rw [List.drop_drop]
        congr 2
        omega
      _ = (l.drop (q + 1)).take k ++ l[i] :: l.drop (i + 1) := by
        rw [List.drop_eq_getElem_cons hit]
      _ = (l.drop (q + 1)).take k ++
          l[i] :: l[i + 1] :: l.drop (i + 2) := by
        rw [List.drop_eq_getElem_cons hi]
  calc
    l = l.take (q + 1) ++ l.drop (q + 1) :=
      (l.take_append_drop (q + 1)).symm
    _ = (l.take q ++ [l[q]]) ++ l.drop (q + 1) := by
      rw [List.take_concat_get' l q hq]
    _ = l.take q ++ l[q] :: l.drop (q + 1) := by simp
    _ = l.take q ++ l[q] ::
        ((l.drop (q + 1)).take k ++
          l[i] :: l[i + 1] :: l.drop (i + 2)) := by
      exact congrArg (fun t ↦ l.take q ++ l[q] :: t) htail
    _ = l.take q ++ l[q] :: (l.drop (q + 1)).take k ++
        l[i] :: l[i + 1] :: l.drop (i + 2) := by simp

theorem oneHoleRouteSource_injective
    {l : List (OneHoleResidualState V)} (hl : l.Nodup) :
    Function.Injective (oneHoleRouteSource l) := by
  intro i j hij
  apply Fin.ext
  apply (hl.getElem_inj_iff).1
  change l[i.1] = l[j.1]
  exact hij

theorem oneHoleRouteTarget_injective
    {l : List (OneHoleResidualState V)} (hl : l.Nodup) :
    Function.Injective (oneHoleRouteTarget l) := by
  intro i j hij
  apply Fin.ext
  have hs : i.1 + 1 = j.1 + 1 := by
    apply (hl.getElem_inj_iff).1
    change l[i.1 + 1] = l[j.1 + 1]
    exact hij
  omega

theorem oneHoleRoute_first
    {G : DWeb V} {J : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hl : IsReducedMarkedRoute G J a b l) :
    l[0]'(List.length_pos_iff.mpr hl.1.1) = .ready a := by
  have hhead := hl.1.2.2.1
  rw [List.head?_eq_some_head hl.1.1] at hhead
  have hh : l.head hl.1.1 = .ready a := Option.some.inj hhead
  rw [List.head_eq_getElem_zero] at hh
  exact hh

theorem oneHoleRoute_last
    {G : DWeb V} {J : Set G.DPath} {a b : V}
    {l : List (OneHoleResidualState V)}
    (hl : IsReducedMarkedRoute G J a b l) :
    l[l.length - 1]'(by
      have hpos : 0 < l.length := List.length_pos_iff.mpr hl.1.1
      omega) = .ready b := by
  have hlast := hl.1.2.2.2
  rw [List.getLast?_eq_some_getLast hl.1.1] at hlast
  have hh : l.getLast hl.1.1 = .ready b := Option.some.inj hlast
  rw [List.getLast_eq_getElem] at hh
  exact hh

/-- The unused ambient edges inserted by the chosen forward transitions of
a finite marked route. -/
def oneHoleRouteForwardEdges (G : DWeb V) (J : Set G.DPath)
    (l : List (OneHoleResidualState V)) : Set (V × V) :=
  {e | ∃ i : Fin (l.length - 1),
    OneHoleChosenForwardStep G J (oneHoleRouteSource l i)
      (oneHoleRouteTarget l i) ∧
    e = ((oneHoleRouteSource l i).vertex,
      (oneHoleRouteTarget l i).vertex)}

/-- The old family edges deleted by the chosen backward transitions of a
finite marked route.  The stored orientation is the old family orientation,
opposite to the route transition. -/
def oneHoleRouteBackwardEdges (G : DWeb V) (J : Set G.DPath)
    (l : List (OneHoleResidualState V)) : Set (V × V) :=
  {e | ∃ i : Fin (l.length - 1),
    OneHoleChosenBackwardStep G J (oneHoleRouteSource l i)
      (oneHoleRouteTarget l i) ∧
    e = ((oneHoleRouteTarget l i).vertex,
      (oneHoleRouteSource l i).vertex)}

/-- The residual symmetric difference encoded by a finite marked route. -/
def oneHoleRouteToggledEdges (G : DWeb V) (J : Set G.DPath)
    (l : List (OneHoleResidualState V)) : Set (V × V) :=
  (familyEdges J \ oneHoleRouteBackwardEdges G J l) ∪
    oneHoleRouteForwardEdges G J l

theorem oneHoleRouteForwardEdges_finite (G : DWeb V)
    (J : Set G.DPath) (l : List (OneHoleResidualState V)) :
    (oneHoleRouteForwardEdges G J l).Finite := by
  let f : Fin (l.length - 1) → V × V := fun i ↦
    ((oneHoleRouteSource l i).vertex, (oneHoleRouteTarget l i).vertex)
  let I : Set (Fin (l.length - 1)) :=
    {i | OneHoleChosenForwardStep G J (oneHoleRouteSource l i)
      (oneHoleRouteTarget l i)}
  have hI : I.Finite := Set.toFinite I
  have heq : oneHoleRouteForwardEdges G J l = f '' I := by
    ext e
    simp only [oneHoleRouteForwardEdges, Set.mem_setOf_eq, Set.mem_image,
      I, f]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
  rw [heq]
  exact hI.image f

theorem oneHoleRouteBackwardEdges_finite (G : DWeb V)
    (J : Set G.DPath) (l : List (OneHoleResidualState V)) :
    (oneHoleRouteBackwardEdges G J l).Finite := by
  let f : Fin (l.length - 1) → V × V := fun i ↦
    ((oneHoleRouteTarget l i).vertex, (oneHoleRouteSource l i).vertex)
  let I : Set (Fin (l.length - 1)) :=
    {i | OneHoleChosenBackwardStep G J (oneHoleRouteSource l i)
      (oneHoleRouteTarget l i)}
  have hI : I.Finite := Set.toFinite I
  have heq : oneHoleRouteBackwardEdges G J l = f '' I := by
    ext e
    simp only [oneHoleRouteBackwardEdges, Set.mem_setOf_eq, Set.mem_image,
      I, f]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
  rw [heq]
  exact hI.image f

theorem oneHoleRouteBackwardEdges_subset_familyEdges
    (G : DWeb V) (J : Set G.DPath)
    (l : List (OneHoleResidualState V)) :
    oneHoleRouteBackwardEdges G J l ⊆ familyEdges J := by
  rintro e ⟨i, hi, rfl⟩
  cases hs : oneHoleRouteSource l i <;>
    cases ht : oneHoleRouteTarget l i <;>
    simp only [OneHoleChosenBackwardStep, hs, ht] at hi ⊢
  · exact hi.2
  · exact hi

theorem oneHoleRouteForwardEdges_disjoint_familyEdges
    (G : DWeb V) (J : Set G.DPath)
    (l : List (OneHoleResidualState V)) :
    Disjoint (oneHoleRouteForwardEdges G J l) (familyEdges J) := by
  rw [Set.disjoint_left]
  rintro e ⟨i, hi, rfl⟩ heJ
  cases hs : oneHoleRouteSource l i <;>
    cases ht : oneHoleRouteTarget l i <;>
    simp only [OneHoleChosenForwardStep, hs, ht,
      OneHoleResidualState.vertex_ready,
      OneHoleResidualState.vertex_pending] at hi heJ ⊢
  · exact hi.2.1 heJ
  · exact hi.2.1 heJ

/-- Chosen forward route edges are bi-unique.  State simplicity controls
equal ready sources, while the ready/pending target mark distinguishes
vertices outside and inside the old warp. -/
theorem oneHoleRouteForwardEdges_biUnique
    {G : DWeb V} {J : Set G.DPath}
    {a b : V} {l : List (OneHoleResidualState V)}
    (hl : IsReducedMarkedRoute G J a b l) :
    Relator.BiUnique
      (fun x y ↦ (x, y) ∈ oneHoleRouteForwardEdges G J l) := by
  constructor
  · intro z x y hxz hyz
    rcases hxz with ⟨i, hi, hei⟩
    rcases hyz with ⟨j, hj, hej⟩
    have hz_i := congrArg Prod.snd hei
    have hz_j := congrArg Prod.snd hej
    cases hsi : oneHoleRouteSource l i <;>
      simp only [OneHoleChosenForwardStep, hsi] at hi
    cases hsj : oneHoleRouteSource l j <;>
      simp only [OneHoleChosenForwardStep, hsj] at hj
    cases hti : oneHoleRouteTarget l i with
    | ready vi =>
        simp only [OneHoleChosenForwardStep, hti] at hi
        cases htj : oneHoleRouteTarget l j with
        | ready vj =>
            simp only [OneHoleChosenForwardStep, htj] at hj
            have hv : vi = vj := by simpa [hti, htj] using hz_i.symm.trans hz_j
            have hij : i = j := oneHoleRouteTarget_injective hl.2.1 (by
              rw [hti, htj, hv])
            subst j
            exact (Prod.mk.inj (hei.trans hej.symm)).1
        | pending vj =>
            simp only [OneHoleChosenForwardStep, htj] at hj
            have hv : vi = vj := by simpa [hti, htj] using hz_i.symm.trans hz_j
            have hiOutside : vi ∉ G.vertexSet J := by
              simpa [hti] using hi.2.2
            have hjInside : vj ∈ G.vertexSet J := by
              simpa [htj] using hj.2.2
            exact False.elim (hiOutside (hv ▸ hjInside))
    | pending vi =>
        simp only [OneHoleChosenForwardStep, hti] at hi
        cases htj : oneHoleRouteTarget l j with
        | ready vj =>
            simp only [OneHoleChosenForwardStep, htj] at hj
            have hv : vi = vj := by simpa [hti, htj] using hz_i.symm.trans hz_j
            have hiInside : vi ∈ G.vertexSet J := by
              simpa [hti] using hi.2.2
            have hjOutside : vj ∉ G.vertexSet J := by
              simpa [htj] using hj.2.2
            exact False.elim (hjOutside (hv.symm ▸ hiInside))
        | pending vj =>
            simp only [OneHoleChosenForwardStep, htj] at hj
            have hv : vi = vj := by simpa [hti, htj] using hz_i.symm.trans hz_j
            have hij : i = j := oneHoleRouteTarget_injective hl.2.1 (by
              rw [hti, htj, hv])
            subst j
            exact (Prod.mk.inj (hei.trans hej.symm)).1
  · intro x y z hxy hxz
    rcases hxy with ⟨i, hi, hei⟩
    rcases hxz with ⟨j, hj, hej⟩
    have hx_i := congrArg Prod.fst hei
    have hx_j := congrArg Prod.fst hej
    cases hsi : oneHoleRouteSource l i with
    | pending vi => simp only [OneHoleChosenForwardStep, hsi] at hi
    | ready vi =>
      cases hsj : oneHoleRouteSource l j with
      | pending vj => simp only [OneHoleChosenForwardStep, hsj] at hj
      | ready vj =>
        have hv : vi = vj := by simpa [hsi, hsj] using hx_i.symm.trans hx_j
        have hij : i = j := oneHoleRouteSource_injective hl.2.1 (by
          rw [hsi, hsj, hv])
        subst j
        exact (Prod.mk.inj (hei.trans hej.symm)).2

/-- Chosen backward route edges are bi-unique.  The only mixed-source case
would be a backward departure from the ready copy of a vertex that occurred
pending earlier; reduced-route normalization forces that departure forward. -/
theorem oneHoleRouteBackwardEdges_biUnique
    {G : DWeb V} {J : Set G.DPath}
    {a b : V} {l : List (OneHoleResidualState V)}
    (hJ : G.IsCleanFiniteWarp J)
    (hl : IsReducedMarkedRoute G J a b l) :
    Relator.BiUnique
      (fun x y ↦ (x, y) ∈ oneHoleRouteBackwardEdges G J l) := by
  constructor
  · intro z x y hxz hyz
    rcases hxz with ⟨i, hi, hei⟩
    rcases hyz with ⟨j, hj, hej⟩
    have hz_i := congrArg Prod.snd hei
    have hz_j := congrArg Prod.snd hej
    cases hsi : oneHoleRouteSource l i with
    | ready vi =>
      cases hsj : oneHoleRouteSource l j with
      | ready vj =>
        have hv : vi = vj := by simpa [hsi, hsj] using hz_i.symm.trans hz_j
        have hij : i = j := oneHoleRouteSource_injective hl.2.1 (by
          rw [hsi, hsj, hv])
        subst j
        exact (Prod.mk.inj (hei.trans hej.symm)).1
      | pending vj =>
        have hv : vi = vj := by simpa [hsi, hsj] using hz_i.symm.trans hz_j
        subst vj
        cases hti : oneHoleRouteTarget l i with
        | pending yi => simp only [OneHoleChosenBackwardStep, hti] at hi
        | ready yi =>
          simp only [OneHoleChosenBackwardStep, hsi, hti] at hi
          cases htj : oneHoleRouteTarget l j with
          | pending yj => simp only [OneHoleChosenBackwardStep, htj] at hj
          | ready yj =>
            simp only [OneHoleChosenBackwardStep, hsj, htj] at hj
            have hy : yi = yj :=
              familyEdges_in_unique hJ.isWarp hi.2 hj
            have hij : i = j := oneHoleRouteTarget_injective hl.2.1 (by
              rw [hti, htj, hy])
            subst j
            simp [hsi] at hsj
    | pending vi =>
      cases hsj : oneHoleRouteSource l j with
      | pending vj =>
        have hv : vi = vj := by simpa [hsi, hsj] using hz_i.symm.trans hz_j
        have hij : i = j := oneHoleRouteSource_injective hl.2.1 (by
          rw [hsi, hsj, hv])
        subst j
        exact (Prod.mk.inj (hei.trans hej.symm)).1
      | ready vj =>
        have hv : vi = vj := by simpa [hsi, hsj] using hz_i.symm.trans hz_j
        subst vj
        cases hti : oneHoleRouteTarget l i with
        | pending yi => simp only [OneHoleChosenBackwardStep, hti] at hi
        | ready yi =>
          simp only [OneHoleChosenBackwardStep, hsi, hti] at hi
          cases htj : oneHoleRouteTarget l j with
          | pending yj => simp only [OneHoleChosenBackwardStep, htj] at hj
          | ready yj =>
            simp only [OneHoleChosenBackwardStep, hsj, htj] at hj
            have hy : yi = yj :=
              familyEdges_in_unique hJ.isWarp hi hj.2
            have hij : i = j := oneHoleRouteTarget_injective hl.2.1 (by
              rw [hti, htj, hy])
            subst j
            simp [hsi] at hsj
  · intro x y z hxy hxz
    rcases hxy with ⟨i, hi, hei⟩
    rcases hxz with ⟨j, hj, hej⟩
    have hx_i := congrArg Prod.fst hei
    have hx_j := congrArg Prod.fst hej
    cases hti : oneHoleRouteTarget l i with
    | pending vi => simp only [OneHoleChosenBackwardStep, hti] at hi
    | ready vi =>
      cases htj : oneHoleRouteTarget l j with
      | pending vj => simp only [OneHoleChosenBackwardStep, htj] at hj
      | ready vj =>
        have hv : vi = vj := by simpa [hti, htj] using hx_i.symm.trans hx_j
        have hij : i = j := oneHoleRouteTarget_injective hl.2.1 (by
          rw [hti, htj, hv])
        subst j
        exact (Prod.mk.inj (hei.trans hej.symm)).2

private theorem left_mem_vertexSet_of_mem_familyEdges
    {G : DWeb V} {J : Set G.DPath} {x y : V}
    (hxy : (x, y) ∈ familyEdges J) : x ∈ G.vertexSet J := by
  simp only [familyEdges, Set.mem_iUnion] at hxy
  rcases hxy with ⟨p, hpJ, hp⟩
  exact ⟨p, hpJ, (p.edgeSet_subset_support_prod hp).1⟩

private theorem right_mem_vertexSet_of_mem_familyEdges
    {G : DWeb V} {J : Set G.DPath} {x y : V}
    (hxy : (x, y) ∈ familyEdges J) : y ∈ G.vertexSet J := by
  simp only [familyEdges, Set.mem_iUnion] at hxy
  rcases hxy with ⟨p, hpJ, hp⟩
  exact ⟨p, hpJ, (p.edgeSet_subset_support_prod hp).2⟩

/-- Whenever a route inserts an edge out of `x`, the old outgoing family
edge at `x`, if present, is exactly the edge deleted by the preceding route
transition. -/
theorem familyOutgoing_mem_oneHoleRouteBackwardEdges_of_forward
    {G : DWeb V} {J : Set G.DPath}
    {a b x y z : V} {l : List (OneHoleResidualState V)}
    (hJ : G.IsCleanFiniteWarp J)
    (ha : a ∈ G.source \ G.initialSet J)
    (hl : IsReducedMarkedRoute G J a b l)
    (hforward : (x, z) ∈ oneHoleRouteForwardEdges G J l)
    (hxy : (x, y) ∈ familyEdges J) :
    (x, y) ∈ oneHoleRouteBackwardEdges G J l := by
  rcases hforward with ⟨i, hi, hei⟩
  have hx_i := congrArg Prod.fst hei
  cases hsi : oneHoleRouteSource l i with
  | pending xi => simp only [OneHoleChosenForwardStep, hsi] at hi
  | ready xi =>
    have hxxi : x = xi := by simpa [hsi] using hx_i
    subst xi
    by_cases hi0 : i.1 = 0
    · have hfirst := oneHoleRoute_first hl
      have hs0 : oneHoleRouteSource l i = .ready a := by
        change l[i.1] = .ready a
        simpa [hi0] using hfirst
      have hxa : x = a := by simpa [hsi] using hsi.symm.trans hs0
      subst x
      exact False.elim
        (Set.disjoint_left.1 hJ.source_gap_disjoint_vertexSet ha
          (left_mem_vertexSet_of_mem_familyEdges hxy))
    · let k : Fin (l.length - 1) := ⟨i.1 - 1, by omega⟩
      have hjoin : oneHoleRouteTarget l k = oneHoleRouteSource l i := by
        change l[k.1 + 1] = l[i.1]
        congr 1
        dsimp [k]
        omega
      have htx : oneHoleRouteTarget l k = .ready x := by
        rw [hjoin, hsi]
      have hstep := oneHoleRoute_step hl.1.2.1 k
      rcases (oneHoleMarkedStep_iff_chosenDirection G J _ _).1 hstep with
        hkforward | hkbackward
      · cases hsk : oneHoleRouteSource l k <;>
          simp only [OneHoleChosenForwardStep, hsk, htx] at hkforward
        have hxOutside : x ∉ G.vertexSet J := by
          exact hkforward.2.2
        exact False.elim
          (hxOutside (left_mem_vertexSet_of_mem_familyEdges hxy))
      · have hkMem :
            ((oneHoleRouteTarget l k).vertex,
              (oneHoleRouteSource l k).vertex) ∈
              oneHoleRouteBackwardEdges G J l :=
          ⟨k, hkbackward, rfl⟩
        have hkOld :=
          oneHoleRouteBackwardEdges_subset_familyEdges G J l hkMem
        have htarget : (oneHoleRouteTarget l k).vertex = x := by
          rw [hjoin, hsi]
          rfl
        have hy : y = (oneHoleRouteSource l k).vertex :=
          familyEdges_out_unique hJ.isWarp hxy (by simpa [htarget] using hkOld)
        simpa [htarget, hy] using hkMem

/-- Whenever a route inserts an edge into `x`, the old incoming family edge
at `x`, if present, is exactly the edge deleted by the mandatory transition
following the contact at `x`. -/
theorem familyIncoming_mem_oneHoleRouteBackwardEdges_of_forward
    {G : DWeb V} {J : Set G.DPath}
    {a b x y z : V} {l : List (OneHoleResidualState V)}
    (hJ : G.IsCleanFiniteWarp J)
    (hl : IsReducedMarkedRoute G J a b l)
    (hforward : (z, x) ∈ oneHoleRouteForwardEdges G J l)
    (hyx : (y, x) ∈ familyEdges J) :
    (y, x) ∈ oneHoleRouteBackwardEdges G J l := by
  rcases hforward with ⟨i, hi, hei⟩
  have hx_i := congrArg Prod.snd hei
  cases hti : oneHoleRouteTarget l i with
  | ready xi =>
    have hxxi : x = xi := by simpa [hti] using hx_i
    subst xi
    cases hsi : oneHoleRouteSource l i <;>
      simp only [OneHoleChosenForwardStep, hsi, hti] at hi
    exact False.elim
      (hi.2.2 (right_mem_vertexSet_of_mem_familyEdges hyx))
  | pending xi =>
    have hxxi : x = xi := by simpa [hti] using hx_i
    subst xi
    have hnext : i.1 + 2 < l.length := by
      by_contra hn
      have hiLt := i.isLt
      have hlen : 0 < l.length := List.length_pos_iff.mpr hl.1.1
      have hiLast : i.1 + 1 = l.length - 1 := by omega
      have hlastTarget : oneHoleRouteTarget l i = .ready b := by
        change l[i.1 + 1] = .ready b
        calc
          l[i.1 + 1] = l[l.length - 1] := by congr 1
          _ = .ready b := oneHoleRoute_last hl
      have hbad : (OneHoleResidualState.pending x : OneHoleResidualState V) =
          .ready b := hti.symm.trans hlastTarget
      cases hbad
    let k : Fin (l.length - 1) := ⟨i.1 + 1, by omega⟩
    have hjoin : oneHoleRouteSource l k = oneHoleRouteTarget l i := by
      change l[k.1] = l[i.1 + 1]
      congr 1
    have hsx : oneHoleRouteSource l k = .pending x := by
      rw [hjoin, hti]
    have hstep := oneHoleRoute_step hl.1.2.1 k
    cases htk : oneHoleRouteTarget l k with
    | pending u =>
        simp only [OneHoleMarkedStep, hsx, htk] at hstep
    | ready u =>
        have hux : (u, x) ∈ familyEdges J := by
          simpa only [OneHoleMarkedStep, hsx, htk] using hstep
        have hkbackward : OneHoleChosenBackwardStep G J
            (oneHoleRouteSource l k) (oneHoleRouteTarget l k) := by
          simpa only [OneHoleChosenBackwardStep, hsx, htk] using hux
        have hkMem :
            ((oneHoleRouteTarget l k).vertex,
              (oneHoleRouteSource l k).vertex) ∈
              oneHoleRouteBackwardEdges G J l :=
          ⟨k, hkbackward, rfl⟩
        have hyu : y = u :=
          familyEdges_in_unique hJ.isWarp hyx hux
        simpa [hsx, htk, hyu] using hkMem

/-- The complete route toggle is locally bi-unique. -/
theorem oneHoleRouteToggledEdges_biUnique
    {G : DWeb V} {J : Set G.DPath}
    {a b : V} {l : List (OneHoleResidualState V)}
    (hJ : G.IsCleanFiniteWarp J)
    (ha : a ∈ G.source \ G.initialSet J)
    (hl : IsReducedMarkedRoute G J a b l) :
    Relator.BiUnique
      (fun x y ↦ (x, y) ∈ oneHoleRouteToggledEdges G J l) := by
  have hF := oneHoleRouteForwardEdges_biUnique hl
  have hB := oneHoleRouteBackwardEdges_biUnique hJ hl
  constructor
  · intro z x y hxz hyz
    rcases hxz with hxz | hxz <;> rcases hyz with hyz | hyz
    · exact familyEdges_in_unique hJ.isWarp hxz.1 hyz.1
    · exact False.elim (hxz.2
        (familyIncoming_mem_oneHoleRouteBackwardEdges_of_forward
          hJ hl hyz hxz.1))
    · exact False.elim (hyz.2
        (familyIncoming_mem_oneHoleRouteBackwardEdges_of_forward
          hJ hl hxz hyz.1))
    · exact hF.1 hxz hyz
  · intro x y z hxy hxz
    rcases hxy with hxy | hxy <;> rcases hxz with hxz | hxz
    · exact familyEdges_out_unique hJ.isWarp hxy.1 hxz.1
    · exact False.elim (hxy.2
        (familyOutgoing_mem_oneHoleRouteBackwardEdges_of_forward
          hJ ha hl hxz hxy.1))
    · exact False.elim (hxz.2
        (familyOutgoing_mem_oneHoleRouteBackwardEdges_of_forward
          hJ ha hl hxy hxz.1))
    · exact hF.2 hxy hxz

theorem oneHoleRouteForwardEdge_left_ne_isolated
    {G : DWeb V} {J : Set G.DPath}
    {a b v : V} {l : List (OneHoleResidualState V)}
    (hJ : G.IsCleanFiniteWarp J)
    (ha : a ∈ G.source \ G.initialSet J)
    (hl : IsReducedMarkedRoute G J a b l)
    {e : V × V} (he : e ∈ oneHoleRouteForwardEdges G J l)
    (hv : v ∈ isolatedVertices J) : e.1 ≠ v := by
  intro hev
  rcases he with ⟨i, hi, hei⟩
  have hsourceV : (oneHoleRouteSource l i).vertex = v := by
    have := congrArg Prod.fst hei
    simpa [hev] using this.symm
  cases hsi : oneHoleRouteSource l i with
  | pending x => simp only [OneHoleChosenForwardStep, hsi] at hi
  | ready x =>
    have hxv : x = v := by simpa [hsi] using hsourceV
    subst x
    by_cases hi0 : i.1 = 0
    · have hs0 : oneHoleRouteSource l i = .ready a := by
        change l[i.1] = .ready a
        simpa [hi0] using oneHoleRoute_first hl
      have hva : v = a := by simpa [hsi] using hsi.symm.trans hs0
      exact Set.disjoint_left.1 hJ.source_gap_disjoint_vertexSet ha
        (isolatedVertices_subset_vertexSet J (hva ▸ hv))
    · let k : Fin (l.length - 1) := ⟨i.1 - 1, by omega⟩
      have hjoin : oneHoleRouteTarget l k = oneHoleRouteSource l i := by
        change l[k.1 + 1] = l[i.1]
        congr 1
        dsimp [k]
        omega
      have htv : oneHoleRouteTarget l k = .ready v := by rw [hjoin, hsi]
      have hstep := oneHoleRoute_step hl.1.2.1 k
      rcases (oneHoleMarkedStep_iff_chosenDirection G J _ _).1 hstep with
        hkforward | hkbackward
      · cases hsk : oneHoleRouteSource l k <;>
          simp only [OneHoleChosenForwardStep, hsk, htv] at hkforward
        exact hkforward.2.2 (isolatedVertices_subset_vertexSet J hv)
      · have hkMem :
            ((oneHoleRouteTarget l k).vertex,
              (oneHoleRouteSource l k).vertex) ∈
              oneHoleRouteBackwardEdges G J l :=
          ⟨k, hkbackward, rfl⟩
        have hkOld :=
          oneHoleRouteBackwardEdges_subset_familyEdges G J l hkMem
        exact (Alternating.IsWarp.familyEdge_not_incident_isolated
          hJ.isWarp hv hkOld).1
          (by simpa [htv])

theorem oneHoleRouteForwardEdge_right_ne_isolated
    {G : DWeb V} {J : Set G.DPath}
    {a b v : V} {l : List (OneHoleResidualState V)}
    (hJ : G.IsCleanFiniteWarp J)
    (hl : IsReducedMarkedRoute G J a b l)
    {e : V × V} (he : e ∈ oneHoleRouteForwardEdges G J l)
    (hv : v ∈ isolatedVertices J) : e.2 ≠ v := by
  intro hev
  rcases he with ⟨i, hi, hei⟩
  have htargetV : (oneHoleRouteTarget l i).vertex = v := by
    have := congrArg Prod.snd hei
    simpa [hev] using this.symm
  cases hti : oneHoleRouteTarget l i with
  | ready x =>
    have hxv : x = v := by simpa [hti] using htargetV
    subst x
    cases hsi : oneHoleRouteSource l i <;>
      simp only [OneHoleChosenForwardStep, hsi, hti] at hi
    exact hi.2.2 (isolatedVertices_subset_vertexSet J hv)
  | pending x =>
    have hxv : x = v := by simpa [hti] using htargetV
    subst x
    have hnext : i.1 + 2 < l.length := by
      by_contra hn
      have hiLt := i.isLt
      have hlen : 0 < l.length := List.length_pos_iff.mpr hl.1.1
      have hiLast : i.1 + 1 = l.length - 1 := by omega
      have hlastTarget : oneHoleRouteTarget l i = .ready b := by
        change l[i.1 + 1] = .ready b
        calc
          l[i.1 + 1] = l[l.length - 1] := by congr 1
          _ = .ready b := oneHoleRoute_last hl
      have hbad : (OneHoleResidualState.pending v : OneHoleResidualState V) =
          .ready b := hti.symm.trans hlastTarget
      cases hbad
    let k : Fin (l.length - 1) := ⟨i.1 + 1, by omega⟩
    have hjoin : oneHoleRouteSource l k = oneHoleRouteTarget l i := by
      change l[k.1] = l[i.1 + 1]
      congr 1
    have hsv : oneHoleRouteSource l k = .pending v := by rw [hjoin, hti]
    have hstep := oneHoleRoute_step hl.1.2.1 k
    cases htk : oneHoleRouteTarget l k with
    | pending u => simp only [OneHoleMarkedStep, hsv, htk] at hstep
    | ready u =>
      have huv : (u, v) ∈ familyEdges J := by
        simpa only [OneHoleMarkedStep, hsv, htk] using hstep
      exact (Alternating.IsWarp.familyEdge_not_incident_isolated
        hJ.isWarp hv huv).2 rfl

theorem oneHoleRouteToggledEdges_old_isolated_not_incident
    {G : DWeb V} {J : Set G.DPath}
    {a b : V} {l : List (OneHoleResidualState V)}
    (hJ : G.IsCleanFiniteWarp J)
    (ha : a ∈ G.source \ G.initialSet J)
    (hl : IsReducedMarkedRoute G J a b l) :
    ∀ x ∈ isolatedVertices J, ∀ y,
      (x, y) ∉ oneHoleRouteToggledEdges G J l ∧
        (y, x) ∉ oneHoleRouteToggledEdges G J l := by
  intro x hx y
  constructor
  · rintro (hOld | hForward)
    · exact (Alternating.IsWarp.familyEdge_not_incident_isolated
        hJ.isWarp hx hOld.1).1 rfl
    · exact oneHoleRouteForwardEdge_left_ne_isolated hJ ha hl hForward hx rfl
  · rintro (hOld | hForward)
    · exact (Alternating.IsWarp.familyEdge_not_incident_isolated
        hJ.isWarp hx hOld.1).2 rfl
    · exact oneHoleRouteForwardEdge_right_ne_isolated hJ hl hForward hx rfl

def OneHoleRouteForwardIndex (G : DWeb V) (J : Set G.DPath)
    (l : List (OneHoleResidualState V)) :=
  {i : Fin (l.length - 1) //
    OneHoleChosenForwardStep G J (oneHoleRouteSource l i)
      (oneHoleRouteTarget l i)}

def OneHoleRouteBackwardIndex (G : DWeb V) (J : Set G.DPath)
    (l : List (OneHoleResidualState V)) :=
  {i : Fin (l.length - 1) //
    ¬ OneHoleChosenForwardStep G J (oneHoleRouteSource l i)
      (oneHoleRouteTarget l i)}

def oneHoleRouteForwardEdge (G : DWeb V) (J : Set G.DPath)
    (l : List (OneHoleResidualState V))
    (i : OneHoleRouteForwardIndex G J l) : V × V :=
  ((oneHoleRouteSource l i.1).vertex, (oneHoleRouteTarget l i.1).vertex)

def oneHoleRouteBackwardEdge (G : DWeb V) (J : Set G.DPath)
    (l : List (OneHoleResidualState V))
    (i : OneHoleRouteBackwardIndex G J l) : V × V :=
  ((oneHoleRouteTarget l i.1).vertex, (oneHoleRouteSource l i.1).vertex)

theorem oneHoleRouteForwardEdges_eq_range
    (G : DWeb V) (J : Set G.DPath)
    (l : List (OneHoleResidualState V)) :
    oneHoleRouteForwardEdges G J l =
      Set.range (oneHoleRouteForwardEdge G J l) := by
  ext e
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.1, i.2, rfl⟩

theorem oneHoleRouteBackwardEdges_eq_range
    {G : DWeb V} {J : Set G.DPath}
    {a b : V} {l : List (OneHoleResidualState V)}
    (hl : IsReducedMarkedRoute G J a b l) :
    oneHoleRouteBackwardEdges G J l =
      Set.range (oneHoleRouteBackwardEdge G J l) := by
  ext e
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hnot : ¬ OneHoleChosenForwardStep G J
        (oneHoleRouteSource l i) (oneHoleRouteTarget l i) :=
      fun hf ↦ oneHoleChosenDirection_exclusive G J hf hi
    exact ⟨⟨i, hnot⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    have hstep := oneHoleRoute_step hl.1.2.1 i.1
    rcases (oneHoleMarkedStep_iff_chosenDirection G J _ _).1 hstep with
      hf | hb
    · exact False.elim (i.2 hf)
    · exact ⟨i.1, hb, rfl⟩

theorem oneHoleRouteForwardEdge_injective
    {G : DWeb V} {J : Set G.DPath}
    {a b : V} {l : List (OneHoleResidualState V)}
    (hl : IsReducedMarkedRoute G J a b l) :
    Function.Injective (oneHoleRouteForwardEdge G J l) := by
  intro i j hij
  apply Subtype.ext
  apply oneHoleRouteSource_injective hl.2.1
  have hfst := congrArg Prod.fst hij
  cases hsi : oneHoleRouteSource l i.1 with
  | pending x =>
      have hi := i.2
      simp only [OneHoleChosenForwardStep, hsi] at hi
  | ready x =>
    cases hsj : oneHoleRouteSource l j.1 with
    | pending y =>
        have hj := j.2
        simp only [OneHoleChosenForwardStep, hsj] at hj
    | ready y =>
      have hxy : x = y := by
        simpa [oneHoleRouteForwardEdge, hsi, hsj] using hfst
      exact congrArg OneHoleResidualState.ready hxy

theorem oneHoleRouteBackwardEdge_injective
    {G : DWeb V} {J : Set G.DPath}
    {a b : V} {l : List (OneHoleResidualState V)}
    (hl : IsReducedMarkedRoute G J a b l) :
    Function.Injective (oneHoleRouteBackwardEdge G J l) := by
  intro i j hij
  have hbi : OneHoleChosenBackwardStep G J
      (oneHoleRouteSource l i.1) (oneHoleRouteTarget l i.1) := by
    have hstep := oneHoleRoute_step hl.1.2.1 i.1
    rcases (oneHoleMarkedStep_iff_chosenDirection G J _ _).1 hstep with
      hf | hb
    · exact False.elim (i.2 hf)
    · exact hb
  have hbj : OneHoleChosenBackwardStep G J
      (oneHoleRouteSource l j.1) (oneHoleRouteTarget l j.1) := by
    have hstep := oneHoleRoute_step hl.1.2.1 j.1
    rcases (oneHoleMarkedStep_iff_chosenDirection G J _ _).1 hstep with
      hf | hb
    · exact False.elim (j.2 hf)
    · exact hb
  apply Subtype.ext
  apply oneHoleRouteTarget_injective hl.2.1
  have hfst := congrArg Prod.fst hij
  cases hti : oneHoleRouteTarget l i.1 with
  | pending x => simp only [OneHoleChosenBackwardStep, hti] at hbi
  | ready x =>
    cases htj : oneHoleRouteTarget l j.1 with
    | pending y => simp only [OneHoleChosenBackwardStep, htj] at hbj
    | ready y =>
      have hxy : x = y := by
        simpa [oneHoleRouteBackwardEdge, hti, htj] using hfst
      exact congrArg OneHoleResidualState.ready hxy

theorem oneHoleRouteToggledEdges_subset_adj
    (G : DWeb V) (J : Set G.DPath)
    (l : List (OneHoleResidualState V)) :
    oneHoleRouteToggledEdges G J l ⊆
      {e | G.graph.Adj e.1 e.2} := by
  rintro e (heOld | heForward)
  · exact familyEdges_subset_adj J heOld.1
  · rcases heForward with ⟨i, hi, rfl⟩
    cases hs : oneHoleRouteSource l i <;>
      cases ht : oneHoleRouteTarget l i <;>
      simp only [OneHoleChosenForwardStep, hs, ht,
        OneHoleResidualState.vertex_ready,
        OneHoleResidualState.vertex_pending] at hi ⊢
    · exact hi.1
    · exact hi.1

/-! ## The relation-theoretic assembly seam

The residual route itself is used only to certify a finite-component,
locally bi-unique edge relation with the displayed boundary delta.  The
following structure records exactly those obligations.  Keeping this seam
independent of a particular list encoding makes the component decomposition
and endpoint calculation reusable.
-/

/-- Data certified by toggling the old warp along a finite marked route from
`a` to `b`.  Cyclic components are allowed: the generic cyclowarp
decomposition discards them without changing the oriented boundary. -/
structure OneHoleToggleCertificate (G : DWeb V) (J : Set G.DPath)
    (a b : V) where
  edges : Set (V × V)
  edges_in_graph : edges ⊆ {e | G.graph.Adj e.1 e.2}
  outgoing_unique : ∀ {x y z}, (x, y) ∈ edges → (x, z) ∈ edges → y = z
  incoming_unique : ∀ {x y z}, (x, z) ∈ edges → (y, z) ∈ edges → x = y
  finite_components : ∀ c : RelationComponents.Component edges,
    (RelationComponents.componentSupport edges c).Finite
  old_isolated_not_incident : ∀ x ∈ isolatedVertices J, ∀ y,
    (x, y) ∉ edges ∧ (y, x) ∉ edges
  balance_delta : ∀ x,
    edgeBalance edges x = edgeBalance (familyEdges J) x +
      propInt (x = a) - propInt (x = b)

/-- Exact arithmetic statement for the symmetric difference encoded by a
reduced marked route. -/
def OneHoleRouteBalanceLaw (V : Type u) : Prop :=
  ∀ (G : DWeb V) (J : Set G.DPath) (a b : V)
    (l : List (OneHoleResidualState V)),
    G.IsCleanFiniteWarp J →
    a ∈ G.source \ G.initialSet J →
    IsReducedMarkedRoute G J a b l →
    ∀ x,
      edgeBalance (oneHoleRouteToggledEdges G J l) x =
        edgeBalance (familyEdges J) x + propInt (x = a) - propInt (x = b)

/-- All structural fields of the route toggle certificate, with the
finite-sum balance calculation supplied explicitly. -/
noncomputable def oneHoleToggleCertificateOfReducedRoute
    {G : DWeb V} {J : Set G.DPath}
    {a b : V} {l : List (OneHoleResidualState V)}
    (hJ : G.IsCleanFiniteWarp J)
    (ha : a ∈ G.source \ G.initialSet J)
    (hl : IsReducedMarkedRoute G J a b l)
    (hbalance : ∀ x,
      edgeBalance (oneHoleRouteToggledEdges G J l) x =
        edgeBalance (familyEdges J) x + propInt (x = a) - propInt (x = b)) :
    OneHoleToggleCertificate G J a b := by
  let hu := oneHoleRouteToggledEdges_biUnique hJ ha hl
  refine
    { edges := oneHoleRouteToggledEdges G J l
      edges_in_graph := oneHoleRouteToggledEdges_subset_adj G J l
      outgoing_unique := fun {_ _ _} h₁ h₂ ↦ hu.2 h₁ h₂
      incoming_unique := fun {_ _ _} h₁ h₂ ↦ hu.1 h₁ h₂
      finite_components := ?_
      old_isolated_not_incident :=
        oneHoleRouteToggledEdges_old_isolated_not_incident hJ ha hl
      balance_delta := hbalance }
  exact G.finite_componentSupports_of_finiteModification_familyEdges
    hJ.isWarp hJ.hasFiniteCharacter
      (oneHoleRouteBackwardEdges_finite G J l)
      (oneHoleRouteForwardEdges_finite G J l)

private theorem not_hasOutgoing_familyEdges_of_outside_vertexSet
    {G : DWeb V} {J : Set G.DPath} {x : V}
    (hx : x ∉ G.vertexSet J) : ¬ HasOutgoing (familyEdges J) x := by
  rintro ⟨y, hxy⟩
  simp only [familyEdges, Set.mem_iUnion] at hxy
  rcases hxy with ⟨p, hpJ, hpedge⟩
  exact hx ⟨p, hpJ, (p.edgeSet_subset_support_prod hpedge).1⟩

private theorem not_hasIncoming_familyEdges_of_outside_vertexSet
    {G : DWeb V} {J : Set G.DPath} {x : V}
    (hx : x ∉ G.vertexSet J) : ¬ HasIncoming (familyEdges J) x := by
  rintro ⟨y, hyx⟩
  simp only [familyEdges, Set.mem_iUnion] at hyx
  rcases hyx with ⟨p, hpJ, hpedge⟩
  exact hx ⟨p, hpJ, (p.edgeSet_subset_support_prod hpedge).2⟩

private theorem edgeBalance_familyEdges_eq_zero_of_outside_vertexSet
    {G : DWeb V} {J : Set G.DPath} {x : V}
    (hx : x ∉ G.vertexSet J) : edgeBalance (familyEdges J) x = 0 := by
  have hout := not_hasOutgoing_familyEdges_of_outside_vertexSet hx
  have hin := not_hasIncoming_familyEdges_of_outside_vertexSet hx
  simp [edgeBalance, propInt, hout, hin]

/-- The generic finite-component decomposition turns a certified residual
toggle into an exact one-point augmentation. -/
theorem exists_onePointAugmentation_of_toggleCertificate
    (G : DWeb V) {J : Set G.DPath} (hJ : G.IsCleanFiniteWarp J)
    {a b : V} (ha : a ∈ G.source \ G.initialSet J)
    (hb : b ∈ G.target \ G.terminalFrontier J) (hab : a ≠ b)
    (T : OneHoleToggleCertificate G J a b) :
    ∃ Jplus, G.IsOnePointAugmentation J Jplus := by
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
  refine ⟨C.pathPart, a, ha, b, hb, C.pathPart_isWarp, hCfin, ?_, ?_⟩
  · ext x
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

  · ext x
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

/-- The route balance law completes the marked residual augmentation
principle. -/
theorem oneHoleMarkedAugmentation_of_routeBalance
    (hbalance : OneHoleRouteBalanceLaw V) :
    OneHoleMarkedAugmentation V := by
  intro G J hJ b hb hreach
  rcases hreach with ⟨a, ha, habReach⟩
  by_cases hab : a = b
  · subst b
    exact G.exists_onePointAugmentation_of_common_gap hJ ha hb
  · obtain ⟨l, hl⟩ := exists_reduced_markedRoute G J habReach
    let T : OneHoleToggleCertificate G J a b :=
      oneHoleToggleCertificateOfReducedRoute hJ ha hl
        (hbalance G J a b l hJ ha hl)
    exact exists_onePointAugmentation_of_toggleCertificate
      G hJ ha hb hab T

end DWeb
end Erdos599
