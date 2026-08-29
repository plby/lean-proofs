/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RoofQuotient
import ErdosProblems.Erdos599.WaveLimits

/-!
# Iterated quotients

This file proves the path-theoretic core of Aharoni--Berger Lemma 2.26.
In the same-vertex-type model used in this development, vertices deleted by
the first quotient remain as isolated formal vertices.  Consequently the
source identity

`strictRoof_(G / X) Y = strictRoof_G (X ∪ Y)`

is literal: the old strict-roof vertices occur on both sides.  This is the
key graph relation calculation behind quotient associativity and the common
quotient used in Lemmas 3.29 and 3.30.
-/

namespace Erdos599

open Set
open DirectedPath

universe u

variable {V : Type u}

namespace DWeb

/-- A vertex is in the strict roof of `S` exactly when every target path
from it meets `S` away from the vertex itself. -/
theorem mem_strictRoof_iff_mem_roof_sdiff_singleton
    (G : DWeb V) (S : Set V) (v : V) :
    v ∈ G.strictRoof S ↔ v ∈ G.roof (S \ {v}) := by
  constructor
  · intro hv
    by_cases hvS : v ∈ S
    · by_contra hnot
      exact hv.2 ⟨hvS, hnot⟩
    · have hsub : S ⊆ S \ {v} := by
        intro x hx
        exact ⟨hx, fun hxv ↦ hvS (hxv ▸ hx)⟩
      exact G.roof_mono hsub hv.1
  · intro hv
    refine ⟨G.roof_mono Set.sdiff_subset hv, ?_⟩
    intro hvEss
    exact hvEss.2 hv

/-- If a simple target path avoids `X` except possibly at its first vertex,
then none of its vertices lies in the strict roof of `X`. -/
private theorem walk_support_avoids_strictRoof_of_avoids_except_start
    (G : DWeb V) (X : Set V) :
    ∀ {a b : V} (p : Walk G.graph a b), p.IsPath → b ∈ G.target →
      (∀ ⦃x⦄, x ∈ p.support → x ∈ X → x = a) →
      ∀ ⦃x⦄, x ∈ p.support → x ∉ G.strictRoof X := by
  intro a b p hp hb hav
  induction p with
  | @nil u =>
      intro x hx
      have hxa : x = u := by simpa using hx
      subst x
      rw [G.mem_strictRoof_iff_mem_roof_sdiff_singleton]
      intro haRoof
      let q : FinitePath G.graph :=
        { start := u, finish := u, walk := .nil, isPath := Walk.isPath_nil u }
      obtain ⟨z, hzq, hzX, hzne⟩ := haRoof q ⟨rfl, hb⟩
      have hza : z = u := by
        change z ∈ ([u] : List V) at hzq
        simpa using hzq
      exact hzne hza
  | @cons u c w e p ih =>
      have htailPath : p.IsPath := (List.nodup_cons.mp hp).2
      have huNotTail : u ∉ p.support := (List.nodup_cons.mp hp).1
      have havTail : ∀ ⦃z⦄, z ∈ p.support → z ∈ X → z = c := by
        intro z hzp hzX
        have hzu : z = u := hav (by simp [hzp]) hzX
        exact False.elim (huNotTail (hzu ▸ hzp))
      intro x hx
      simp only [Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · rw [G.mem_strictRoof_iff_mem_roof_sdiff_singleton]
        intro haRoof
        let q : FinitePath G.graph :=
          { start := x, finish := w, walk := .cons e p, isPath := hp }
        obtain ⟨z, hzq, hzX, hzne⟩ := haRoof q ⟨rfl, hb⟩
        exact hzne (hav hzq hzX)
      · exact ih htailPath hb havTail hx

/-- Avoiding `X ∪ Y` away from the initial vertex in the original web is
equivalent to avoiding `Y` away from that vertex after quotienting by `X`.
This is the finite-path content of source Lemma 2.26. -/
theorem canReachTargetAvoiding_union_sdiff_singleton_iff_quotient
    (G : DWeb V) (X Y : Set V) (v : V) :
    G.CanReachTargetAvoiding ((X ∪ Y) \ {v}) v ↔
      (G.quotient X).CanReachTargetAvoiding (Y \ {v}) v := by
  constructor
  · rintro ⟨p, hp, hav⟩
    have havAtStart : ∀ ⦃x⦄, x ∈ p.walk.support → x ∈ X → x = p.start := by
      intro x hxp hxX
      by_contra hxne
      exact Set.disjoint_left.1 hav hxp
        ⟨Or.inl hxX, fun hxv ↦ hxne (hxv.trans hp.1.symm)⟩
    have hstrict : ∀ ⦃x⦄, x ∈ p.walk.support → x ∉ G.strictRoof X :=
      G.walk_support_avoids_strictRoof_of_avoids_except_start
        X p.walk p.isPath hp.2 havAtStart
    have hcommit : ∀ ⦃x⦄, x ∈ p.walk.support.tail → x ∉ X := by
      intro x hxtail hxX
      have hxstart : x = p.start := havAtStart (List.mem_of_mem_tail hxtail) hxX
      exact p.walk.start_not_mem_tail p.isPath (hxstart ▸ hxtail)
    let q : FinitePath (G.quotient X).graph :=
      G.restrictFinitePathToQuotient X p (@hstrict) (@hcommit)
    have hqstart : q.start = v := by
      change p.start = v
      exact hp.1
    have hqfinish : q.finish ∈ (G.quotient X).target := by
      change p.finish ∈ G.target
      exact hp.2
    refine ⟨q, ⟨hqstart, hqfinish⟩, ?_⟩
    apply Set.disjoint_left.2
    intro x hxq hxY
    have hxp : x ∈ p.support := by
      rw [show q.support = p.support from
        G.support_restrictFinitePathToQuotient X p (@hstrict) (@hcommit)] at hxq
      exact hxq
    exact Set.disjoint_left.1 hav hxp ⟨Or.inr hxY.1, hxY.2⟩
  · rintro ⟨q, hq, hav⟩
    let p : FinitePath G.graph :=
      q.lift (fun {_ _} e ↦ G.quotient_adj_imp e)
    refine ⟨p, ⟨hq.1, hq.2⟩, ?_⟩
    apply Set.disjoint_left.2
    intro x hxp hxUnion
    have hxq : x ∈ q.support := by
      simpa only [p, FinitePath.support_lift] using hxp
    rcases (RelationalRoof.mem_support_iff_start_or_mem_tail
      (G.quotient X).graph.Adj q.walk).1 hxq with hxstart | hxtail
    · exact hxUnion.2 (hxstart.trans hq.1)
    · rcases hxUnion.1 with hxX | hxY
      · exact (G.quotientWalk_tail_avoids q.walk hxtail).2 hxX
      · exact Set.disjoint_left.1 hav hxq ⟨hxY, hxUnion.2⟩

/-- Same-type form of Aharoni--Berger Lemma 2.26.  The first quotient's
formally deleted vertices are isolated and hence already belong to the
second strict roof, so no explicit union with the old strict roof is needed. -/
theorem strictRoof_quotient_eq_strictRoof_union
    (G : DWeb V) (X Y : Set V) :
    (G.quotient X).strictRoof Y = G.strictRoof (X ∪ Y) := by
  ext v
  rw [(G.quotient X).mem_strictRoof_iff_mem_roof_sdiff_singleton,
    G.mem_strictRoof_iff_mem_roof_sdiff_singleton]
  constructor
  · intro hq
    by_contra hg
    have hr := (G.not_mem_roof_iff _ _).1 hg
    have hqr :=
      (G.canReachTargetAvoiding_union_sdiff_singleton_iff_quotient X Y v).1 hr
    exact ((G.quotient X).not_mem_roof_iff _ _).2 hqr hq
  · intro hg
    by_contra hq
    have hqr := ((G.quotient X).not_mem_roof_iff _ _).1 hq
    have hr :=
      (G.canReachTargetAvoiding_union_sdiff_singleton_iff_quotient X Y v).2 hqr
    exact (G.not_mem_roof_iff _ _).2 hr hg

/-- The graph and target fields of an iterated quotient agree with those
of the quotient by the union.  The source field is treated separately,
because it additionally uses essential-source trimming. -/
theorem quotient_quotient_graph_eq_union
    (G : DWeb V) (X Y : Set V) :
    ((G.quotient X).quotient Y).graph = (G.quotient (X ∪ Y)).graph := by
  ext a b
  change
    ((G.quotient X).graph.Adj a b ∧
        a ∉ (G.quotient X).strictRoof Y ∧
        b ∉ (G.quotient X).strictRoof Y ∧ b ∉ Y) ↔
      (G.graph.Adj a b ∧ a ∉ G.strictRoof (X ∪ Y) ∧
        b ∉ G.strictRoof (X ∪ Y) ∧ b ∉ X ∪ Y)
  rw [G.strictRoof_quotient_eq_strictRoof_union]
  change
    ((G.graph.Adj a b ∧ a ∉ G.strictRoof X ∧
        b ∉ G.strictRoof X ∧ b ∉ X) ∧
        a ∉ G.strictRoof (X ∪ Y) ∧
        b ∉ G.strictRoof (X ∪ Y) ∧ b ∉ Y) ↔ _
  constructor
  · rintro ⟨⟨e, haX, hbX, hbNotX⟩, haXY, hbXY, hbNotY⟩
    exact ⟨e, haXY, hbXY, fun hb ↦ hb.elim hbNotX hbNotY⟩
  · rintro ⟨e, haXY, hbXY, hbNotUnion⟩
    have hmono : G.strictRoof X ⊆ G.strictRoof (X ∪ Y) := by
      intro z hz
      rw [G.mem_strictRoof_iff_mem_roof_sdiff_singleton] at hz ⊢
      apply G.roof_mono (show X \ {z} ⊆ (X ∪ Y) \ {z} by
        intro t ht
        exact ⟨Or.inl ht.1, ht.2⟩)
      exact hz
    exact ⟨⟨e, fun h ↦ haXY (hmono h), fun h ↦ hbXY (hmono h),
      fun hb ↦ hbNotUnion (Or.inl hb)⟩,
      haXY, hbXY, fun hb ↦ hbNotUnion (Or.inr hb)⟩

/-- Essential-source calculation for an iterated quotient.  The global
normalization that no edge enters the original source is used only when a
path in the first quotient is lifted: after its initial vertex, that path
cannot visit the old source. -/
theorem essential_source_union_quotient_eq
    (G : DWeb V) (X Y : Set V)
    (hNoEnter : G.NoEdgeEnters G.source) :
    (G.quotient X).essential ((G.quotient X).source ∪ Y) =
      G.essential (G.source ∪ (X ∪ Y)) := by
  ext s
  constructor
  · rintro ⟨hsMem, hsNotRoof⟩
    obtain ⟨q, hq, hqAvoid⟩ :=
      ((G.quotient X).not_mem_roof_iff
        (((G.quotient X).source ∪ Y) \ {s}) s).1 hsNotRoof
    let p : FinitePath G.graph :=
      q.lift (fun {_ _} e ↦ G.quotient_adj_imp e)
    have hsBig : s ∈ G.source ∪ (X ∪ Y) := by
      rcases hsMem with hsSource | hsY
      · rcases G.essential_subset (G.source ∪ X) hsSource with hsA | hsX
        · exact Or.inl hsA
        · exact Or.inr (Or.inl hsX)
      · exact Or.inr (Or.inr hsY)
    refine ⟨hsBig, (G.not_mem_roof_iff _ _).2 ⟨p, ⟨hq.1, hq.2⟩, ?_⟩⟩
    apply Set.disjoint_left.2
    intro z hzp hzBig
    have hzq : z ∈ q.support := by
      simpa only [p, FinitePath.support_lift] using hzp
    rcases (RelationalRoof.mem_support_iff_start_or_mem_tail
      (G.quotient X).graph.Adj q.walk).1 hzq with hzstart | hztail
    · exact hzBig.2 (hzstart.trans hq.1)
    · rcases hzBig.1 with hzA | hzXY
      · have hzpTail : z ∈ p.walk.support.tail := by
          change z ∈ (q.walk.lift fun {_ _} e ↦ G.quotient_adj_imp e).support.tail
          simpa using hztail
        exact (G.walk_tail_avoids_of_noEdgeEnters hNoEnter p.walk hzpTail) hzA
      · rcases hzXY with hzX | hzY
        · exact (G.quotientWalk_tail_avoids q.walk hztail).2 hzX
        · exact Set.disjoint_left.1 hqAvoid hzq
            ⟨Or.inr hzY, hzBig.2⟩
  · rintro hs
    obtain ⟨p, hp, hpAvoid⟩ :=
      (G.not_mem_roof_iff ((G.source ∪ (X ∪ Y)) \ {s}) s).1 hs.2
    have hsSmall : s ∈ (G.quotient X).source ∪ Y := by
      rcases hs.1 with hsA | hsXY
      · left
        refine ⟨Or.inl hsA, ?_⟩
        apply (G.not_mem_roof_iff ((G.source ∪ X) \ {s}) s).2
        refine ⟨p, hp, Set.disjoint_left.2 ?_⟩
        intro z hzp hz
        exact Set.disjoint_left.1 hpAvoid hzp
          ⟨hz.1.elim Or.inl (fun hzX ↦ Or.inr (Or.inl hzX)), hz.2⟩
      · rcases hsXY with hsX | hsY
        · left
          refine ⟨Or.inr hsX, ?_⟩
          apply (G.not_mem_roof_iff ((G.source ∪ X) \ {s}) s).2
          refine ⟨p, hp, Set.disjoint_left.2 ?_⟩
          intro z hzp hz
          exact Set.disjoint_left.1 hpAvoid hzp
            ⟨hz.1.elim Or.inl (fun hzX ↦ Or.inr (Or.inl hzX)), hz.2⟩
        · exact Or.inr hsY
    have hpReachReordered :
        G.CanReachTargetAvoiding ((X ∪ (G.source ∪ Y)) \ {s}) s := by
      have hset : X ∪ (G.source ∪ Y) = G.source ∪ (X ∪ Y) := by
        ac_rfl
      rw [hset]
      exact ⟨p, hp, hpAvoid⟩
    obtain ⟨q, hq, hqAvoid⟩ :=
      (G.canReachTargetAvoiding_union_sdiff_singleton_iff_quotient
        X (G.source ∪ Y) s).1 hpReachReordered
    refine ⟨hsSmall,
      ((G.quotient X).not_mem_roof_iff
        (((G.quotient X).source ∪ Y) \ {s}) s).2 ⟨q, hq, ?_⟩⟩
    apply Set.disjoint_left.2
    intro z hzq hzSmall
    rcases (RelationalRoof.mem_support_iff_start_or_mem_tail
      (G.quotient X).graph.Adj q.walk).1 hzq with hzstart | hztail
    · exact hzSmall.2 (hzstart.trans hq.1)
    · rcases hzSmall.1 with hzSource | hzY
      · rcases G.essential_subset (G.source ∪ X) hzSource with hzA | hzX
        · exact Set.disjoint_left.1 hqAvoid hzq
            ⟨Or.inl hzA, hzSmall.2⟩
        · exact (G.quotientWalk_tail_avoids q.walk hztail).2 hzX
      · exact Set.disjoint_left.1 hqAvoid hzq
          ⟨Or.inr hzY, hzSmall.2⟩

/-- Normalized quotient associativity, the same-type version of source
Lemma 2.27. -/
theorem quotient_quotient_eq_union
    (G : DWeb V) (X Y : Set V)
    (hNoEnter : G.NoEdgeEnters G.source) :
    (G.quotient X).quotient Y = G.quotient (X ∪ Y) := by
  rw [DWeb.mk.injEq]
  refine ⟨G.quotient_quotient_graph_eq_union X Y, ?_, rfl⟩
  exact G.essential_source_union_quotient_eq X Y hNoEnter

/-- Quotient sets with the same essential core define the same normalized
quotient.  This is the concrete sandwich form used to pass from a union to
its essential part in Corollary 2.28. -/
theorem quotient_eq_of_essential_subset
    (G : DWeb V) {C D : Set V}
    (hCD : C ⊆ D) (hEss : G.essential D ⊆ C)
    (hNoEnter : G.NoEdgeEnters G.source)
    (hSourceD : Disjoint G.source D) :
    G.quotient C = G.quotient D := by
  have hRoof : G.roof C = G.roof D := by
    apply Set.Subset.antisymm
    · exact G.roof_mono hCD
    · rw [← G.roof_essential D]
      exact G.roof_mono hEss
  have hEssential : G.essential C = G.essential D := by
    exact RelationalRoof.essential_sandwich G.graph.Adj G.target hEss hCD
  have hStrict : G.strictRoof C = G.strictRoof D := by
    rw [strictRoof, strictRoof, hRoof, hEssential]
  have hDCStrict : D \ C ⊆ G.strictRoof D := by
    intro x hx
    exact ⟨G.subset_roof D hx.1,
      fun hxEss ↦ hx.2 (hEss hxEss)⟩
  have hSourceC : Disjoint G.source C :=
    hSourceD.mono_right hCD
  rw [DWeb.mk.injEq]
  refine ⟨?_, ?_, rfl⟩
  · ext a b
    change
      (G.graph.Adj a b ∧ a ∉ G.strictRoof C ∧
          b ∉ G.strictRoof C ∧ b ∉ C) ↔
        (G.graph.Adj a b ∧ a ∉ G.strictRoof D ∧
          b ∉ G.strictRoof D ∧ b ∉ D)
    rw [hStrict]
    constructor
    · rintro ⟨e, ha, hb, hbC⟩
      refine ⟨e, ha, hb, ?_⟩
      intro hbD
      exact hb (hDCStrict ⟨hbD, hbC⟩)
    · rintro ⟨e, ha, hb, hbD⟩
      exact ⟨e, ha, hb, fun hbC ↦ hbD (hCD hbC)⟩
  · rw [G.quotient_source_eq_union_sdiff_strictRoof_of_noEdgeEnters
        hNoEnter hSourceC,
      G.quotient_source_eq_union_sdiff_strictRoof_of_noEdgeEnters
        hNoEnter hSourceD,
      hStrict]
    ext x
    constructor
    · rintro ⟨hxA | hxC, hxNotStrict⟩
      · exact ⟨Or.inl hxA, hxNotStrict⟩
      · exact ⟨Or.inr (hCD hxC), hxNotStrict⟩
    · rintro ⟨hxA | hxD, hxNotStrict⟩
      · exact ⟨Or.inl hxA, hxNotStrict⟩
      · by_cases hxC : x ∈ C
        · exact ⟨Or.inr hxC, hxNotStrict⟩
        · exact False.elim (hxNotStrict (hDCStrict ⟨hxD, hxC⟩))

/-- Aharoni--Berger Corollary 2.28, left-hand common-quotient identity. -/
theorem quotient_quotient_essential_union_left
    (G : DWeb V) (X₁ X₂ : Set V)
    (hNoEnter : G.NoEdgeEnters G.source)
    (hSource : Disjoint G.source (X₁ ∪ X₂)) :
    (G.quotient X₁).quotient (G.essential (X₁ ∪ X₂)) =
      G.quotient (G.essential (X₁ ∪ X₂)) := by
  let U := X₁ ∪ X₂
  let Y := G.essential U
  have hX₁U : X₁ ⊆ U := Set.subset_union_left
  have hYU : Y ⊆ U := G.essential_subset U
  have hX₁Y_U : X₁ ∪ Y ⊆ U := Set.union_subset hX₁U hYU
  have hY_X₁Y : G.essential U ⊆ X₁ ∪ Y := Set.subset_union_right
  have hQU : G.quotient (X₁ ∪ Y) = G.quotient U :=
    G.quotient_eq_of_essential_subset hX₁Y_U hY_X₁Y hNoEnter hSource
  have hQY : G.quotient Y = G.quotient U :=
    G.quotient_eq_of_essential_subset hYU Set.Subset.rfl hNoEnter hSource
  calc
    (G.quotient X₁).quotient (G.essential (X₁ ∪ X₂)) =
        G.quotient (X₁ ∪ Y) := by
          simpa only [U, Y] using
            G.quotient_quotient_eq_union X₁ Y hNoEnter
    _ = G.quotient U := hQU
    _ = G.quotient Y := hQY.symm
    _ = G.quotient (G.essential (X₁ ∪ X₂)) := rfl

/-- Symmetric right-hand identity in Corollary 2.28. -/
theorem quotient_quotient_essential_union_right
    (G : DWeb V) (X₁ X₂ : Set V)
    (hNoEnter : G.NoEdgeEnters G.source)
    (hSource : Disjoint G.source (X₁ ∪ X₂)) :
    (G.quotient X₂).quotient (G.essential (X₁ ∪ X₂)) =
      G.quotient (G.essential (X₁ ∪ X₂)) := by
  have hSource' : Disjoint G.source (X₂ ∪ X₁) := by
    simpa [Set.union_comm] using hSource
  simpa only [Set.union_comm X₂ X₁] using
    G.quotient_quotient_essential_union_left X₂ X₁ hNoEnter hSource'

/-! ## Wave quotient kernel -/

/-- Source Lemma 3.5 reduced to the structural clauses of Definition 2.29.
The separate quotient-component construction only has to provide the warp,
initial, and terminal clauses displayed here. -/
theorem isWave_of_quotientWarp_frontiers
    (G : DWeb V) {X : Set V} {W : Set G.DPath}
    (hW : G.IsWave W)
    {R : Set (G.quotient X).DPath}
    (hWarp : (G.quotient X).IsWarp R)
    (hInitial : (G.quotient X).initialSet R ⊆
      (G.quotient X).source)
    (hTerminal :
      (G.terminalFrontier W \ G.strictRoof X) ∪
          (G.essential X \ G.vertexSet W) ⊆
        (G.quotient X).terminalFrontier R) :
    (G.quotient X).IsWave R := by
  refine ⟨hWarp, hInitial, ?_⟩
  intro a ha q hq
  have haNotStrict : a ∉ G.strictRoof X := by
    intro haStrict
    apply ha.2
    rw [G.mem_strictRoof_iff_mem_roof_sdiff_singleton] at haStrict
    apply G.roof_mono (show X \ {a} ⊆ (G.source ∪ X) \ {a} by
      intro z hz
      exact ⟨Or.inr hz.1, hz.2⟩)
    exact haStrict
  have hqAvoidStrict : Disjoint q.support (G.strictRoof X) := by
    apply Set.disjoint_left.2
    intro z hzq hzStrict
    rcases (RelationalRoof.mem_support_iff_start_or_mem_tail
      (G.quotient X).graph.Adj q.walk).1 hzq with hzstart | hztail
    · exact haNotStrict (hzstart.trans hq.1 ▸ hzStrict)
    · exact (G.quotientWalk_tail_avoids q.walk hztail).1 hzStrict
  let p : FinitePath G.graph :=
    q.lift (fun {_ _} e ↦ G.quotient_adj_imp e)
  have hp : G.IsTargetPathFrom a p := ⟨hq.1, hq.2⟩
  rcases ha.1 with haSource | haX
  · obtain ⟨t, htp, htW⟩ := hW.2.2 haSource p hp
    have htq : t ∈ q.support := by
      simpa only [p, FinitePath.support_lift] using htp
    exact ⟨t, htq, hTerminal (Or.inl
      ⟨htW, Set.disjoint_left.1 hqAvoidStrict htq⟩)⟩
  · by_cases haVertex : a ∈ G.vertexSet W
    · have haRoof : a ∈ G.roof (G.terminalFrontier W) :=
        DWeb.IsWave.self_roofing (Γ := G) hW haVertex
      obtain ⟨t, htp, htW⟩ := haRoof p hp
      have htq : t ∈ q.support := by
        simpa only [p, FinitePath.support_lift] using htp
      exact ⟨t, htq, hTerminal (Or.inl
        ⟨htW, Set.disjoint_left.1 hqAvoidStrict htq⟩)⟩
    · have haEssential : a ∈ G.essential X := by
        rw [← G.sdiff_strictRoof_self X]
        exact ⟨haX, haNotStrict⟩
      exact ⟨a, hq.1 ▸ q.start_mem_support,
        hTerminal (Or.inr ⟨haEssential, haVertex⟩)⟩

/-- Source Lemma 3.5 for the already-admissible quotient constructor.  The
full constructor first decomposes an arbitrary warp into its maximal
admissible components, after which this theorem applies unchanged. -/
theorem IsWave.admissibleWarpQuotient
    (G : DWeb V) {X : Set V} {W : Set G.DPath}
    (hNoEnter : G.NoEdgeEnters G.source)
    (hSourceX : Disjoint G.source X)
    (hW : G.IsWave W)
    (hAdmissible : ∀ p ∈ W, G.PathQuotientAdmissible X p) :
    (G.quotient X).IsWave
      (G.admissibleWarpQuotient X W hAdmissible) := by
  apply G.isWave_of_quotientWarp_frontiers hW
  · exact DWeb.IsWarp.admissibleWarpQuotient G hW.1 hAdmissible
  · rw [G.initialSet_admissibleWarpQuotient_source_formula]
    intro a ha
    rw [G.quotient_source_eq_union_sdiff_strictRoof_of_noEdgeEnters
      hNoEnter hSourceX]
    exact ⟨ha.1.elim (fun h ↦ Or.inl (hW.2.1 h)) Or.inr, ha.2⟩
  · rw [G.terminalFrontier_admissibleWarpQuotient]
    rintro x (hx | hx)
    · exact Or.inl hx.1
    · exact Or.inr hx

end DWeb

end Erdos599
