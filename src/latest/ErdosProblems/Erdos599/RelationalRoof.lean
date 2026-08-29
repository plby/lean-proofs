/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DirectedPath
import Mathlib.Data.List.Nodup

/-!
# Relation-generic roof calculus for Erdős Problem 599

This file contains the elementary finite-path calculus from Section 2 of
Aharoni--Berger.  It is deliberately independent of `DWeb`: the only data are
an arbitrary directed relation `R` and a target set `B`.  Paths are the
endpoint-indexed walks and finite paths from `DirectedPath.lean`, specialized
to the digraph whose adjacency relation is `R`.

Besides the basic roof laws, the file proves source Lemmas 2.14 and 2.16--2.19,
the roof/deletion identity, and exposes the already-proved last-exit
construction at the relation level.  No finiteness or decidable-equality
assumption is made on the vertex type.
-/

namespace Erdos599.RelationalRoof

open Set
open Erdos599.DirectedPath

universe u

variable {V : Type u}

/-- Regard an arbitrary binary relation as a Mathlib digraph. -/
abbrev relationDigraph (R : V → V → Prop) : Digraph V := ⟨R⟩

/-- A finite simple path for an arbitrary directed relation. -/
abbrev Path (R : V → V → Prop) :=
  DirectedPath.FinitePath (relationDigraph R)

/-- A finite endpoint-indexed walk for an arbitrary directed relation. -/
abbrev Walk (R : V → V → Prop) (u v : V) :=
  DirectedPath.Walk (relationDigraph R) u v

variable (R : V → V → Prop) (B : Set V)

/-- A finite path begins at `v` and ends in the fixed target `B`. -/
def IsTargetPathFrom (v : V) (p : Path R) : Prop :=
  p.start = v ∧ p.finish ∈ B

/-- A finite path meets a vertex set. -/
def Meets (p : Path R) (S : Set V) : Prop :=
  p.walk.Meets S

/-- A finite path avoids a vertex set. -/
def Avoids (p : Path R) (S : Set V) : Prop :=
  ∀ {x}, x ∈ p.walk.support → x ∉ S

/-- A vertex reaches `B` by a finite path avoiding `S`. -/
def CanReachAvoiding (S : Set V) (v : V) : Prop :=
  ∃ p : Path R, IsTargetPathFrom R B v p ∧ Avoids R p S

/-- The roof of `S`: vertices from which every finite path to `B` meets `S`. -/
def roof (S : Set V) : Set V :=
  {v | ∀ p : Path R, IsTargetPathFrom R B v p → Meets R p S}

/-- The essential part of `S`. -/
def essential (S : Set V) : Set V :=
  {s | s ∈ S ∧ s ∉ roof R B (S \ {s})}

/-- The strict roof of `S`. -/
def strictRoof (S : Set V) : Set V :=
  roof R B S \ essential R B S

@[simp] theorem mem_roof_iff (S : Set V) (v : V) :
    v ∈ roof R B S ↔
      ∀ p : Path R, IsTargetPathFrom R B v p → Meets R p S :=
  Iff.rfl

@[simp] theorem mem_essential_iff (S : Set V) (s : V) :
    s ∈ essential R B S ↔
      s ∈ S ∧ s ∉ roof R B (S \ {s}) :=
  Iff.rfl

@[simp] theorem mem_strictRoof_iff (S : Set V) (v : V) :
    v ∈ strictRoof R B S ↔
      v ∈ roof R B S ∧ v ∉ essential R B S :=
  Iff.rfl

theorem avoids_iff_not_meets (p : Path R) (S : Set V) :
    Avoids R p S ↔ ¬ Meets R p S := by
  constructor
  · intro h ⟨x, hxp, hxS⟩
    exact h hxp hxS
  · intro h x hxp hxS
    exact h ⟨x, hxp, hxS⟩

theorem not_mem_roof_iff (S : Set V) (v : V) :
    v ∉ roof R B S ↔ CanReachAvoiding R B S v := by
  constructor
  · intro hv
    change ¬ ∀ p : Path R, IsTargetPathFrom R B v p → Meets R p S at hv
    simp only [not_forall] at hv
    obtain ⟨p, hp, hmeet⟩ := hv
    exact ⟨p, hp, (avoids_iff_not_meets R p S).2 hmeet⟩
  · rintro ⟨p, hp, hav⟩ hv
    exact (avoids_iff_not_meets R p S).1 hav (hv p hp)

theorem subset_roof (S : Set V) : S ⊆ roof R B S := by
  intro v hv p hp
  exact ⟨p.start, p.start_mem_support, hp.1 ▸ hv⟩

theorem roof_mono : Monotone (roof R B) := by
  intro S T hST v hv p hp
  obtain ⟨x, hxp, hxS⟩ := hv p hp
  exact ⟨x, hxp, hST hxS⟩

theorem essential_subset (S : Set V) : essential R B S ⊆ S :=
  fun _ hs ↦ hs.1

theorem essential_subset_roof (S : Set V) :
    essential R B S ⊆ roof R B S :=
  (essential_subset R B S).trans (subset_roof R B S)

theorem strictRoof_subset_roof (S : Set V) :
    strictRoof R B S ⊆ roof R B S :=
  Set.sdiff_subset

theorem disjoint_strictRoof_essential (S : Set V) :
    Disjoint (strictRoof R B S) (essential R B S) :=
  Set.disjoint_sdiff_left

theorem roof_eq_strictRoof_union_essential (S : Set V) :
    roof R B S = strictRoof R B S ∪ essential R B S := by
  rw [strictRoof, Set.sdiff_union_of_subset (essential_subset_roof R B S)]

/-! ## Walk simplification and suffix witnesses -/

/-- Change the displayed initial endpoint of a walk along an equality. -/
def castStart {u u' v : V} (h : u = u') (p : Walk R u v) : Walk R u' v :=
  h ▸ p

@[simp] theorem support_castStart {u u' v : V} (h : u = u') (p : Walk R u v) :
    (castStart R h p).support = p.support := by
  subst u'
  rfl

@[simp] theorem getElem?_zero_support {u v : V} (p : Walk R u v) :
    p.support[0]? = some u := by
  cases p <;> rfl

/-- Every finite directed walk contains a simple path with the same endpoints
and no new vertices.  The proof erases a loop whenever the initial vertex
occurs again in the recursively simplified tail. -/
theorem exists_pathTo_support_subset :
    ∀ {u v : V} (p : Walk R u v),
      ∃ q : DirectedPath.Walk.PathTo (relationDigraph R) u v,
        ∀ {x}, x ∈ q.1.support → x ∈ p.support
  | u, _, .nil => by
      exact ⟨⟨.nil, DirectedPath.Walk.isPath_nil u⟩, by simp⟩
  | u, v, .cons (v := w) h p => by
      obtain ⟨q, hq⟩ := exists_pathTo_support_subset p
      by_cases hu : u ∈ q.1.support
      · let hm : q.1.Meets ({u} : Set V) := ⟨u, hu, Set.mem_singleton u⟩
        let L := DirectedPath.Walk.lastHit q.1 ({u} : Set V) hm
        have hLu : L.startpoint = u := Set.mem_singleton_iff.1 L.startpoint_mem
        let r : DirectedPath.Walk.PathTo (relationDigraph R) u v :=
          ⟨castStart R hLu L.walk, by
            simpa [DirectedPath.Walk.IsPath] using L.isPath q.2⟩
        refine ⟨r, ?_⟩
        intro x hx
        have hxL : x ∈ L.walk.support := by simpa [r] using hx
        exact List.mem_cons_of_mem u (hq (L.support_subset hxL))
      · let q' : DirectedPath.Walk.PathTo (relationDigraph R) u v :=
          ⟨.cons h q.1, by simpa [DirectedPath.Walk.IsPath, hu] using q.2⟩
        refine ⟨q', ?_⟩
        intro x hx
        simp only [q', DirectedPath.Walk.support_cons, List.mem_cons] at hx ⊢
        exact hx.elim (fun hxu ↦ Or.inl hxu) (fun hxq ↦ Or.inr (hq hxq))

/-- A support vertex is either the initial vertex or belongs to the tail of
the support list. -/
theorem mem_support_iff_start_or_mem_tail {u v x : V} (p : Walk R u v) :
    x ∈ p.support ↔ x = u ∨ x ∈ p.support.tail := by
  cases p <;> simp

/-- A walk with different endpoints has a first edge and a remaining tail. -/
theorem exists_cons_of_start_ne_finish {u v : V} (p : Walk R u v)
    (huv : u ≠ v) :
    ∃ w, ∃ h : R u w, ∃ q : Walk R w v, p = .cons h q := by
  cases p with
  | nil => exact (huv rfl).elim
  | cons h q => exact ⟨_, h, q, rfl⟩

/-- Membership in a roof can equivalently be tested against arbitrary finite
walks.  This is the loop-erasure bridge used when two paths are spliced. -/
theorem roof_meets_walk {v b : V} {S : Set V}
    (hv : v ∈ roof R B S) (p : Walk R v b) (hb : b ∈ B) :
    p.Meets S := by
  obtain ⟨q, hqp⟩ := exists_pathTo_support_subset (R := R) p
  let q' : Path R :=
    { start := v
      finish := b
      walk := q.1
      isPath := q.2 }
  obtain ⟨x, hxq, hxS⟩ := hv q' ⟨rfl, hb⟩
  exact ⟨x, hqp hxq, hxS⟩

/-- A target path avoiding `S` witnesses that each of its vertices is outside
the roof of `S`: take the suffix beginning at the last occurrence. -/
theorem not_mem_roof_of_mem_targetPath {v x : V} {S : Set V}
    (p : Path R) (hp : IsTargetPathFrom R B v p)
    (hav : Avoids R p S) (hx : x ∈ p.walk.support) :
    x ∉ roof R B S := by
  let hm : p.walk.Meets ({x} : Set V) := ⟨x, hx, Set.mem_singleton x⟩
  let L := DirectedPath.Walk.lastHit p.walk ({x} : Set V) hm
  have hLx : L.startpoint = x := Set.mem_singleton_iff.1 L.startpoint_mem
  apply (not_mem_roof_iff R B S x).2
  let q : Path R :=
    { start := x
      finish := p.finish
      walk := castStart R hLx L.walk
      isPath := by
        simpa [DirectedPath.Walk.IsPath] using L.isPath p.isPath }
  refine ⟨q, ⟨rfl, hp.2⟩, ?_⟩
  intro y hyq
  exact hav (L.support_subset (by simpa [q] using hyq))

/-- If a simple target path avoids `S` except possibly at its first vertex,
then every later vertex is outside `roof S`. -/
theorem not_mem_roof_of_later_mem_targetPath {v x : V} {S : Set V}
    (p : Path R) (hp : IsTargetPathFrom R B v p)
    (hav : Avoids R p (S \ {p.start}))
    (hx : x ∈ p.walk.support) (hxne : x ≠ p.start) :
    x ∉ roof R B S := by
  let hm : p.walk.Meets ({x} : Set V) := ⟨x, hx, Set.mem_singleton x⟩
  let L := DirectedPath.Walk.lastHit p.walk ({x} : Set V) hm
  have hLx : L.startpoint = x := Set.mem_singleton_iff.1 L.startpoint_mem
  have hstartNotL : p.start ∉ L.walk.support := by
    intro hstart
    have heq : L.walk.support = p.walk.support :=
      List.Nodup.eq_of_head_mem_of_suffix (hne := p.walk.support_ne_nil) L.support_suffix
        (by simpa using hstart) p.isPath
    have hhead : L.startpoint = p.start := by
      have h := congrArg (fun l ↦ l[0]?) heq
      rw [getElem?_zero_support R L.walk, getElem?_zero_support R p.walk] at h
      exact Option.some.inj h
    exact hxne (hLx.symm.trans hhead)
  apply (not_mem_roof_iff R B S x).2
  let q : Path R :=
    { start := L.startpoint
      finish := p.finish
      walk := L.walk
      isPath := L.isPath p.isPath }
  refine ⟨q, ⟨hLx, hp.2⟩, ?_⟩
  intro y hyq hyS
  exact hav (L.support_subset hyq) ⟨hyS, fun hyp ↦ hstartNotL (hyp ▸ hyq)⟩

/-! ## Last-hit and essential trimming (source Lemma 2.14) -/

/-- The last `S`-vertex on a target path is essential in `S`. -/
theorem lastHit_mem_essential {v : V} (S : Set V)
    (p : Path R) (hp : IsTargetPathFrom R B v p)
    (hmeet : Meets R p S) :
    let L := DirectedPath.Walk.lastHit p.walk S hmeet
    L.startpoint ∈ essential R B S := by
  let L := DirectedPath.Walk.lastHit p.walk S hmeet
  change L.startpoint ∈ S ∧
    L.startpoint ∉ roof R B (S \ {L.startpoint})
  refine ⟨L.startpoint_mem, (not_mem_roof_iff R B _ _).2 ?_⟩
  let q : Path R :=
    { start := L.startpoint
      finish := p.finish
      walk := L.walk
      isPath := L.isPath p.isPath }
  refine ⟨q, ⟨rfl, hp.2⟩, ?_⟩
  intro x hxq hxS
  rcases (mem_support_iff_start_or_mem_tail R L.walk).1 hxq with hxeq | hxtail
  · exact hxS.2 hxeq
  · exact L.no_mem_after hxtail hxS.1

/-- Trimming to essential points does not change the roof.  This is the
roof form of Aharoni--Berger Lemma 2.14. -/
theorem roof_essential (S : Set V) :
    roof R B (essential R B S) = roof R B S := by
  apply Set.Subset.antisymm
  · exact roof_mono R B (essential_subset R B S)
  · intro v hv p hp
    have hmeet := hv p hp
    let L := DirectedPath.Walk.lastHit p.walk S hmeet
    exact ⟨L.startpoint, L.support_subset L.walk.start_mem_support,
      lastHit_mem_essential R B S p hp hmeet⟩

/-- If `X` is already roofed by `S`, then everything roofed by `X` is
roofed by `S`. -/
theorem roof_cut {X S : Set V} (hXS : X ⊆ roof R B S) :
    roof R B X ⊆ roof R B S := by
  intro v hv p hp
  have hmeet := hv p hp
  let L := DirectedPath.Walk.lastHit p.walk X hmeet
  let q : Path R :=
    { start := L.startpoint
      finish := p.finish
      walk := L.walk
      isPath := L.isPath p.isPath }
  obtain ⟨s, hsq, hsS⟩ := hXS L.startpoint_mem q ⟨rfl, hp.2⟩
  exact ⟨s, L.support_subset hsq, hsS⟩

/-! ## Source Lemmas 2.16--2.19 -/

/-- Aharoni--Berger Lemma 2.16: unless it is the terminal vertex, the last
vertex of a finite path in `roof S` is essential in `S`. -/
theorem lastRoofHit_mem_essential_or_finish (S : Set V) (p : Path R)
    (hmeet : Meets R p (roof R B S)) :
    let L := DirectedPath.Walk.lastHit p.walk (roof R B S) hmeet
    L.startpoint ∈ essential R B S ∪ {p.finish} := by
  let L := DirectedPath.Walk.lastHit p.walk (roof R B S) hmeet
  by_cases hfinish : L.startpoint = p.finish
  · exact Or.inr (Set.mem_singleton_iff.2 hfinish)
  · apply Or.inl
    obtain ⟨u, edge, tail, hL⟩ :=
      exists_cons_of_start_ne_finish R L.walk hfinish
    have huTail : u ∈ L.walk.support.tail := by simp [hL]
    have huNotRoof : u ∉ roof R B S := L.no_mem_after huTail
    obtain ⟨q, hqtarget, hqavoid⟩ :=
      (not_mem_roof_iff R B S u).1 huNotRoof
    have hstartNotQ : L.startpoint ∉ q.walk.support := by
      intro hmem
      exact (not_mem_roof_of_mem_targetPath R B q hqtarget hqavoid hmem)
        L.startpoint_mem
    let qwalk : Walk R u q.finish := castStart R hqtarget.1 q.walk
    let vq : Path R :=
      { start := L.startpoint
        finish := q.finish
        walk := .cons edge qwalk
        isPath := by
          simpa [qwalk, DirectedPath.Walk.IsPath, hstartNotQ] using q.isPath }
    have hvqTarget : IsTargetPathFrom R B L.startpoint vq :=
      ⟨rfl, hqtarget.2⟩
    obtain ⟨z, hzvq, hzS⟩ := L.startpoint_mem vq hvqTarget
    have hstartS : L.startpoint ∈ S := by
      simp only [vq, DirectedPath.Walk.support_cons, List.mem_cons] at hzvq
      exact hzvq.elim (fun h ↦ h ▸ hzS)
        (fun hzq ↦ (hqavoid (by simpa [qwalk] using hzq) hzS).elim)
    refine ⟨hstartS, (not_mem_roof_iff R B _ _).2 ⟨vq, hvqTarget, ?_⟩⟩
    intro z hzvq hzDiff
    simp only [vq, DirectedPath.Walk.support_cons, List.mem_cons] at hzvq
    exact hzvq.elim (fun h ↦ hzDiff.2 (Set.mem_singleton_iff.2 h))
      (fun hzq ↦ hqavoid (by simpa [qwalk] using hzq) hzDiff.1)

/-- Aharoni--Berger Lemma 2.17 (essential sandwich). -/
theorem essential_sandwich {C D : Set V}
    (hDC : essential R B D ⊆ C) (hCD : C ⊆ D) :
    essential R B C = essential R B D := by
  apply Set.Subset.antisymm
  · intro x hxC
    obtain ⟨p, hpTarget, hpAvoid⟩ :=
      (not_mem_roof_iff R B (C \ {x}) x).1 hxC.2
    have hmeetD : Meets R p D :=
      ⟨x, hpTarget.1 ▸ p.walk.start_mem_support, hCD hxC.1⟩
    let L := DirectedPath.Walk.lastHit p.walk D hmeetD
    have hLessC : L.startpoint ∈ C :=
      hDC (lastHit_mem_essential R B D p hpTarget hmeetD)
    have hLx : L.startpoint = x := by
      by_contra hne
      exact hpAvoid (L.support_subset L.walk.start_mem_support) ⟨hLessC, hne⟩
    have hsupport : L.walk.support = p.walk.support := by
      exact List.Nodup.eq_of_head_mem_of_suffix (hne := p.walk.support_ne_nil) L.support_suffix
        (by simpa [hpTarget.1, hLx] using L.walk.start_mem_support) p.isPath
    refine ⟨hCD hxC.1, (not_mem_roof_iff R B (D \ {x}) x).2 ⟨p, hpTarget, ?_⟩⟩
    intro y hyp hyD
    rcases (mem_support_iff_start_or_mem_tail R p.walk).1 hyp with hyeq | hytail
    · have : y = x := hyeq.trans hpTarget.1
      exact hyD.2 (Set.mem_singleton_iff.2 this)
    · apply L.no_mem_after
      · simpa [hsupport] using hytail
      · exact hyD.1
  · intro x hxD
    obtain ⟨p, hpTarget, hpAvoid⟩ :=
      (not_mem_roof_iff R B (D \ {x}) x).1 hxD.2
    refine ⟨hDC hxD, (not_mem_roof_iff R B (C \ {x}) x).2 ⟨p, hpTarget, ?_⟩⟩
    intro y hyp hyC
    exact hpAvoid hyp ⟨hCD hyC.1, hyC.2⟩

/-- Adding vertices already roofed by `U` does not change the essential
frontier of `U`. -/
theorem essential_union_eq_of_subset_roof {U Z : Set V}
    (hZ : Z ⊆ roof R B U) :
    essential R B (U ∪ Z) = essential R B U := by
  symm
  apply essential_sandwich R B (C := U) (D := U ∪ Z)
  · intro x hx
    rcases hx.1 with hxU | hxZ
    · exact hxU
    · by_contra hxU
      obtain ⟨p, hpTarget, hpAvoid⟩ :=
        (not_mem_roof_iff R B ((U ∪ Z) \ {x}) x).1 hx.2
      obtain ⟨y, hyp, hyU⟩ := hZ hxZ p hpTarget
      exact hpAvoid hyp ⟨Or.inl hyU, fun hyx ↦ hxU (hyx ▸ hyU)⟩
  · exact Set.subset_union_left

/-- Aharoni--Berger Observation 2.18 (mutual roofing). -/
theorem mutual_roofing {S T X Y : Set V} (hXY : Disjoint X Y)
    (hX : X ⊆ roof R B (T ∪ Y))
    (hY : Y ⊆ roof R B (S ∪ X)) :
    X ∪ Y ⊆ roof R B (S ∪ T) := by
  intro z hz p hp
  have hmeetXY : Meets R p (X ∪ Y) :=
    ⟨p.start, p.start_mem_support, hp.1 ▸ hz⟩
  let L := DirectedPath.Walk.lastHit p.walk (X ∪ Y) hmeetXY
  let q : Path R :=
    { start := L.startpoint
      finish := p.finish
      walk := L.walk
      isPath := L.isPath p.isPath }
  have hqTarget : IsTargetPathFrom R B L.startpoint q := ⟨rfl, hp.2⟩
  rcases L.startpoint_mem with hLX | hLY
  · obtain ⟨w, hwq, hw⟩ := hX hLX q hqTarget
    rcases hw with hwT | hwY
    · exact ⟨w, L.support_subset hwq, Or.inr hwT⟩
    · exfalso
      rcases (mem_support_iff_start_or_mem_tail R L.walk).1 hwq with h | h
      · exact Set.disjoint_left.1 hXY hLX (h ▸ hwY)
      · exact L.no_mem_after h (Or.inr hwY)
  · obtain ⟨w, hwq, hw⟩ := hY hLY q hqTarget
    rcases hw with hwS | hwX
    · exact ⟨w, L.support_subset hwq, Or.inl hwS⟩
    · exfalso
      rcases (mem_support_iff_start_or_mem_tail R L.walk).1 hwq with h | h
      · exact Set.disjoint_left.1 hXY (h ▸ hwX) hLY
      · exact L.no_mem_after h (Or.inl hwX)

/-- The equivalent essential-frontier formulation of Observation 2.18. -/
theorem essential_mutual_roofing {S T X Y : Set V} (hXY : Disjoint X Y)
    (hX : X ⊆ roof R B (T ∪ Y))
    (hY : Y ⊆ roof R B (S ∪ X)) :
    essential R B (S ∪ T ∪ X ∪ Y) = essential R B (S ∪ T) := by
  rw [show S ∪ T ∪ X ∪ Y = (S ∪ T) ∪ (X ∪ Y) by aesop]
  exact essential_union_eq_of_subset_roof R B
    (mutual_roofing R B hXY hX hY)

/-- `S` separates `R₀` from `T` when every finite directed path beginning
in `R₀` and ending in `T` meets `S`. -/
def Separates (R₀ T S : Set V) : Prop :=
  ∀ {r t : V} (p : Walk R r t),
    r ∈ R₀ → t ∈ T → p.Meets S

/-- Aharoni--Berger Lemma 2.19 (nested roofs separate). -/
theorem nested_roofs_separate {R₀ S T : Set V}
    (hT : T = essential R B T)
    (hRS : roof R B R₀ ⊆ roof R B S)
    (hST : roof R B S ⊆ roof R B T) :
    Separates R R₀ T S := by
  intro r t p hr ht
  have hrRoofS : r ∈ roof R B S := hRS (subset_roof R B R₀ hr)
  have htEss : t ∈ essential R B T := hT ▸ ht
  obtain ⟨q, hqTarget, hqAvoid⟩ :=
    (not_mem_roof_iff R B (T \ {t}) t).1 htEss.2
  by_contra hpMeet
  have hpAvoid : ∀ {x}, x ∈ p.support → x ∉ S := by
    intro x hxp hxS
    exact hpMeet ⟨x, hxp, hxS⟩
  have htNotS : t ∉ S := hpAvoid p.end_mem_support
  have hqAvoid' : Avoids R q (T \ {q.start}) := by
    intro y hyq hyT
    apply hqAvoid hyq
    exact ⟨hyT.1, fun hyt ↦ hyT.2 (hyt.trans hqTarget.1.symm)⟩
  have hqAvoidS : Avoids R q S := by
    intro x hxq hxS
    have hxRoofT : x ∈ roof R B T := hST (subset_roof R B S hxS)
    have hxne : x ≠ q.start := by
      intro hxstart
      apply htNotS
      rw [← hqTarget.1]
      exact hxstart ▸ hxS
    have hxNotRoofT := not_mem_roof_of_later_mem_targetPath R B q hqTarget
      hqAvoid' hxq hxne
    exact hxNotRoofT hxRoofT
  let qwalk : Walk R t q.finish := castStart R hqTarget.1 q.walk
  have happAvoid : ¬ (p.append qwalk).Meets S := by
    rintro ⟨x, hx, hxS⟩
    rw [DirectedPath.Walk.support_append] at hx
    simp only [qwalk, support_castStart] at hx
    rcases List.mem_append.1 hx with hxp | hxqtail
    · exact hpAvoid hxp hxS
    · exact hqAvoidS (List.mem_of_mem_tail hxqtail) hxS
  exact happAvoid (roof_meets_walk R B hrRoofS (p.append qwalk) hqTarget.2)

/-! ## Deletion and the roof identity -/

/-- Delete a set of vertices from a relation. -/
def deleteRel (X : Set V) (u v : V) : Prop :=
  R u v ∧ u ∉ X ∧ v ∉ X

/-- Forget the deletion certificate on a walk. -/
def liftDeleteWalk (X : Set V) :
    ∀ {u v : V}, Walk (deleteRel R X) u v → Walk R u v
  | _, _, .nil => .nil
  | _, _, .cons h p => .cons h.1 (liftDeleteWalk X p)

@[simp] theorem support_liftDeleteWalk (X : Set V) {u v : V}
    (p : Walk (deleteRel R X) u v) :
    (liftDeleteWalk R X p).support = p.support := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [liftDeleteWalk, ih]

/-- Every nontrivial deleted walk, and every deleted walk ending outside the
deleted set, uses only undeleted vertices. -/
theorem deleteWalk_avoids_of_finish {X : Set V} {u v : V}
    (p : Walk (deleteRel R X) u v) (hv : v ∉ X) :
    ∀ {x}, x ∈ p.support → x ∉ X := by
  induction p with
  | nil => simpa using hv
  | @cons u w v h p ih =>
      intro x hx
      simp only [DirectedPath.Walk.support_cons, List.mem_cons] at hx
      exact hx.elim (fun hxu ↦ hxu ▸ h.2.1) (fun hxp ↦ ih hv hxp)

/-- Restrict a walk whose vertices avoid `X` to the deleted relation. -/
def restrictDeleteWalk (X : Set V) :
    ∀ {u v : V} (p : Walk R u v),
      (∀ {x}, x ∈ p.support → x ∉ X) → Walk (deleteRel R X) u v
  | _, _, .nil, _ => .nil
  | _, _, .cons (v := w) h p, hav =>
      .cons ⟨h, hav (by simp), hav (by simp)⟩
        (restrictDeleteWalk X p (fun {_} hx ↦ hav (by simp [hx])))

@[simp] theorem support_restrictDeleteWalk (X : Set V) {u v : V}
    (p : Walk R u v) (hav : ∀ {x}, x ∈ p.support → x ∉ X) :
    (restrictDeleteWalk R X p hav).support = p.support := by
  induction p with
  | nil => rfl
  | cons h p ih =>
      have havp : ∀ {x}, x ∈ p.support → x ∉ X := by
        intro x hx
        exact hav (by simp [hx])
      change _ :: (restrictDeleteWalk R X p havp).support = _ :: p.support
      rw [ih havp]

/-- Roof/deletion identity:
`RFΓ(X ∪ Y) = X ∪ RF(Γ-X)(Y)`. -/
theorem roof_union_eq_union_roof_delete (X Y : Set V) :
    roof R B (X ∪ Y) =
      X ∪ roof (deleteRel R X) (B \ X) Y := by
  ext v
  by_cases hvX : v ∈ X
  · constructor
    · intro _
      exact Or.inl hvX
    · intro _
      exact subset_roof R B (X ∪ Y) (Or.inl hvX)
  · simp only [Set.mem_union, hvX, false_or]
    constructor
    · intro hv p hp
      let q : Path R :=
        { start := p.start
          finish := p.finish
          walk := liftDeleteWalk R X p.walk
          isPath := by simpa [DirectedPath.Walk.IsPath] using p.isPath }
      obtain ⟨z, hzq, hz⟩ := hv q ⟨hp.1, hp.2.1⟩
      have hzSupport : z ∈ p.walk.support := by
        simpa [q, support_liftDeleteWalk] using hzq
      rcases hz with hzX | hzY
      · exact (deleteWalk_avoids_of_finish R p.walk hp.2.2 hzSupport hzX).elim
      · exact ⟨z, hzSupport, hzY⟩
    · intro hv p hp
      by_contra hmeet
      have hpAvoid : Avoids R p (X ∪ Y) :=
        (avoids_iff_not_meets R p (X ∪ Y)).2 hmeet
      have hpAvoidX : ∀ {x}, x ∈ p.walk.support → x ∉ X :=
        fun {_} hxp hxX ↦ hpAvoid hxp (Or.inl hxX)
      let q : Path (deleteRel R X) :=
        { start := p.start
          finish := p.finish
          walk := restrictDeleteWalk R X p.walk hpAvoidX
          isPath := by simpa [DirectedPath.Walk.IsPath] using p.isPath }
      have hfinishX : p.finish ∉ X := hpAvoidX p.walk.end_mem_support
      obtain ⟨z, hzq, hzY⟩ := hv q ⟨hp.1, hp.2, hfinishX⟩
      apply hpAvoid (x := z)
      · simpa [q, support_restrictDeleteWalk] using hzq
      · exact Or.inr hzY

/-! ## Last exit -/

/-- A finite walk which meets `X` and ends outside it has a last exit.  The
statement returns the boundary edge and an `X`-avoiding suffix directly, so
it introduces no second path or web structure. -/
theorem exists_lastExit {u v : V} (p : Walk R u v) (X : Set V)
    (hmeet : p.Meets X) (hv : v ∉ X) :
    ∃ inside ∈ X, ∃ outside ∉ X,
      R inside outside ∧
      ∃ suffix : Walk R outside v,
        (∀ {x}, x ∈ suffix.support → x ∉ X) ∧
        suffix.support <:+ p.support := by
  obtain ⟨L⟩ := DirectedPath.Walk.exists_lastHit p X hmeet
  have hne : L.startpoint ≠ v := by
    intro h
    exact hv (h ▸ L.startpoint_mem)
  obtain ⟨outside, edge, suffix, hL⟩ :=
    exists_cons_of_start_ne_finish R L.walk hne
  have hout : outside ∉ X :=
    L.no_mem_after (by simp [hL])
  refine ⟨L.startpoint, L.startpoint_mem, outside, hout, edge, suffix, ?_, ?_⟩
  · intro x hx
    exact L.no_mem_after (by simpa [hL] using hx)
  · have hsuffix : suffix.support <:+ L.walk.support := by
      rw [hL]
      exact List.suffix_cons L.startpoint suffix.support
    exact hsuffix.trans L.support_suffix

end Erdos599.RelationalRoof
