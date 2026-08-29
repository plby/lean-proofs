/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Set.Card

/-!
# Erdős Problem 599: basic undirected definitions

This file gives the public `SimpleGraph` formulation of the Erdős--Menger
theorem.  It deliberately places no finiteness or decidability assumption on
the vertex type.
-/

namespace Erdos599

open SimpleGraph

universe u

/-- A finite simple path whose initial vertex lies in `A` and whose terminal
vertex lies in `B`.  The orientation only records which endpoint is in which
set; the ambient graph is undirected. -/
structure ABPath {V : Type u} (G : SimpleGraph V) (A B : Set V) where
  start : V
  finish : V
  walk : G.Walk start finish
  isPath : walk.IsPath
  start_mem : start ∈ A
  finish_mem : finish ∈ B

namespace ABPath

/-- The set of vertices visited by an `A`–`B` path. -/
def supportSet {V : Type u} {G : SimpleGraph V} {A B : Set V}
    (p : ABPath G A B) : Set V :=
  {v | v ∈ p.walk.support}

@[simp]
theorem mem_supportSet {V : Type u} {G : SimpleGraph V} {A B : Set V}
    (p : ABPath G A B) (v : V) :
    v ∈ p.supportSet ↔ v ∈ p.walk.support :=
  Iff.rfl

@[simp]
theorem start_mem_supportSet {V : Type u} {G : SimpleGraph V} {A B : Set V}
    (p : ABPath G A B) : p.start ∈ p.supportSet :=
  p.walk.start_mem_support

@[simp]
theorem finish_mem_supportSet {V : Type u} {G : SimpleGraph V} {A B : Set V}
    (p : ABPath G A B) : p.finish ∈ p.supportSet :=
  p.walk.end_mem_support

/-- A path support is finite even when the ambient graph is infinite. -/
theorem supportSet_finite {V : Type u} {G : SimpleGraph V} {A B : Set V}
    (p : ABPath G A B) : p.supportSet.Finite := by
  exact p.walk.support.finite_toSet

/-- Since an `ABPath` is simple, its number of vertices is the length of its
walk plus one. -/
theorem ncard_supportSet {V : Type u} {G : SimpleGraph V} {A B : Set V}
    (p : ABPath G A B) : p.supportSet.ncard = p.walk.length + 1 := by
  classical
  rw [Set.ncard_eq_toFinset_card _ p.supportSet_finite]
  have hto : p.supportSet_finite.toFinset = p.walk.support.toFinset := by
    ext v
    simp [supportSet]
  rw [hto]
  rw [List.toFinset_card_of_nodup p.isPath.support_nodup]
  exact p.walk.length_support

/-- Intersecting an arbitrary set with a path support is still finite. -/
theorem inter_supportSet_finite {V : Type u} {G : SimpleGraph V} {A B : Set V}
    (p : ABPath G A B) (S : Set V) : (S ∩ p.supportSet).Finite :=
  p.supportSet_finite.subset Set.inter_subset_right

/-- Disjoint endpoint sets rule out length-zero `A`–`B` paths. -/
theorem start_ne_finish {V : Type u} {G : SimpleGraph V} {A B : Set V}
    (hAB : Disjoint A B) (p : ABPath G A B) : p.start ≠ p.finish := by
  intro h
  exact Set.disjoint_left.1 hAB p.start_mem (h ▸ p.finish_mem)

/-- Disjoint endpoint sets rule out nil `A`–`B` walks. -/
theorem not_nil {V : Type u} {G : SimpleGraph V} {A B : Set V}
    (hAB : Disjoint A B) (p : ABPath G A B) : ¬ p.walk.Nil := by
  intro hp
  exact p.start_ne_finish hAB hp.eq

end ABPath

/-- A set-indexed family of pairwise vertex-disjoint `A`–`B` paths. -/
def IsPathPacking {V : Type u} {G : SimpleGraph V} {A B : Set V}
    (P : Set (ABPath G A B)) : Prop :=
  P.PairwiseDisjoint ABPath.supportSet

/-- A set of vertices meeting every finite simple `A`–`B` path. -/
def IsABSeparator {V : Type u} (G : SimpleGraph V) (A B S : Set V) : Prop :=
  ∀ q : ABPath G A B, ∃ v : V, v ∈ S ∧ v ∈ q.supportSet

/-- `S` consists of exactly one selected vertex from every path in `P`.
The first conjunct excludes extraneous vertices of `S` lying on no selected
path. -/
def IsOrthogonal {V : Type u} {G : SimpleGraph V} {A B : Set V}
    (P : Set (ABPath G A B)) (S : Set V) : Prop :=
  S ⊆ ⋃ p ∈ P, p.supportSet ∧
    ∀ p ∈ P, ∃! v : V, v ∈ S ∧ v ∈ p.supportSet

theorem IsPathPacking.disjoint {V : Type u} {G : SimpleGraph V} {A B : Set V}
    {P : Set (ABPath G A B)} (hP : IsPathPacking P)
    {p q : ABPath G A B} (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q) :
    Disjoint p.supportSet q.supportSet :=
  hP hp hq hpq

/-- Two packed paths sharing a vertex are equal. -/
theorem IsPathPacking.eq_of_mem_supportSet {V : Type u}
    {G : SimpleGraph V} {A B : Set V} {P : Set (ABPath G A B)}
    (hP : IsPathPacking P) {p q : ABPath G A B} (hp : p ∈ P) (hq : q ∈ P)
    {v : V} (hvp : v ∈ p.supportSet) (hvq : v ∈ q.supportSet) : p = q := by
  by_contra hpq
  exact Set.disjoint_left.1 (hP.disjoint hp hq hpq) hvp hvq

theorem IsOrthogonal.subset_iUnion {V : Type u} {G : SimpleGraph V}
    {A B : Set V} {P : Set (ABPath G A B)} {S : Set V}
    (h : IsOrthogonal P S) : S ⊆ ⋃ p ∈ P, p.supportSet :=
  h.1

theorem IsOrthogonal.existsUnique {V : Type u} {G : SimpleGraph V}
    {A B : Set V} {P : Set (ABPath G A B)} {S : Set V}
    (h : IsOrthogonal P S) {p : ABPath G A B} (hp : p ∈ P) :
    ∃! v : V, v ∈ S ∧ v ∈ p.supportSet :=
  h.2 p hp

/-- Cardinality one of the intersection is exactly unique choice on a path. -/
theorem ncard_inter_supportSet_eq_one_iff {V : Type u} {G : SimpleGraph V}
    {A B : Set V} (S : Set V) (p : ABPath G A B) :
    (S ∩ p.supportSet).ncard = 1 ↔
      ∃! v : V, v ∈ S ∧ v ∈ p.supportSet := by
  rw [Set.ncard_eq_one]
  constructor
  · rintro ⟨v, hv⟩
    have hv_mem : v ∈ S ∩ p.supportSet := by
      rw [hv]
      simp
    refine ⟨v, hv_mem, ?_⟩
    intro w hw
    have : w ∈ ({v} : Set V) := by
      rw [← hv]
      exact hw
    simpa using this
  · rintro ⟨v, hv, huniq⟩
    refine ⟨v, Set.ext ?_⟩
    intro w
    constructor
    · intro hw
      exact Set.mem_singleton_iff.mpr (huniq w hw)
    · intro hw
      have hwv : w = v := Set.mem_singleton_iff.mp hw
      simpa [hwv] using hv

/-- The direct unique-choice definition of orthogonality is equivalent to
the usual `ncard = 1` formulation. -/
theorem isOrthogonal_iff_ncard {V : Type u} {G : SimpleGraph V}
    {A B : Set V} (P : Set (ABPath G A B)) (S : Set V) :
    IsOrthogonal P S ↔
      S ⊆ ⋃ p ∈ P, p.supportSet ∧
        ∀ p ∈ P, (S ∩ p.supportSet).ncard = 1 := by
  simp only [IsOrthogonal, ncard_inter_supportSet_eq_one_iff]

/-- A selector respecting pairwise disjoint supports is injective. -/
theorem selector_injective_of_isPathPacking {V : Type u} {G : SimpleGraph V}
    {A B : Set V} {P : Set (ABPath G A B)} (hP : IsPathPacking P)
    {c : P → V} (hc : ∀ p : P, c p ∈ p.1.supportSet) : Function.Injective c := by
  intro p q hpq
  apply Subtype.ext
  exact hP.eq_of_mem_supportSet p.2 q.2 (hpq ▸ hc p) (hc q)

/-- For a path packing, orthogonality says precisely that `S` is the range
of a choice of one vertex on each path. -/
theorem isOrthogonal_iff_exists_selector {V : Type u} {G : SimpleGraph V}
    {A B : Set V} {P : Set (ABPath G A B)} (hP : IsPathPacking P) (S : Set V) :
    IsOrthogonal P S ↔
      ∃ c : P → V, (∀ p : P, c p ∈ p.1.supportSet) ∧ S = Set.range c := by
  classical
  constructor
  · intro h
    let c : P → V := fun p ↦ (h.existsUnique p.2).exists.choose
    have hc : ∀ p : P, c p ∈ S ∧ c p ∈ p.1.supportSet := fun p ↦
      (h.existsUnique p.2).exists.choose_spec
    refine ⟨c, fun p ↦ (hc p).2, Set.Subset.antisymm ?_ ?_⟩
    · intro v hv
      have hv_union := h.subset_iUnion hv
      simp only [Set.mem_iUnion] at hv_union
      obtain ⟨p, hp, hvp⟩ := hv_union
      let p' : P := ⟨p, hp⟩
      have hcv : c p' = v := (h.existsUnique hp).unique (hc p') ⟨hv, hvp⟩
      exact ⟨p', hcv⟩
    · rintro v ⟨p, rfl⟩
      exact (hc p).1
  · rintro ⟨c, hc, rfl⟩
    constructor
    · rintro v ⟨p, rfl⟩
      simp only [Set.mem_iUnion]
      exact ⟨p.1, p.2, hc p⟩
    · intro p hp
      let p' : P := ⟨p, hp⟩
      refine ⟨c p', ⟨⟨p', rfl⟩, hc p'⟩, ?_⟩
      intro v hv
      obtain ⟨q, hq⟩ := hv.1
      have hcommon : c q ∈ p.supportSet := by
        rw [hq]
        exact hv.2
      have hpaths : q.1 = p :=
        hP.eq_of_mem_supportSet q.2 p'.2 (hc q) hcommon
      have hqp : q = p' := Subtype.ext hpaths
      calc
        v = c q := hq.symm
        _ = c p' := congrArg c hqp

end Erdos599
