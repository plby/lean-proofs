/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Basic
import ErdosProblems.Erdos599.DirectedPath

/-!
# Erdős Problem 599: the directed-to-undirected bridge

This file states the exact directed conclusion needed from the
Aharoni--Berger argument and transfers it to the public `SimpleGraph`
formulation in `Basic.lean`.  The directed theorem is always a parameter of
the reduction theorem; no unproved global declaration is introduced here.
-/

namespace Erdos599

open SimpleGraph

universe u

namespace Bridge

open DirectedPath

variable {V : Type u}

/-! ## Bidirected walks -/

/-- Regard an undirected walk as a directed walk in the bidirected graph. -/
def toDirectedWalk (G : SimpleGraph V) :
    {u v : V} → G.Walk u v → DirectedPath.Walk (DirectedPath.bidirect G) u v
  | _, _, .nil => .nil
  | _, _, .cons h p => .cons h (toDirectedWalk G p)

/-- Forget the directions in a walk in a bidirected graph. -/
def toUndirectedWalk (G : SimpleGraph V) :
    {u v : V} → DirectedPath.Walk (DirectedPath.bidirect G) u v → G.Walk u v
  | _, _, .nil => .nil
  | _, _, .cons h p => .cons h (toUndirectedWalk G p)

@[simp]
theorem support_toDirectedWalk (G : SimpleGraph V) {u v : V} (p : G.Walk u v) :
    (toDirectedWalk G p).support = p.support := by
  induction p with
  | nil => rfl
  | cons h p ih =>
      change _ :: (toDirectedWalk G p).support = _ :: p.support
      rw [ih]

@[simp]
theorem support_toUndirectedWalk (G : SimpleGraph V) {u v : V}
    (p : DirectedPath.Walk (DirectedPath.bidirect G) u v) :
    (toUndirectedWalk G p).support = p.support := by
  induction p with
  | nil => rfl
  | cons h p ih =>
      change _ :: (toUndirectedWalk G p).support = _ :: p.support
      rw [ih]

@[simp]
theorem toUndirectedWalk_toDirectedWalk (G : SimpleGraph V) {u v : V}
    (p : G.Walk u v) : toUndirectedWalk G (toDirectedWalk G p) = p := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [toDirectedWalk, toUndirectedWalk, ih]

@[simp]
theorem toDirectedWalk_toUndirectedWalk (G : SimpleGraph V) {u v : V}
    (p : DirectedPath.Walk (DirectedPath.bidirect G) u v) :
    toDirectedWalk G (toUndirectedWalk G p) = p := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [toDirectedWalk, toUndirectedWalk, ih]

/-! ## Bundled directed `A`–`B` paths -/

/-- A bundled finite simple directed path starting in `A` and ending in `B`. -/
structure DirectedABPath (D : Digraph V) (A B : Set V) where
  path : DirectedPath.FinitePath D
  start_mem : path.start ∈ A
  finish_mem : path.finish ∈ B

namespace DirectedABPath

/-- The vertex set of a bundled directed `A`–`B` path. -/
def supportSet {D : Digraph V} {A B : Set V} (p : DirectedABPath D A B) : Set V :=
  p.path.support

@[simp]
theorem mem_supportSet {D : Digraph V} {A B : Set V}
    (p : DirectedABPath D A B) (v : V) :
    v ∈ p.supportSet ↔ v ∈ p.path.walk.support :=
  Iff.rfl

@[simp]
theorem start_mem_supportSet {D : Digraph V} {A B : Set V}
    (p : DirectedABPath D A B) : p.path.start ∈ p.supportSet :=
  p.path.start_mem_support

@[simp]
theorem finish_mem_supportSet {D : Digraph V} {A B : Set V}
    (p : DirectedABPath D A B) : p.path.finish ∈ p.supportSet :=
  p.path.finish_mem_support

/-- Direct an undirected `A`–`B` path in the bidirected graph. -/
def ofUndirected {G : SimpleGraph V} {A B : Set V}
    (p : ABPath G A B) : DirectedABPath (DirectedPath.bidirect G) A B where
  path := {
    start := p.start
    finish := p.finish
    walk := toDirectedWalk G p.walk
    isPath := by
      rw [DirectedPath.Walk.isPath_iff, support_toDirectedWalk]
      exact p.isPath.support_nodup }
  start_mem := p.start_mem
  finish_mem := p.finish_mem

/-- Forget directions in an `A`–`B` path in a bidirected graph. -/
def toUndirected {G : SimpleGraph V} {A B : Set V}
    (p : DirectedABPath (DirectedPath.bidirect G) A B) : ABPath G A B where
  start := p.path.start
  finish := p.path.finish
  walk := toUndirectedWalk G p.path.walk
  isPath := by
    apply SimpleGraph.Walk.IsPath.mk'
    rw [support_toUndirectedWalk]
    exact p.path.isPath
  start_mem := p.start_mem
  finish_mem := p.finish_mem

@[simp]
theorem supportSet_ofUndirected {G : SimpleGraph V} {A B : Set V}
    (p : ABPath G A B) : (ofUndirected p).supportSet = p.supportSet := by
  ext v
  change v ∈ (toDirectedWalk G p.walk).support ↔ v ∈ p.walk.support
  rw [support_toDirectedWalk]

@[simp]
theorem supportSet_toUndirected {G : SimpleGraph V} {A B : Set V}
    (p : DirectedABPath (DirectedPath.bidirect G) A B) :
    p.toUndirected.supportSet = p.supportSet := by
  ext v
  change v ∈ (toUndirectedWalk G p.path.walk).support ↔ v ∈ p.path.walk.support
  rw [support_toUndirectedWalk]

@[simp]
theorem toUndirected_ofUndirected {G : SimpleGraph V} {A B : Set V}
    (p : ABPath G A B) : (ofUndirected p).toUndirected = p := by
  cases p
  simp [ofUndirected, toUndirected]

@[simp]
theorem ofUndirected_toUndirected {G : SimpleGraph V} {A B : Set V}
    (p : DirectedABPath (DirectedPath.bidirect G) A B) :
    ofUndirected p.toUndirected = p := by
  rcases p with ⟨⟨start, finish, walk, isPath⟩, start_mem, finish_mem⟩
  simp [ofUndirected, toUndirected]

/-- Directed and undirected `A`–`B` paths in a bidirected graph are equivalent. -/
def bidirectEquiv (G : SimpleGraph V) (A B : Set V) :
    DirectedABPath (DirectedPath.bidirect G) A B ≃ ABPath G A B where
  toFun := toUndirected
  invFun := ofUndirected
  left_inv := ofUndirected_toUndirected
  right_inv := toUndirected_ofUndirected

end DirectedABPath

/-! ## The exact directed conclusion -/

/-- Pairwise vertex-disjointness for a set of directed `A`–`B` paths. -/
def DirectedIsPathPacking {D : Digraph V} {A B : Set V}
    (P : Set (DirectedABPath D A B)) : Prop :=
  P.PairwiseDisjoint DirectedABPath.supportSet

/-- A vertex set meeting every finite simple directed `A`–`B` path. -/
def DirectedIsABSeparator (D : Digraph V) (A B S : Set V) : Prop :=
  ∀ q : DirectedABPath D A B, ∃ v : V, v ∈ S ∧ v ∈ q.supportSet

/-- A set consisting of exactly one chosen vertex from each directed path. -/
def DirectedIsOrthogonal {D : Digraph V} {A B : Set V}
    (P : Set (DirectedABPath D A B)) (S : Set V) : Prop :=
  S ⊆ ⋃ p ∈ P, p.supportSet ∧
    ∀ p ∈ P, ∃! v : V, v ∈ S ∧ v ∈ p.supportSet

/-- The exact conclusion of the directed Aharoni--Berger theorem. -/
def DirectedMengerConclusion (D : Digraph V) (A B : Set V) : Prop :=
  ∃ (P : Set (DirectedABPath D A B)) (S : Set V),
    DirectedIsPathPacking P ∧ DirectedIsABSeparator D A B S ∧
      DirectedIsOrthogonal P S

/-! ## Transfer of the directed conclusion -/

/-- Forget the directions in every member of a directed path family. -/
def undirectFamily {G : SimpleGraph V} {A B : Set V}
    (P : Set (DirectedABPath (DirectedPath.bidirect G) A B)) : Set (ABPath G A B) :=
  DirectedABPath.toUndirected '' P

theorem isPathPacking_undirectFamily {G : SimpleGraph V} {A B : Set V}
    {P : Set (DirectedABPath (DirectedPath.bidirect G) A B)}
    (hP : DirectedIsPathPacking P) : IsPathPacking (undirectFamily P) := by
  intro p hp q hq hpq
  rcases hp with ⟨p', hp', rfl⟩
  rcases hq with ⟨q', hq', rfl⟩
  have hpq' : p' ≠ q' := by
    intro h
    exact hpq (congrArg DirectedABPath.toUndirected h)
  change Disjoint p'.toUndirected.supportSet q'.toUndirected.supportSet
  rw [DirectedABPath.supportSet_toUndirected, DirectedABPath.supportSet_toUndirected]
  exact hP hp' hq' hpq'

theorem isABSeparator_of_directed {G : SimpleGraph V} {A B S : Set V}
    (hS : DirectedIsABSeparator (DirectedPath.bidirect G) A B S) :
    IsABSeparator G A B S := by
  intro q
  obtain ⟨v, hvS, hvq⟩ := hS (DirectedABPath.ofUndirected q)
  exact ⟨v, hvS, by simpa using hvq⟩

theorem isOrthogonal_undirectFamily {G : SimpleGraph V} {A B S : Set V}
    {P : Set (DirectedABPath (DirectedPath.bidirect G) A B)}
    (hS : DirectedIsOrthogonal P S) : IsOrthogonal (undirectFamily P) S := by
  constructor
  · intro v hv
    have hv' := hS.1 hv
    simp only [Set.mem_iUnion] at hv' ⊢
    obtain ⟨p, hp, hvp⟩ := hv'
    exact ⟨p.toUndirected, ⟨p, hp, rfl⟩, by simpa using hvp⟩
  · intro p hp
    obtain ⟨p', hp', rfl⟩ := hp
    obtain ⟨v, hv, huniq⟩ := hS.2 p' hp'
    refine ⟨v, by simpa using hv, ?_⟩
    intro w hw
    apply huniq w
    simpa using hw

/-- The exact directed conclusion for the bidirected graph implies the
public undirected conclusion. -/
theorem exists_orthogonal_pathPacking_of_directed
    {G : SimpleGraph V} {A B : Set V}
    (h : DirectedMengerConclusion (DirectedPath.bidirect G) A B) :
    ∃ (P : Set (ABPath G A B)) (S : Set V),
      IsPathPacking P ∧ IsABSeparator G A B S ∧ IsOrthogonal P S := by
  obtain ⟨P, S, hP, hsep, horth⟩ := h
  exact ⟨undirectFamily P, S, isPathPacking_undirectFamily hP,
    isABSeparator_of_directed hsep, isOrthogonal_undirectFamily horth⟩

/-- Any theorem proving the exact directed Aharoni--Berger conclusion for
all digraphs proves Erdős Problem 599 for simple undirected graphs.  The
independence and disjointness hypotheses belong to the public problem but
are unnecessary for the stronger directed theorem. -/
theorem erdos_599_of_directed_menger
    (directedMenger : ∀ {W : Type u} (D : Digraph W) (A B : Set W),
      DirectedMengerConclusion D A B)
    {V : Type u} (G : SimpleGraph V) (A B : Set V)
    (_hAB : Disjoint A B) (_hA : G.IsIndepSet A) (_hB : G.IsIndepSet B) :
    ∃ (P : Set (ABPath G A B)) (S : Set V),
      IsPathPacking P ∧ IsABSeparator G A B S ∧ IsOrthogonal P S :=
  exists_orthogonal_pathPacking_of_directed
    (directedMenger (DirectedPath.bidirect G) A B)

end Bridge

end Erdos599
