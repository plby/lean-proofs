/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Set.Card

open SimpleGraph

universe u

namespace Erdos599

/-- A finite simple path from a vertex in `A` to a vertex in `B`. -/
structure ABPath {V : Type u} (G : SimpleGraph V) (A B : Set V) where
  start : V
  finish : V
  walk : G.Walk start finish
  isPath : walk.IsPath
  start_mem : start ∈ A
  finish_mem : finish ∈ B

namespace ABPath

/-- The vertices visited by the path. -/
def supportSet {V : Type u} {G : SimpleGraph V} {A B : Set V}
    (p : ABPath G A B) : Set V :=
  {v | v ∈ p.walk.support}

end ABPath

/-- Pairwise vertex-disjoint paths. -/
def IsPathPacking {V : Type u} {G : SimpleGraph V} {A B : Set V}
    (P : Set (ABPath G A B)) : Prop :=
  P.PairwiseDisjoint ABPath.supportSet

/-- A set of vertices meeting every finite simple path from `A` to `B`. -/
def IsABSeparator {V : Type u} (G : SimpleGraph V) (A B S : Set V) : Prop :=
  ∀ q : ABPath G A B, ∃ v : V, v ∈ S ∧ v ∈ q.supportSet

/-- The separator contains exactly one vertex from each selected path,
and no vertices outside the selected paths. -/
def IsOrthogonal {V : Type u} {G : SimpleGraph V} {A B : Set V}
    (P : Set (ABPath G A B)) (S : Set V) : Prop :=
  S ⊆ ⋃ p ∈ P, p.supportSet ∧
    ∀ p ∈ P, ∃! v : V, v ∈ S ∧ v ∈ p.supportSet

end Erdos599
