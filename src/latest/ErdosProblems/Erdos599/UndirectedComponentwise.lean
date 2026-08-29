/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UndirectedFiniteEndpoint
import ErdosProblems.Erdos599.AlternatingComponents
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Componentwise assembly for the undirected Erdős--Menger theorem

The directed cardinal induction treats the whole source at once.  In an
undirected graph there is an additional decomposition which is unavailable
in a genuinely directed web: distinct connected components do not interact.
This file proves the exact gluing theorem and combines it with the countable
endpoint theorem.

Consequently the endpoint set may be globally uncountable.  It is enough
that its intersection with each connected component be countable.  For
example, an arbitrary disjoint union of graphs with countable left endpoint
sets satisfies the full Erdős--Menger conclusion.
-/

noncomputable section

namespace Erdos599
namespace UndirectedComponentwise

open Set SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V} {A B : Set V}

/-- Regard a path whose endpoints lie in one component as a path for the
ambient endpoint sets. -/
def liftPath (c : G.ConnectedComponent)
    (p : ABPath G (A ∩ c.supp) (B ∩ c.supp)) : ABPath G A B where
  start := p.start
  finish := p.finish
  walk := p.walk
  isPath := p.isPath
  start_mem := p.start_mem.1
  finish_mem := p.finish_mem.1

@[simp]
theorem supportSet_liftPath (c : G.ConnectedComponent)
    (p : ABPath G (A ∩ c.supp) (B ∩ c.supp)) :
    (liftPath c p).supportSet = p.supportSet :=
  rfl

theorem liftPath_injective (c : G.ConnectedComponent) :
    Function.Injective
      (liftPath (A := A) (B := B) c) := by
  intro p q hpq
  cases p
  cases q
  simp only [liftPath] at hpq
  cases hpq
  rfl

/-- Every vertex of a walk lies in any connected component containing its
initial vertex. -/
private theorem walk_support_subset_component
    (c : G.ConnectedComponent) {x y : V} (p : G.Walk x y)
    (hx : x ∈ c.supp) : {v | v ∈ p.support} ⊆ c.supp := by
  induction p with
  | nil => simpa
  | @cons x z y hxz p ih =>
      intro v hv
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact hx
      · exact ih ((c.mem_supp_congr_adj hxz).mp hx) hv

/-- A path beginning in a connected component stays in that component. -/
theorem supportSet_subset_component (c : G.ConnectedComponent)
    (p : ABPath G A B) (hp : p.start ∈ c.supp) :
    p.supportSet ⊆ c.supp :=
  walk_support_subset_component c p.walk hp

/-- Reinterpret a global path as a path between the endpoint slices in the
component of its initial vertex. -/
def localizePath (p : ABPath G A B) :
    ABPath G
      (A ∩ (G.connectedComponentMk p.start).supp)
      (B ∩ (G.connectedComponentMk p.start).supp) where
  start := p.start
  finish := p.finish
  walk := p.walk
  isPath := p.isPath
  start_mem := ⟨p.start_mem, ConnectedComponent.connectedComponentMk_mem⟩
  finish_mem := ⟨p.finish_mem,
    supportSet_subset_component (G.connectedComponentMk p.start) p
      ConnectedComponent.connectedComponentMk_mem p.finish_mem_supportSet⟩

@[simp]
theorem supportSet_localizePath (p : ABPath G A B) :
    (localizePath p).supportSet = p.supportSet :=
  rfl

@[simp]
theorem liftPath_localizePath (p : ABPath G A B) :
    liftPath (G.connectedComponentMk p.start) (localizePath p) = p := by
  cases p
  rfl

/-- If the exact Erdős--Menger conclusion is available separately in every
connected component, the component witnesses glue to an exact global
witness.  The local paths are still paths in `G`; only their endpoint sets
are restricted to the component support. -/
theorem assemble
    (hlocal : ∀ c : G.ConnectedComponent,
      ∃ (P : Set (ABPath G (A ∩ c.supp) (B ∩ c.supp))) (S : Set V),
        IsPathPacking P ∧ IsABSeparator G (A ∩ c.supp) (B ∩ c.supp) S ∧
          IsOrthogonal P S) :
    ∃ (P : Set (ABPath G A B)) (S : Set V),
      IsPathPacking P ∧ IsABSeparator G A B S ∧ IsOrthogonal P S := by
  classical
  choose P S hP hsep horth using hlocal
  let P' : Set (ABPath G A B) :=
    ⋃ c : G.ConnectedComponent, liftPath c '' P c
  let S' : Set V := ⋃ c : G.ConnectedComponent, S c
  have hS_component : ∀ c : G.ConnectedComponent, S c ⊆ c.supp := by
    intro c v hv
    have hvU := (horth c).1 hv
    simp only [Set.mem_iUnion] at hvU
    obtain ⟨p, hp, hvp⟩ := hvU
    exact supportSet_subset_component c p p.start_mem.2 hvp
  refine ⟨P', S', ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    simp only [P', Set.mem_iUnion] at hp hq
    obtain ⟨c, p₀, hp₀, rfl⟩ := hp
    obtain ⟨d, q₀, hq₀, rfl⟩ := hq
    by_cases hcd : c = d
    · subst d
      change Disjoint (liftPath c p₀).supportSet (liftPath c q₀).supportSet
      rw [supportSet_liftPath, supportSet_liftPath]
      apply hP c hp₀ hq₀
      intro hp₀q₀
      apply hpq
      exact congrArg (liftPath c) hp₀q₀
    · apply Set.disjoint_of_subset
        (supportSet_subset_component c (liftPath c p₀) p₀.start_mem.2)
        (supportSet_subset_component d (liftPath d q₀) q₀.start_mem.2)
      exact SimpleGraph.pairwise_disjoint_supp_connectedComponent G hcd
  · intro q
    let c : G.ConnectedComponent := G.connectedComponentMk q.start
    obtain ⟨v, hvS, hvq⟩ := hsep c (localizePath q)
    exact ⟨v, Set.mem_iUnion.2 ⟨c, hvS⟩, by simpa using hvq⟩
  · constructor
    · intro v hv
      simp only [S', Set.mem_iUnion] at hv
      obtain ⟨c, hvc⟩ := hv
      have hvU := (horth c).1 hvc
      simp only [Set.mem_iUnion] at hvU ⊢
      obtain ⟨p, hp, hvp⟩ := hvU
      refine ⟨liftPath c p, ?_, by simpa using hvp⟩
      exact Set.mem_iUnion.2 ⟨c, ⟨p, hp, rfl⟩⟩
    · intro p hp
      simp only [P', Set.mem_iUnion] at hp
      obtain ⟨c, p₀, hp₀, rfl⟩ := hp
      obtain ⟨v, hv, huniq⟩ := (horth c).2 p₀ hp₀
      refine ⟨v, ⟨Set.mem_iUnion.2 ⟨c, hv.1⟩, by simpa using hv.2⟩, ?_⟩
      intro w hw
      simp only [S', Set.mem_iUnion] at hw
      obtain ⟨d, hwd⟩ := hw.1
      have hwc : w ∈ c.supp :=
        supportSet_subset_component c (liftPath c p₀) p₀.start_mem.2 hw.2
      have hwdc : d = c :=
        ConnectedComponent.eq_of_common_vertex (hS_component d hwd) hwc
      subst d
      apply huniq w
      exact ⟨hwd, by simpa using hw.2⟩

/-- Exact Erdős--Menger for graphs whose left endpoint set is countable in
each connected component.  There may be arbitrarily many components, so the
whole endpoint set can have arbitrary cardinality. -/
theorem erdos_599_of_componentwise_left_countable
    (G : SimpleGraph V) (A B : Set V)
    (hcount : ∀ c : G.ConnectedComponent, (A ∩ c.supp).Countable) :
    ∃ (P : Set (ABPath G A B)) (S : Set V),
      IsPathPacking P ∧ IsABSeparator G A B S ∧ IsOrthogonal P S := by
  apply assemble
  intro c
  exact UndirectedFiniteEndpoint.erdos_599_of_left_countable
    G (A ∩ c.supp) (B ∩ c.supp) (hcount c)

/-- Right-endpoint version of the componentwise countability theorem. -/
theorem erdos_599_of_componentwise_right_countable
    (G : SimpleGraph V) (A B : Set V)
    (hcount : ∀ c : G.ConnectedComponent, (B ∩ c.supp).Countable) :
    ∃ (P : Set (ABPath G A B)) (S : Set V),
      IsPathPacking P ∧ IsABSeparator G A B S ∧ IsOrthogonal P S := by
  exact UndirectedFiniteEndpoint.conclusion_symm
    (erdos_599_of_componentwise_left_countable G B A hcount)

/-- A graph with countable neighborhoods has countable connected
components. -/
theorem connectedComponent_countable_of_neighborSet_countable
    (G : SimpleGraph V) (hneighbors : ∀ v, (G.neighborSet v).Countable)
    (c : G.ConnectedComponent) : c.supp.Countable := by
  refine c.ind ?_
  intro root
  have hreach :
      {v | Relation.ReflTransGen G.Adj root v}.Countable :=
    AlternatingComponents.countable_reflTransGen_of_countable_neighbors
      (fun v ↦ by simpa [SimpleGraph.neighborSet] using hneighbors v) root
  apply hreach.mono
  intro v hv
  rw [ConnectedComponent.mem_supp_iff] at hv
  exact (G.reachable_iff_reflTransGen root v).1
    (ConnectedComponent.exact hv.symm)

/-- Exact Erdős--Menger for every locally countable graph.  Neither endpoint
set nor the set of connected components is required to be countable. -/
theorem erdos_599_of_neighborSet_countable
    (G : SimpleGraph V) (A B : Set V)
    (hneighbors : ∀ v, (G.neighborSet v).Countable) :
    ∃ (P : Set (ABPath G A B)) (S : Set V),
      IsPathPacking P ∧ IsABSeparator G A B S ∧ IsOrthogonal P S := by
  apply erdos_599_of_componentwise_left_countable
  intro c
  exact (connectedComponent_countable_of_neighborSet_countable
    G hneighbors c).mono Set.inter_subset_right

/-- In particular, the exact theorem holds for every locally finite graph,
with no global cardinality restriction. -/
theorem erdos_599_of_neighborSet_finite
    (G : SimpleGraph V) (A B : Set V)
    (hneighbors : ∀ v, (G.neighborSet v).Finite) :
    ∃ (P : Set (ABPath G A B)) (S : Set V),
      IsPathPacking P ∧ IsABSeparator G A B S ∧ IsOrthogonal P S :=
  erdos_599_of_neighborSet_countable G A B
    (fun v ↦ (hneighbors v).countable)

#print axioms assemble
#print axioms erdos_599_of_componentwise_left_countable
#print axioms erdos_599_of_componentwise_right_countable
#print axioms erdos_599_of_neighborSet_countable
#print axioms erdos_599_of_neighborSet_finite

end UndirectedComponentwise
end Erdos599
