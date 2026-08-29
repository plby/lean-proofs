/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DirectedEndpointDuality
import Mathlib.Combinatorics.Digraph.Orientation
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Weak-component assembly for exact directed Menger pairs

A directed path stays in one connected component of the undirected graph
obtained by forgetting edge orientations.  Consequently exact directed
Menger pairs constructed independently in those weak components glue
without interactions.  Combining this with source--target duality proves
the directed conclusion whenever, in every weak component, at least one of
the two endpoint slices is countable.
-/

noncomputable section

namespace Erdos599
namespace DirectedComponentwise

open Set DirectedPath SimpleGraph

universe u

variable {V : Type u} {D : Digraph V} {A B : Set V}

/-- The simple graph obtained by forgetting the orientations of all
non-loop directed edges. -/
abbrev WeakGraph (D : Digraph V) : SimpleGraph V :=
  D.toSimpleGraphInclusive

/-- Regard a directed path whose endpoints lie in one weak component as a
path for the ambient endpoint sets. -/
def liftPath (c : (WeakGraph D).ConnectedComponent)
    (p : Bridge.DirectedABPath D (A ∩ c.supp) (B ∩ c.supp)) :
    Bridge.DirectedABPath D A B where
  path := p.path
  start_mem := p.start_mem.1
  finish_mem := p.finish_mem.1

@[simp]
theorem supportSet_liftPath (c : (WeakGraph D).ConnectedComponent)
    (p : Bridge.DirectedABPath D (A ∩ c.supp) (B ∩ c.supp)) :
    (liftPath c p).supportSet = p.supportSet :=
  rfl

theorem liftPath_injective (c : (WeakGraph D).ConnectedComponent) :
    Function.Injective (liftPath (A := A) (B := B) c) := by
  intro p q hpq
  cases p
  cases q
  simp only [liftPath] at hpq
  cases hpq
  rfl

/-- Every vertex of a simple directed walk lies in any weak component
containing its initial vertex.  Simplicity excludes directed loop steps,
which disappear when passing to `WeakGraph`. -/
private theorem walk_support_subset_component
    (c : (WeakGraph D).ConnectedComponent) {x y : V}
    (p : Walk D x y) (hp : p.IsPath) (hx : x ∈ c.supp) :
    {v | v ∈ p.support} ⊆ c.supp := by
  induction p with
  | nil => simpa
  | @cons x z y hxz p ih =>
      have hnodup : (x :: p.support).Nodup := hp
      have hxne : x ≠ z := by
        intro heq
        exact (List.pairwise_cons.mp hnodup).1 z
          p.start_mem_support heq
      have hweak : (WeakGraph D).Adj x z :=
        ⟨hxne, Or.inl hxz⟩
      have hz : z ∈ c.supp := (c.mem_supp_congr_adj hweak).mp hx
      intro v hv
      simp only [DirectedPath.Walk.support_cons, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact hx
      · exact ih (List.pairwise_cons.mp hnodup).2 hz hv

/-- A finite simple directed path beginning in a weak component stays in
that component. -/
theorem supportSet_subset_component
    (c : (WeakGraph D).ConnectedComponent)
    (p : Bridge.DirectedABPath D A B) (hp : p.path.start ∈ c.supp) :
    p.supportSet ⊆ c.supp :=
  walk_support_subset_component c p.path.walk p.path.isPath hp

/-- Reinterpret a global directed path as a path between the endpoint
slices in the weak component of its initial vertex. -/
def localizePath (p : Bridge.DirectedABPath D A B) :
    Bridge.DirectedABPath D
      (A ∩ ((WeakGraph D).connectedComponentMk p.path.start).supp)
      (B ∩ ((WeakGraph D).connectedComponentMk p.path.start).supp) where
  path := p.path
  start_mem := ⟨p.start_mem, ConnectedComponent.connectedComponentMk_mem⟩
  finish_mem := ⟨p.finish_mem,
    supportSet_subset_component
      ((WeakGraph D).connectedComponentMk p.path.start) p
      ConnectedComponent.connectedComponentMk_mem
      p.finish_mem_supportSet⟩

@[simp]
theorem supportSet_localizePath (p : Bridge.DirectedABPath D A B) :
    (localizePath p).supportSet = p.supportSet :=
  rfl

@[simp]
theorem liftPath_localizePath (p : Bridge.DirectedABPath D A B) :
    liftPath ((WeakGraph D).connectedComponentMk p.path.start)
      (localizePath p) = p := by
  cases p
  rfl

/-- Exact directed Menger conclusions constructed separately in all weak
components assemble to the exact global conclusion.  Local paths remain
paths in `D`; only their endpoint sets are sliced by the component. -/
theorem assemble
    (hlocal : ∀ c : (WeakGraph D).ConnectedComponent,
      Bridge.DirectedMengerConclusion D (A ∩ c.supp) (B ∩ c.supp)) :
    Bridge.DirectedMengerConclusion D A B := by
  classical
  choose P S hP hsep horth using hlocal
  let P' : Set (Bridge.DirectedABPath D A B) :=
    ⋃ c : (WeakGraph D).ConnectedComponent, liftPath c '' P c
  let S' : Set V := ⋃ c : (WeakGraph D).ConnectedComponent, S c
  have hS_component :
      ∀ c : (WeakGraph D).ConnectedComponent, S c ⊆ c.supp := by
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
      change Disjoint (liftPath c p₀).supportSet
        (liftPath c q₀).supportSet
      rw [supportSet_liftPath, supportSet_liftPath]
      apply hP c hp₀ hq₀
      intro hp₀q₀
      exact hpq (congrArg (liftPath c) hp₀q₀)
    · change Disjoint (liftPath c p₀).supportSet
        (liftPath d q₀).supportSet
      apply Set.disjoint_of_subset
        (supportSet_subset_component c (liftPath c p₀) p₀.start_mem.2)
        (supportSet_subset_component d (liftPath d q₀) q₀.start_mem.2)
      exact SimpleGraph.pairwise_disjoint_supp_connectedComponent
        (WeakGraph D) hcd
  · intro q
    let c : (WeakGraph D).ConnectedComponent :=
      (WeakGraph D).connectedComponentMk q.path.start
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
      refine ⟨v,
        ⟨Set.mem_iUnion.2 ⟨c, hv.1⟩, by simpa using hv.2⟩, ?_⟩
      intro w hw
      simp only [S', Set.mem_iUnion] at hw
      obtain ⟨d, hwd⟩ := hw.1
      have hwc : w ∈ c.supp :=
        supportSet_subset_component c (liftPath c p₀)
          p₀.start_mem.2 hw.2
      have hdc : d = c :=
        ConnectedComponent.eq_of_common_vertex (hS_component d hwd) hwc
      subst d
      apply huniq w
      exact ⟨hwd, by simpa using hw.2⟩

/-- If one endpoint slice is countable in each weak component (with the
choice of endpoint allowed to vary by component), the exact directed
Menger conclusion holds globally. -/
theorem directedMengerConclusion_of_componentwise_either_countable
    (D : Digraph V) (A B : Set V)
    (hcount : ∀ c : (WeakGraph D).ConnectedComponent,
      (A ∩ c.supp).Countable ∨ (B ∩ c.supp).Countable) :
    Bridge.DirectedMengerConclusion D A B := by
  apply assemble
  intro c
  let G : DWeb V :=
    { graph := D
      source := A ∩ c.supp
      target := B ∩ c.supp }
  rcases hcount c with hsource | htarget
  · exact AharoniBerger.directedMengerConclusion_of_source_countable
      G hsource
  · exact DirectedEndpointDuality.directedMengerConclusion_of_target_countable
      G htarget

#print axioms assemble
#print axioms directedMengerConclusion_of_componentwise_either_countable

end DirectedComponentwise
end Erdos599
