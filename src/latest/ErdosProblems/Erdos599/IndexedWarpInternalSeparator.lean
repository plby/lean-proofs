/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.IndexedWarpComponents
import ErdosProblems.Erdos599.InternalSeparatorComponentwise

/-!
# Indexed cofinal families behind an internal separator

An indexed family of finite-character warps has small interaction
components.  To use those components for an exact Menger decomposition one
needs the additional, logically essential coverage condition that every
edge of the residual quotient lie in one of those interaction components.
Under that condition, weak quotient components are small and the internal
separator theorem closes the original web by lower cardinal induction.
-/

noncomputable section

namespace Erdos599
namespace IndexedWarpInternalSeparator

open Cardinal Set DirectedPath SimpleGraph

universe u

variable {V I : Type u} {G : DWeb V}

/-- Every directed edge has both endpoints on one member of one indexed
warp. -/
def CoversEdges (W : I → Set G.DPath) : Prop :=
  ∀ {x y : V}, G.graph.Adj x y →
    ∃ i p, p ∈ W i ∧ x ∈ p.support ∧ y ∈ p.support

theorem sameIndexedWarpPath_of_weakAdj
    {W : I → Set G.DPath} (hcover : CoversEdges W) {x y : V}
    (hxy : (DirectedComponentwise.WeakGraph G.graph).Adj x y) :
    IndexedWarpComponents.SameIndexedWarpPath W x y := by
  rcases hxy.2 with h | h
  · exact hcover h
  · exact IndexedWarpComponents.sameIndexedWarpPath_symm (hcover h)

/-- A weak graph component is contained in the indexed-warp interaction
component of any one of its vertices, provided the indexed family covers
all directed edges. -/
theorem weakComponent_support_subset_indexed_component
    {W : I → Set G.DPath} (hcover : CoversEdges W) (root : V) :
    ((DirectedComponentwise.WeakGraph G.graph).connectedComponentMk root).supp
      ⊆ IndexedWarpComponents.component W root := by
  intro x hx
  rw [ConnectedComponent.mem_supp_iff] at hx
  have hreach :
      (DirectedComponentwise.WeakGraph G.graph).Reachable root x :=
    ConnectedComponent.exact hx.symm
  have hrtc : Relation.ReflTransGen
      (DirectedComponentwise.WeakGraph G.graph).Adj root x :=
    ((DirectedComponentwise.WeakGraph G.graph).reachable_iff_reflTransGen
      root x).1 hreach
  exact Relation.ReflTransGen.mono
    (r := (DirectedComponentwise.WeakGraph G.graph).Adj)
    (p := IndexedWarpComponents.SameIndexedWarpPath W)
    (fun _ _ h ↦ sameIndexedWarpPath_of_weakAdj hcover h)
    root x hrtc

/-- Hence each weak component has the same sharp cardinal upper bound as
the corresponding indexed-warp interaction component. -/
theorem mk_weakComponent_le
    (W : I → Set G.DPath)
    (hW : ∀ i, G.IsWarp (W i))
    (hfinite : ∀ i, G.HasFiniteCharacter (W i))
    (hcover : CoversEdges W)
    (c : (DirectedComponentwise.WeakGraph G.graph).ConnectedComponent) :
    #c.supp ≤ max aleph0 #I := by
  refine c.ind ?_
  intro root
  exact (Cardinal.mk_subtype_mono
    (weakComponent_support_subset_indexed_component hcover root)).trans
      (IndexedWarpComponents.mk_component_le W hW hfinite root)

#print axioms mk_weakComponent_le

end IndexedWarpInternalSeparator

namespace AharoniBerger
namespace IndexedWarpInternalSeparator

open Cardinal Set DirectedPath
open _root_.Erdos599.IndexedWarpInternalSeparator
open _root_.Erdos599.AharoniBerger.InternalSeparatorComponentwise

variable {V I : Type u}

/-- A cofinal-size indexed family which covers all residual quotient edges
forces every quotient weak component below `kappa`; lower induction then
gives the exact directed Menger conclusion in the original web. -/
theorem directedMengerConclusion_of_indexedWarp_edge_cover
    (G : DWeb V) (M : G.Wave) (kappa : Cardinal.{u})
    (hlower : CardinalInduction.UniversalCardinalInductionBelow V kappa)
    (W : I → Set (Quotient G M).DPath)
    (hW : ∀ i, (Quotient G M).IsWarp (W i))
    (hfinite : ∀ i, (Quotient G M).HasFiniteCharacter (W i))
    (hcover : CoversEdges W)
    (hindex : max aleph0 #I < kappa) :
    Bridge.DirectedMengerConclusion G.graph G.source G.target := by
  apply directedMengerConclusion_of_lowerInduction_and_componentwise_shrink
    G M kappa hlower
  intro c
  apply Or.inl
  refine (Cardinal.mk_subtype_mono Set.inter_subset_right).trans_lt ?_
  exact (mk_weakComponent_le W hW hfinite hcover c).trans_lt hindex

#print axioms directedMengerConclusion_of_indexedWarp_edge_cover

end IndexedWarpInternalSeparator
end AharoniBerger
end Erdos599
