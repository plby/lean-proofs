/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import Mathlib.Combinatorics.SimpleGraph.Maps
import ErdosProblems.Erdos551.External.Erdos207.ExclusiveAbsorbers
import ErdosProblems.Erdos551.External.Erdos207.SphereExpansion

/-!
# Transporting finite absorber certificates

The cycle cover attaches a rooted copy of a fixed exclusive absorber along
each injection of its root graph.  This file proves once and for all that the
triple-system and graph certificates are preserved by an arbitrary vertex
embedding.
-/

namespace Erdos207

open Finset

/-- Mapping all vertices of a triple family maps its covered graph. -/
theorem coveredGraph_mapTripleSystem
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (C : TripleSystemOn V) :
    coveredGraph (mapTripleSystem f C) = (coveredGraph C).map f := by
  ext x y
  rw [coveredGraph_adj, SimpleGraph.map_adj]
  constructor
  · rintro ⟨T, hT, hxT, hyT, hxy⟩
    obtain ⟨T₀, hT₀, rfl⟩ := Finset.mem_map.mp hT
    obtain ⟨a, haT, hax⟩ := Finset.mem_map.mp hxT
    obtain ⟨b, hbT, hby⟩ := Finset.mem_map.mp hyT
    refine ⟨a, b, ⟨T₀, hT₀, haT, hbT, ?_⟩, hax, hby⟩
    intro hab
    apply hxy
    exact hax.symm.trans ((congrArg f hab).trans hby)
  · rintro ⟨a, b, ⟨T, hT, haT, hbT, hab⟩, rfl, rfl⟩
    refine ⟨mapTriple f T, (mem_mapTripleSystem_iff f C T).mpr hT,
      (mem_mapTriple_apply_iff f T a).mpr haT,
      (mem_mapTriple_apply_iff f T b).mpr hbT, f.injective.ne hab⟩

/-- Graph pushforward by an embedding preserves binary suprema. -/
theorem SimpleGraph.map_sup_embedding
    {V W : Type*} (f : V ↪ W) (G H : SimpleGraph V) :
    (G ⊔ H).map f = G.map f ⊔ H.map f := by
  ext x y
  simp only [SimpleGraph.map_adj, SimpleGraph.sup_adj]
  constructor
  · rintro ⟨u, v, huv | huv, rfl, rfl⟩
    · exact Or.inl ⟨u, v, huv, rfl, rfl⟩
    · exact Or.inr ⟨u, v, huv, rfl, rfl⟩
  · rintro (⟨u, v, huv, rfl, rfl⟩ | ⟨u, v, huv, rfl, rfl⟩)
    · exact ⟨u, v, Or.inl huv, rfl, rfl⟩
    · exact ⟨u, v, Or.inr huv, rfl, rfl⟩

/-- Graph pushforward by an embedding preserves edge-disjointness. -/
theorem SimpleGraph.disjoint_map_embedding
    {V W : Type*} (f : V ↪ W) {G H : SimpleGraph V}
    (hGH : Disjoint G H) : Disjoint (G.map f) (H.map f) := by
  rw [← SimpleGraph.disjoint_edgeSet]
  rw [SimpleGraph.edgeSet_map, SimpleGraph.edgeSet_map]
  rw [Set.disjoint_left]
  rintro e ⟨a, haG, rfl⟩ ⟨b, hbH, hab⟩
  have hsym2 : a = b := f.sym2Map.injective hab.symm
  subst b
  exact (Set.disjoint_left.mp
    (SimpleGraph.disjoint_edgeSet.mpr hGH) haG) hbH

/-- Every exclusive absorber certificate can be attached along an arbitrary
vertex embedding. -/
theorem IsExclusiveGraphAbsorberOn.map
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {root : SimpleGraph V} {out inn : TripleSystemOn V}
    (h : IsExclusiveGraphAbsorberOn root out inn) (f : V ↪ W) :
    IsExclusiveGraphAbsorberOn (root.map f)
      (mapTripleSystem f out) (mapTripleSystem f inn) := by
  refine ⟨h.1.map f, h.2.1.map f, ?_, ?_⟩
  · rw [coveredGraph_mapTripleSystem]
    exact SimpleGraph.disjoint_map_embedding f h.2.2.1
  · rw [coveredGraph_mapTripleSystem, coveredGraph_mapTripleSystem,
      ← SimpleGraph.map_sup_embedding]
    exact congrArg (SimpleGraph.map f) h.2.2.2

end Erdos207
