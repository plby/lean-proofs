/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos182.Foundations
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Erdős Problem 182: passing to an exact number of vertices

The asymptotic constructions naturally produce a graph on at most `n`
vertices.  This file records that one can add isolated vertices without
changing the number of edges or creating a positive-degree regular subgraph.
-/

open Finset Fintype
open scoped Classical

namespace Erdos182

/-- Add `n - m` isolated vertices to a graph on `Fin m`, using the canonical
inclusion `Fin m ↪ Fin n`. -/
def padGraph {m n : ℕ} (G : SimpleGraph (Fin m)) (h : m ≤ n) :
    SimpleGraph (Fin n) :=
  G.map (Fin.castLEEmb h)

@[simp]
lemma padGraph_adj_iff {m n : ℕ} (G : SimpleGraph (Fin m)) (h : m ≤ n)
    {u v : Fin n} :
    (padGraph G h).Adj u v ↔
      ∃ u' v' : Fin m, G.Adj u' v' ∧ Fin.castLEEmb h u' = u ∧
        Fin.castLEEmb h v' = v := by
  change (G.map (Fin.castLEEmb h)).Adj u v ↔ _
  exact SimpleGraph.map_adj (Fin.castLEEmb h) G u v

@[simp]
lemma padGraph_adj_castLE_iff {m n : ℕ} (G : SimpleGraph (Fin m)) (h : m ≤ n)
    (u v : Fin m) :
    (padGraph G h).Adj (Fin.castLEEmb h u) (Fin.castLEEmb h v) ↔ G.Adj u v := by
  change (G.map (Fin.castLEEmb h)).Adj (Fin.castLEEmb h u) (Fin.castLEEmb h v) ↔ _
  exact SimpleGraph.map_adj_apply

/-- Padding adds only isolated vertices, so it preserves the number of edges. -/
@[simp]
lemma card_edgeFinset_padGraph {m n : ℕ} (G : SimpleGraph (Fin m)) (h : m ≤ n) :
    (padGraph G h).edgeFinset.card = G.edgeFinset.card := by
  classical
  rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset,
    ← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset, padGraph,
    SimpleGraph.edgeSet_map]
  exact Set.ncard_image_of_injective _ (Fin.castLEEmb h).sym2Map.injective

/-- Every non-isolated vertex of a padded graph comes from the original
vertex set. -/
lemma mem_range_of_mem_support_padGraph {m n : ℕ} (G : SimpleGraph (Fin m))
    (h : m ≤ n) {v : Fin n} (hv : v ∈ (padGraph G h).support) :
    v ∈ Set.range (Fin.castLEEmb h) := by
  rw [padGraph, SimpleGraph.support_map] at hv
  obtain ⟨u, _, rfl⟩ := hv
  exact ⟨u, rfl⟩

private lemma subgraph_verts_subset_range_of_pos_regular
    {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (f : V ↪ W) (k : ℕ) (hk : 0 < k)
    (H : (G.map f).Subgraph)
    (hHreg : ∀ v : H.verts, (H.coe.neighborSet v).ncard = k) :
    H.verts ⊆ Set.range f := by
  classical
  intro w hw
  let wH : H.verts := ⟨w, hw⟩
  have hpos : 0 < (H.coe.neighborSet wH).ncard := by
    rw [hHreg wH]
    exact hk
  obtain ⟨z, hz⟩ := (Set.ncard_pos (Set.toFinite _)).mp hpos
  have hadj : H.Adj w z := hz
  have hmap : (G.map f).Adj w z := H.adj_sub hadj
  rw [SimpleGraph.map_adj] at hmap
  obtain ⟨u, _, _, hu, _⟩ := hmap
  exact ⟨u, hu⟩

/-- A positive-degree regular subgraph of a graph padded by isolates pulls
back to a regular subgraph of the original graph. -/
lemma containsRegularSubgraph_of_contains_map
    {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (f : V ↪ W) (k : ℕ) (hk : 0 < k)
    (hcontains : ContainsRegularSubgraph (G.map f) k) :
    ContainsRegularSubgraph G k := by
  classical
  obtain ⟨H, hHne, hHreg⟩ := hcontains
  let gf : G ↪g G.map f := SimpleGraph.Embedding.map f G
  let K : G.Subgraph := H.comap gf.toHom
  have hRange : H.verts ⊆ Set.range f :=
    subgraph_verts_subset_range_of_pos_regular G f k hk H hHreg
  have hKne : K.verts.Nonempty := by
    obtain ⟨w, hw⟩ := hHne
    obtain ⟨v, hv⟩ := hRange hw
    refine ⟨v, ?_⟩
    change f v ∈ H.verts
    simpa [hv]
  let toH : K.verts → H.verts := fun v ↦ ⟨f v, v.2⟩
  have htoH_injective : Function.Injective toH := by
    intro u v huv
    apply Subtype.ext
    exact f.injective (congrArg Subtype.val huv)
  have htoH_surjective : Function.Surjective toH := by
    intro w
    obtain ⟨v, hv⟩ := hRange w.2
    have hvK : v ∈ K.verts := by
      change f v ∈ H.verts
      simp [hv]
    refine ⟨⟨v, hvK⟩, ?_⟩
    apply Subtype.ext
    exact hv
  let eVerts : K.verts ≃ H.verts :=
    Equiv.ofBijective toH ⟨htoH_injective, htoH_surjective⟩
  have he_adj (u v : K.verts) :
      H.coe.Adj (eVerts u) (eVerts v) ↔ K.coe.Adj u v := by
    change H.Adj (f u) (f v) ↔ G.Adj u v ∧ H.Adj (f u) (f v)
    constructor
    · intro huv
      exact ⟨(SimpleGraph.map_adj_apply.mp (H.adj_sub huv)), huv⟩
    · exact And.right
  let eGraph : K.coe ≃g H.coe :=
    { __ := eVerts
      map_rel_iff' := fun {u v} ↦ he_adj u v }
  refine ⟨K, hKne, ?_⟩
  intro v
  have hncard :
      (K.coe.neighborSet v).ncard =
        (H.coe.neighborSet (eGraph v)).ncard :=
    Set.ncard_congr' (eGraph.mapNeighborSet v)
  rw [hncard]
  exact hHreg (eGraph v)

/-- Adding isolated vertices preserves avoidance of a nonempty regular
subgraph of positive degree. -/
lemma isRegularSubgraphFree_padGraph {m n k : ℕ} (G : SimpleGraph (Fin m))
    (h : m ≤ n) (hk : 0 < k) (hG : IsRegularSubgraphFree G k) :
    IsRegularSubgraphFree (padGraph G h) k := by
  intro hcontains
  exact hG (containsRegularSubgraph_of_contains_map G (Fin.castLEEmb h) k hk hcontains)

/-- Exact-order padding transfers every lower-bound witness from `m ≤ n`
vertices to exactly `n` vertices. -/
lemma exists_exactOrder_regularSubgraphFree_of_le {m n k e : ℕ} (h : m ≤ n)
    (hk : 0 < k)
    (hex : ∃ G : SimpleGraph (Fin m), IsRegularSubgraphFree G k ∧
      e ≤ G.edgeFinset.card) :
    ∃ G : SimpleGraph (Fin n), IsRegularSubgraphFree G k ∧
      e ≤ G.edgeFinset.card := by
  obtain ⟨G, hGfree, hGedges⟩ := hex
  exact ⟨padGraph G h, isRegularSubgraphFree_padGraph G h hk hGfree,
    by simpa using hGedges⟩

/-- Consequently the regular-subgraph extremal number is monotone in the
number of vertices (for positive target degree). -/
lemma regularExtremalNumber_mono_vertices {m n k : ℕ} (h : m ≤ n) (hk : 0 < k) :
    regularExtremalNumber m k ≤ regularExtremalNumber n k := by
  obtain ⟨G, hGfree, hGcard⟩ := exists_regularExtremalGraph m k hk
  have hpadfree : IsRegularSubgraphFree (padGraph G h) k :=
    isRegularSubgraphFree_padGraph G h hk hGfree
  calc
    regularExtremalNumber m k = G.edgeFinset.card := hGcard.symm
    _ = (padGraph G h).edgeFinset.card := (card_edgeFinset_padGraph G h).symm
    _ ≤ regularExtremalNumber n k :=
      card_edgeFinset_le_regularExtremalNumber (padGraph G h) hpadfree

end Erdos182
