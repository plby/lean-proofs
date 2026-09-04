/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos76.Assembly

/-!
# Transport and asymptotic interfaces for Erdős Problem 76

The finite fractional theorem is stated on `Fin n`, whereas averaging arguments
naturally produce induced graphs on arbitrary finite subtypes.  This file
provides the graph-isomorphism transport needed to pass between those forms.

It also records the strictly weaker asymptotic fractional statement that is
already sufficient, together with Haxell--Rödl rounding, to prove `Resolution`.
-/

open Filter Finset

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {α β : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]

/-- Relabel a triangle-weight function along an equivalence of vertex types. -/
def relabelWeight (e : α ≃ β) (w : Finset α → ℝ) : Finset β → ℝ :=
  fun t ↦ w (t.map e.symm.toEmbedding)

@[simp]
lemma relabelWeight_apply_map (e : α ≃ β) (w : Finset α → ℝ)
    (t : Finset α) : relabelWeight e w (t.map e.toEmbedding) = w t := by
  simp [relabelWeight, Finset.map_map]

@[simp]
lemma relabelWeight_symm (e : α ≃ β) (w : Finset α → ℝ) :
    relabelWeight e.symm (relabelWeight e w) = w := by
  funext t
  simp [relabelWeight, Finset.map_map]

private lemma isNClique_map_equiv_iff (G : SimpleGraph α) (e : α ≃ β)
    (t : Finset α) (n : ℕ) :
    (G.map e.toEmbedding).IsNClique n (t.map e.toEmbedding) ↔ G.IsNClique n t := by
  constructor
  · intro ht
    have h := ht.map (f := e.symm.toEmbedding)
    have hgraph : (G.map e.toEmbedding).map e.symm.toEmbedding = G := by
      rw [SimpleGraph.map_map]
      change G.map (fun x : α ↦ e.symm (e x)) = G
      rw [show (fun x : α ↦ e.symm (e x)) = id by funext x; simp, G.map_id]
    have hfin : (t.map e.toEmbedding).map e.symm.toEmbedding = t := by
      simp [Finset.map_map]
    rw [hgraph, hfin] at h
    exact h
  · exact fun ht ↦ ht.map

lemma fractionalSize_relabel (G : SimpleGraph α) (e : α ≃ β)
    (w : Finset α → ℝ) :
    fractionalSize (G.map e.toEmbedding) (relabelWeight e w) = fractionalSize G w := by
  classical
  let : DecidableRel G.Adj := Classical.decRel _
  let : DecidableRel (G.map e.toEmbedding).Adj := Classical.decRel _
  unfold fractionalSize
  symm
  apply Finset.sum_equiv e.finsetCongr
  · intro t
    change t ∈ G.cliqueFinset 3 ↔
      t.map e.toEmbedding ∈ (G.map e.toEmbedding).cliqueFinset 3
    simpa only [SimpleGraph.mem_cliqueFinset_iff] using
      (isNClique_map_equiv_iff G e t 3).symm
  · intro t ht
    exact (relabelWeight_apply_map e w t).symm

lemma fractionalCoveredSize_relabel (G : SimpleGraph α) (e : α ≃ β)
    (w : Finset α → ℝ) :
    fractionalCoveredSize (G.map e.toEmbedding) (relabelWeight e w) =
      fractionalCoveredSize G w := by
  rw [fractionalCoveredSize, fractionalCoveredSize, fractionalSize_relabel]

/-- The graph complement commutes with relabelling by a vertex equivalence. -/
lemma compl_map_equiv (G : SimpleGraph α) (e : α ≃ β) :
    (G.map e.toEmbedding)ᶜ = Gᶜ.map e.toEmbedding := by
  rw [← SimpleGraph.comap_symm G e, ← SimpleGraph.comap_symm Gᶜ e]
  ext x y
  simp [SimpleGraph.compl_adj]

private lemma edge_mem_triangle_map_iff (e : α ↪ β) (p : Sym2 α)
    (t : Finset α) :
    e.sym2Map p ∈ (t.map e).sym2 ↔ p ∈ t.sym2 := by
  rw [Finset.sym2_map]
  constructor
  · intro hp
    obtain ⟨q, hq, hqp⟩ := Finset.mem_map.mp hp
    have : q = p := e.sym2Map.injective hqp
    simpa only [this] using hq
  · intro hp
    exact Finset.mem_map.mpr ⟨p, hp, rfl⟩

lemma fractionalEdgeLoad_relabel (G : SimpleGraph α) (e : α ≃ β)
    (w : Finset α → ℝ) (p : Sym2 α) :
    fractionalEdgeLoad (G.map e.toEmbedding) (relabelWeight e w)
        (e.toEmbedding.sym2Map p) =
      fractionalEdgeLoad G w p := by
  classical
  let : DecidableRel G.Adj := Classical.decRel _
  let : DecidableRel (G.map e.toEmbedding).Adj := Classical.decRel _
  unfold fractionalEdgeLoad
  symm
  apply Finset.sum_equiv e.finsetCongr
  · intro t
    simp only [Finset.mem_filter, Equiv.finsetCongr_apply]
    constructor
    · rintro ⟨ht, hp⟩
      exact ⟨SimpleGraph.mem_cliqueFinset_iff.mpr
        ((isNClique_map_equiv_iff G e t 3).mpr
          (SimpleGraph.mem_cliqueFinset_iff.mp ht)),
        (edge_mem_triangle_map_iff e.toEmbedding p t).mpr hp⟩
    · rintro ⟨ht, hp⟩
      exact ⟨SimpleGraph.mem_cliqueFinset_iff.mpr
        ((isNClique_map_equiv_iff G e t 3).mp
          (SimpleGraph.mem_cliqueFinset_iff.mp ht)),
        (edge_mem_triangle_map_iff e.toEmbedding p t).mp hp⟩
  · intro t ht
    exact (relabelWeight_apply_map e w t).symm

/-- Feasible fractional packings are invariant under relabelling of vertices. -/
lemma IsFractionalPacking.relabel {G : SimpleGraph α} {w : Finset α → ℝ}
    (hw : IsFractionalPacking G w) (e : α ≃ β) :
    IsFractionalPacking (G.map e.toEmbedding) (relabelWeight e w) := by
  classical
  let : DecidableRel G.Adj := Classical.decRel _
  let : DecidableRel (G.map e.toEmbedding).Adj := Classical.decRel _
  constructor
  · intro t ht
    have ht' := SimpleGraph.mem_cliqueFinset_iff.mp ht
    obtain ⟨s, hs, rfl⟩ :=
      (SimpleGraph.isNClique_map_iff (G := G) (f := e.toEmbedding) (by omega)).mp ht'
    simpa using hw.1 s (SimpleGraph.mem_cliqueFinset_iff.mpr hs)
  · intro p hp
    have hp' := SimpleGraph.mem_edgeFinset.mp hp
    rw [SimpleGraph.edgeSet_map e.toEmbedding G] at hp'
    obtain ⟨q, hq, rfl⟩ := hp'
    have hq' : q ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr hq
    rw [fractionalEdgeLoad_relabel]
    exact hw.2 q hq'

/-- `GruslysLetzterFractional` on an arbitrary finite vertex type of the
specified cardinality. -/
lemma GruslysLetzterFractional.on_fintype (hGL : GruslysLetzterFractional)
    {n : ℕ} (hcard : Fintype.card α = n) (hn : 26 ≤ n) (G : SimpleGraph α) :
    ∃ wR wB : Finset α → ℝ,
      IsFractionalPacking G wR ∧ IsFractionalPacking Gᶜ wB ∧
        (((n - 1) ^ 2 / 4 : ℕ) : ℝ) ≤
          fractionalCoveredSize G wR + fractionalCoveredSize Gᶜ wB := by
  classical
  let e : α ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let H : SimpleGraph (Fin n) := G.map e.toEmbedding
  obtain ⟨uR, uB, huR, huB, hsize⟩ := hGL.apply n hn H
  let wR : Finset α → ℝ := relabelWeight e.symm uR
  let wB : Finset α → ℝ := relabelWeight e.symm uB
  have hmap : H.map e.symm.toEmbedding = G := by
    dsimp only [H]
    rw [SimpleGraph.map_map]
    simpa using G.map_id
  refine ⟨wR, wB, ?_, ?_, ?_⟩
  · simpa only [wR, hmap] using huR.relabel e.symm
  · have hc : Hᶜ.map e.symm.toEmbedding = Gᶜ := by
      rw [← compl_map_equiv H e.symm, hmap]
    simpa only [wB, hc] using huB.relabel e.symm
  · have hsR : fractionalCoveredSize G wR = fractionalCoveredSize H uR := by
      simpa only [wR, hmap] using fractionalCoveredSize_relabel H e.symm uR
    have hc : Hᶜ.map e.symm.toEmbedding = Gᶜ := by
      rw [← compl_map_equiv H e.symm, hmap]
    have hsB : fractionalCoveredSize Gᶜ wB = fractionalCoveredSize Hᶜ uB := by
      simpa only [wB, hc] using fractionalCoveredSize_relabel Hᶜ e.symm uB
    rwa [hsR, hsB]

end

end Erdos76
