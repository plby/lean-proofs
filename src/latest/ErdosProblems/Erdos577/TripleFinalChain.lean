import ErdosProblems.Erdos577.TripleFinalGeometry
import ErdosProblems.Erdos577.SelectedChainExchange

/-! The first changed chain is strong, preserves both scores, and has the exact block family. -/

namespace Erdos577.UniversalTriple

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {q : Quadrilateral G} {a : Finset V} {u : V}

theorem HeavyChoice.exists_final_chain (h : HeavyChoice c p q a u) (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k) :
    ∃ d : TriangleChain G, d.Strong ∧ h.finalPaw.support = d.remainder ∧
      d.terminal = p.vertices 3 ∧ d.triangle = h.finalPaw.triangle ∧
      d.edgeScore = c.edgeScore ∧ d.completeScore = c.completeScore ∧
      d.blocks = (c.blocks \ {q.support, a}) ∪
        {insert (p.vertices 2) (q.support.erase (q 3)), insert (q 3) (a.erase u)} := by
  let b₁ := insert (p.vertices 2) (q.support.erase (q 3))
  let b₂ := insert (q 3) (a.erase u)
  have hcl₁ := h.toConfiguration.second_replacement_complete
  have hcl₂ := h.replacement_complete
  let parts := (BlockPartition.single (QuadOn.of_clique hcl₁.card_eq hcl₁.isClique)).union
    (BlockPartition.single (QuadOn.of_clique hcl₂.card_eq hcl₂.isClique)) h.new_blocks_disjoint
  have hsel : ({q.support, a} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset h.block (singleton_subset_iff.mpr h.heavy_mem)
  have hselected : c.remainder ∪ ({q.support, a} : Finset (Finset V)).biUnion id =
      p.support ∪ (q.support ∪ a) := by
    rw [← h.paw]
    simp only [biUnion_insert, singleton_biUnion, id_eq]
  have hsub : b₁ ∪ b₂ ⊆ c.remainder ∪ ({q.support, a} : Finset (Finset V)).biUnion id := by
    rw [hselected]
    change insert (p.vertices 2) (q.support.erase (q 3)) ∪
      insert (q 3) (a.erase u) ⊆ _
    rw [h.new_blocks_union]
    exact h.new_blocks_subset
  have hrem : (c.remainder ∪ ({q.support, a} : Finset (Finset V)).biUnion id) \ (b₁ ∪ b₂) =
      insert h.finalPaw.leaf h.finalPaw.triangle := by
    rw [hselected, ← h.finalPaw.support_eq]
    change (p.support ∪ (q.support ∪ a)) \ (insert (p.vertices 2)
      (q.support.erase (q 3)) ∪ insert (q 3) (a.erase u)) = _
    rw [h.new_blocks_union]
    exact h.new_remainder
  have hscore (w : ℕ → ℕ) : parts.weightSum (fun s ↦ w (edgeCount G s)) =
      (c.complementPartition.select {q.support, a} hsel).weightSum
        (fun s ↦ w (edgeCount G s)) := by
    rw [BlockPartition.weightSum_union, BlockPartition.weightSum_single,
      BlockPartition.weightSum_single]
    change _ = ∑ s ∈ ({q.support, a} : Finset (Finset V)), w (edgeCount G s)
    rw [sum_pair h.heavy_ne.symm, edgeCount_clique hcl₁.isClique, hcl₁.card_eq,
      edgeCount_clique hcl₂.isClique, hcl₂.card_eq, edgeCount_clique h.complete.isClique,
      h.complete.card_eq, edgeCount_clique h.heavy_complete.isClique,
      h.heavy_complete.card_eq]
  let d := c.replaceSelected {q.support, a} hsel parts hsub h.finalPaw.leaf
    h.finalPaw.triangle_clique h.finalPaw.leaf_not_mem_triangle hrem
  have hd : d.Feasible := hc.replaceSelected_feasible {q.support, a} hsel parts hsub
    h.finalPaw.leaf h.finalPaw.triangle_clique h.finalPaw.leaf_not_mem_triangle hrem
      (hscore id) (hscore (fun n ↦ if n = 6 then 1 else 0))
  have hp : h.finalPaw.support = d.remainder := h.finalPaw.support_eq
  have hpos : 0 < degreeIn G d.terminal d.triangle := card_pos.mpr
    ⟨h.finalPaw.center, mem_filter.mpr ⟨h.finalPaw.center_mem_triangle, h.finalPaw.pendant⟩⟩
  have hbound := d.terminal_degree_le_one hcard hn
  have hs : d.Strong := ⟨hd, by change degreeIn G d.terminal d.triangle = 1; omega⟩
  have he : d.edgeScore = c.edgeScore := le_antisymm (hc.edge_max d) (hd.edge_max c)
  have hf : d.completeScore = c.completeScore :=
    le_antisymm (hc.complete_max d he) (hd.complete_max c he.symm)
  refine ⟨d, hs, hp, rfl, rfl, he, hf, ?_⟩
  change (c.blocks \ {q.support, a}) ∪ ({b₁} ∪ {b₂}) = _
  rw [singleton_union]

end Erdos577.UniversalTriple
