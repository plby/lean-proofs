import ErdosProblems.Erdos577.FullLeafHeavyScoreBounds

/-! The core insertion score bounds apply after exposing any of the five possible terminals. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}
variable (h : Configuration c p s a y)

include h

theorem Configuration.core_insertion_triangle_bound {x : V} (hx : x ∈ insert p.leaf s)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    {v : V} (hv : v ∈ j) (f : BlockPartition G (insert v (p.triangle ∪ a)))
    (htri : TriangleIn G (insert x (j.erase v))) :
    f.weightSum (edgeCount G) ≤ 6 + edgeCount G j := by
  obtain ⟨e, he, ht, hT, _, _, hkeep⟩ := h.exposed_chain hx
  let f' : BlockPartition G (insert v (e.triangle ∪ a)) := {
    blocks := f.blocks
    disjoint := f.disjoint
    cover := by rw [hT]; exact f.cover
    quad := f.quad }
  have hb := FullLeafHeavy.insertion_triangle_bound he (hkeep a h.core h.different)
    (hkeep j hj hjs) hja.symm hv f' (by simpa only [ht] using htri)
  change f.weightSum (edgeCount G) ≤ edgeCount G a + edgeCount G j at hb
  rw [edgeCount_clique h.core_clique.isClique, h.core_clique.card_eq] at hb
  norm_num only [Nat.choose] at hb
  exact hb

theorem Configuration.core_insertion_matching_bound {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {x : V} (hx : x ∈ insert p.leaf s)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    {v : V} (hv : v ∈ j) (f : BlockPartition G (insert v (p.triangle ∪ a)))
    (m : TwoEdges G) (hm : m.support = insert x (j.erase v)) :
    f.weightSum (edgeCount G) ≤ 7 + edgeCount G j := by
  obtain ⟨e, he, ht, hT, _, _, hkeep⟩ := h.exposed_chain hx
  let f' : BlockPartition G (insert v (e.triangle ∪ a)) := {
    blocks := f.blocks
    disjoint := f.disjoint
    cover := by rw [hT]; exact f.cover
    quad := f.quad }
  have hb := FullLeafHeavy.insertion_matching_bound he hcard hdeg hn
    (hkeep a h.core h.different) (hkeep j hj hjs) hja.symm hv f' m
    (by simpa only [ht] using hm)
  change f.weightSum (edgeCount G) ≤ edgeCount G a + edgeCount G j + 1 at hb
  rw [edgeCount_clique h.core_clique.isClique, h.core_clique.card_eq] at hb
  norm_num only [Nat.choose] at hb
  omega

theorem Configuration.complete_of_core_split {x : V} (hx : x ∈ insert p.leaf s)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    {v : V} (hv : v ∈ j) (f : BlockPartition G (insert v (p.triangle ∪ a)))
    (hweight : 12 ≤ f.weightSum (edgeCount G))
    (htri : TriangleIn G (insert x (j.erase v))) : G.IsNClique 4 j := by
  have hb := h.core_insertion_triangle_bound hx hj hjs hja hv f htri
  have hj4 := (c.property.blocks_quad j hj).card
  have hupper := edgeCount_le_six G hj4
  exact clique_of_four_six hj4 (by omega)

end Erdos577.FullLeafCore
