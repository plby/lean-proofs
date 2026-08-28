import ErdosProblems.Erdos577.FullLeafSparseRefinement

/-! Exact three-cycle local partitions are prohibited by the actual complementary core blocks. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}
variable (h : Configuration c p s a y)

include h

theorem Configuration.first_no_double_partition {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {v : V} (hv : v ∈ insert p.leaf s)
    {j l : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    (hl : l ∈ c.blocks) (hls : l ≠ s) (hla : l ≠ a)
    {t : Finset V} (ht : t ⊆ p.triangle ∪ a) (ht3 : t.card = 3) :
    ¬Nonempty (BlockPartition G (insert v (t ∪ (j ∪ l)))) := by
  intro hf
  obtain ⟨e, _, he, htri, _, _, hkeep⟩ := h.exposed_chain hv
  have hsel : ({j, l} : Finset (Finset V)) ⊆ e.blocks :=
    insert_subset (hkeep j hj hjs) (singleton_subset_iff.mpr (hkeep l hl hls))
  have hna : a ∉ ({j, l} : Finset (Finset V)) := by
    simpa only [mem_insert, mem_singleton, not_or] using And.intro hja.symm hla.symm
  apply hn (e.hasPacking_of_selected_core hcard (hkeep a h.core h.different)
    {j, l} hsel hna (by simpa only [htri] using ht)
    (by simpa only [htri] using h.core_complement_quad ht ht3) ?_)
  simpa only [biUnion_insert, singleton_biUnion, id_eq, he] using hf

theorem Configuration.second_no_double_partition {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {v : V} (hv : v ∈ insert (p.vertices 3) a)
    {j l : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    (hl : l ∈ c.blocks) (hls : l ≠ s) (hla : l ≠ a) :
    ¬Nonempty (BlockPartition G (insert v ((s.erase y) ∪ (j ∪ l)))) := by
  intro hf
  have hd := disjoint_union_right.mpr
    ⟨h.bridge_disjoint_block hj hjs, h.bridge_disjoint_block hl hls⟩
  have hpart := h.partition_with_bridge hv (j ∪ l) hd hf
  have hsel : ({s, j, l} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset h.first (insert_subset hj (singleton_subset_iff.mpr hl))
  have hna : a ∉ ({s, j, l} : Finset (Finset V)) := by
    simpa only [mem_insert, mem_singleton, not_or] using
      And.intro h.different (And.intro hja.symm hla.symm)
  obtain ⟨ht, ht3⟩ := h.used_triple hv
  apply hn (JointFirst.hasPacking_of_selected_core hcard p h.paw h.core
    {s, j, l} hsel hna ht (h.core_complement_quad ht ht3) ?_)
  simpa only [biUnion_insert, singleton_biUnion, id_eq] using hpart

end Erdos577.FullLeafCore
