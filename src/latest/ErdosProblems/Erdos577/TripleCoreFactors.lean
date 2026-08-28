import ErdosProblems.Erdos577.TripleCoreSwap
import ErdosProblems.Erdos577.PartitionReplacement

/-! Complete a triangle-core factor by the actual complementary first block. -/

namespace Erdos577.UniversalTriple

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {q : Quadrilateral G}

lemma Configuration.paw_disjoint_block (h : Configuration c p q)
    {a : Finset V} (ha : a ∈ c.blocks) : Disjoint p.support a := by
  rw [h.paw]
  exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)

theorem Configuration.no_triangle_core_factor (h : Configuration c p q) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {a : Finset V} (ha : a ∈ c.blocks) (haq : a ≠ q.support)
    {u : V} (hu : u ∈ q.support)
    (hrep : QuadOn G (insert p.leaf (q.support.erase u))) :
    ¬LocalFactor G (insert u (p.triangle ∪ a)) := by
  intro hf
  have hFA := h.paw_disjoint_block ha
  have hAQ := c.property.blocks_disjoint ha h.block haq
  have hTQ := h.disjoint.mono_left (p.support_eq ▸ subset_insert _ _)
  have hdis : Disjoint (p.triangle ∪ a) q.support := disjoint_union_left.mpr ⟨hTQ, hAQ⟩
  have hx : p.leaf ∉ (p.triangle ∪ a) ∪ q.support := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · rcases mem_union.mp hh with hh | hh
      · exact p.leaf_not_mem_triangle hh
      · exact disjoint_left.mp hFA (p.support_eq ▸ mem_insert_self _ _) hh
    · exact h.paw_outside 0 hh
  obtain ⟨f⟩ := hf.partition
  let all := BlockPartition.replacementUnion hdis hx hu f (BlockPartition.single hrep)
  have hsel : ({q.support, a} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset h.block (singleton_subset_iff.mpr ha)
  have he : insert p.leaf ((p.triangle ∪ a) ∪ q.support) =
      c.remainder ∪ ({q.support, a} : Finset (Finset V)).biUnion id := by
    simp only [biUnion_insert, singleton_biUnion, id_eq]
    rw [← h.paw, p.support_eq]
    ext v
    simp only [mem_insert, mem_union]
    tauto
  exact hn (c.complementPartition.hasPacking_of_selected_factor hcard {q.support, a} hsel
    (he ▸ all))

theorem Configuration.no_exposed_core_factor (h : Configuration c p q) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {a : Finset V} (ha : a ∈ c.blocks) (haq : a ≠ q.support) :
    ¬LocalFactor G (insert (q 3) (p.triangle ∪ a)) :=
  h.no_triangle_core_factor hcard hn ha haq ((q.mem_support _).mpr ⟨3, rfl⟩)
    (QuadOn.of_clique h.leaf_replacement_complete.card_eq h.leaf_replacement_complete.isClique)

end Erdos577.UniversalTriple
