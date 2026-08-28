import ErdosProblems.Erdos577.TripleForbiddenRows
import ErdosProblems.Erdos577.JointCoreCompletion

/-! Complete the partial factors for both centers, retaining the actual remaining blocks. -/

namespace Erdos577

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
theorem TriangleChain.hasPacking_of_triangle_core_partial (c : TriangleChain G) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) {a j : Finset V}
    (ha : a ∈ c.blocks) (hj : j ∈ c.blocks) (haj : a ≠ j) {used : Finset V}
    (hu : used ⊆ c.triangle ∪ a) (hr : QuadOn G ((c.triangle ∪ a) \ used))
    (hf : Nonempty (BlockPartition G (insert c.terminal (used ∪ j)))) : HasPacking G k := by
  have hd : Disjoint (c.triangle ∪ a) j := disjoint_union_left.mpr
    ⟨c.triangle_disjoint_block hj, c.property.blocks_disjoint ha hj haj⟩
  have hx : c.terminal ∉ (c.triangle ∪ a) ∪ j := by
    simp only [mem_union, not_or]
    exact ⟨⟨c.property.terminal_not_mem, c.terminal_not_mem_block ha⟩,
      c.terminal_not_mem_block hj⟩
  obtain ⟨parts⟩ := TwoCore.partition_with_core_complement hd hx hu hr hf
  have hsel : ({a, j} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset ha (singleton_subset_iff.mpr hj)
  have he : insert c.terminal ((c.triangle ∪ a) ∪ j) =
      c.remainder ∪ ({a, j} : Finset (Finset V)).biUnion id := by
    simp only [biUnion_insert, singleton_biUnion, id_eq]
    change insert c.terminal ((c.triangle ∪ a) ∪ j) = insert c.terminal c.triangle ∪ (a ∪ j)
    simp only [insert_union, union_assoc]
  exact c.complementPartition.hasPacking_of_selected_factor hcard {a, j} hsel (he ▸ parts)

namespace UniversalTriple

variable {c : TriangleChain G} {p : Paw G} {q : Quadrilateral G} {a : Finset V} {w : V}

lemma HighCore.core_disjoint_block (h : HighCore c p q a w)
    {j : Finset V} (hj : j ∈ c.blocks) (hja : j ≠ a) : Disjoint (p.triangle ∪ a) j :=
  disjoint_union_left.mpr ⟨(h.toConfiguration.paw_disjoint_block hj).mono_left
    (p.support_eq ▸ subset_insert _ _), c.property.blocks_disjoint h.core_block hj hja.symm⟩

theorem HighCore.no_exposed_partial_factor (h : HighCore c p q a w) (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ c.blocks) (hjQ : j ≠ q.support) (hja : j ≠ a)
    {used : Finset V} (hu : used ⊆ p.triangle ∪ a)
    (hr : QuadOn G ((p.triangle ∪ a) \ used)) :
    ¬LocalFactor G (insert (q 3) (used ∪ j)) := by
  intro hf
  obtain ⟨d, hd, hY, hT, _, _, hblocks⟩ := h.toConfiguration.exists_exposed_chain hc
  have hkeep (b : Finset V) (hb : b ∈ c.blocks) (hbQ : b ≠ q.support) : b ∈ d.blocks := by
    rw [hblocks]
    exact mem_union_left _ (mem_erase.mpr ⟨hbQ, hb⟩)
  apply hn
  apply d.hasPacking_of_triangle_core_partial (used := used) hcard
    (hkeep a h.core_block h.core_ne) (hkeep j hj hjQ) hja.symm
  · rwa [hT]
  · rwa [hT]
  · rw [hY]
    exact hf.partition

theorem HighCore.no_bridge_factor (h : HighCore c p q a w) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ c.blocks) (hjQ : j ≠ q.support) (hja : j ≠ a)
    {used : Finset V} (hu : used ⊆ p.triangle ∪ a) (hb : p.vertices 2 ∉ used)
    (hr : QuadOn G ((p.triangle ∪ a) \ insert (p.vertices 2) used)) :
    ¬LocalFactor G (insert (q 3) (insert p.leaf (used ∪ j))) := by
  intro hf
  have hKJ := h.core_disjoint_block hj hja
  have hJQ := c.property.blocks_disjoint hj h.block hjQ
  have hXJ : p.leaf ∉ j := fun hh ↦ disjoint_left.mp
    (h.toConfiguration.paw_disjoint_block hj) (p.support_eq ▸ mem_insert_self _ _) hh
  have hdis : Disjoint (insert p.leaf (used ∪ j)) q.support :=
    disjoint_insert_left.mpr ⟨h.toConfiguration.paw_outside 0,
      disjoint_union_left.mpr ⟨h.core_disjoint_first.mono_left hu, hJQ⟩⟩
  have hbK : p.vertices 2 ∈ p.triangle ∪ a := mem_union_left _ (by simp [Paw.triangle])
  have hbX : p.vertices 2 ≠ p.leaf := p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 0)
  have hbout : p.vertices 2 ∉ insert p.leaf (used ∪ j) ∪ q.support := by
    simp only [mem_union, mem_insert, not_or]
    exact ⟨⟨hbX, hb, fun hh ↦ disjoint_left.mp hKJ hbK hh⟩,
      h.toConfiguration.paw_outside 2⟩
  obtain ⟨f⟩ := hf.partition
  have hcl := h.toConfiguration.second_replacement_complete
  let f' := BlockPartition.replacementUnion hdis hbout ((q.mem_support _).mpr ⟨3, rfl⟩)
    f (BlockPartition.single (QuadOn.of_clique hcl.card_eq hcl.isClique))
  have he : insert (p.vertices 2) (insert p.leaf (used ∪ j) ∪ q.support) =
      insert p.leaf (insert (p.vertices 2) used ∪ (q.support ∪ j)) := by
    ext z
    simp only [mem_insert, mem_union]
    tauto
  have hXout : p.leaf ∉ (p.triangle ∪ a) ∪ (q.support ∪ j) := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · exact h.leaf_outside_core hh
    · rcases mem_union.mp hh with hh | hh
      · exact h.toConfiguration.paw_outside 0 hh
      · exact hXJ hh
  obtain ⟨parts⟩ := TwoCore.partition_with_core_complement
    (disjoint_union_right.mpr ⟨h.core_disjoint_first, hKJ⟩) hXout
    (insert_subset hbK hu) hr ⟨he ▸ f'⟩
  have hsel : ({q.support, a, j} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset h.block (insert_subset h.core_block (singleton_subset_iff.mpr hj))
  have hcover : insert p.leaf ((p.triangle ∪ a) ∪ (q.support ∪ j)) =
      c.remainder ∪ ({q.support, a, j} : Finset (Finset V)).biUnion id := by
    simp only [biUnion_insert, singleton_biUnion, id_eq]
    rw [← h.paw, p.support_eq]
    ext z
    simp only [mem_insert, mem_union]
    tauto
  exact hn (c.complementPartition.hasPacking_of_selected_factor hcard {q.support, a, j} hsel
    (hcover ▸ parts))

end UniversalTriple

end Erdos577
