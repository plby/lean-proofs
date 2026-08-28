import ErdosProblems.Erdos577.TripleLowCounts

/-! Complete the low-branch factors by Q-Y+b and exclude common leaf/third-vertex columns. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma Paw.erase_second_support (p : Paw G) :
    p.support.erase (p.vertices 2) = {p.leaf, p.center, p.vertices 3} := by
  simp only [Paw.support_eq, Paw.triangle, Paw.leaf, Paw.center]
  rw [erase_insert_of_ne (p.vertices.injective.ne (by decide : (0 : Fin 4) ≠ 2)),
    erase_insert_of_ne (p.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 2)),
    erase_insert]
  simpa only [mem_singleton] using p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 3)

namespace UniversalTriple

variable [Fintype V] [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {q : Quadrilateral G} {a : Finset V}

lemma Configuration.exposed_outside_other (h : Configuration c p q)
    (ha : a ∈ c.blocks) (haq : a ≠ q.support) : q 3 ∉ p.support ∪ a := by
  intro hh
  rcases mem_union.mp hh with hh | hh
  · exact h.quad_outside 3 hh
  · exact disjoint_left.mp (c.property.blocks_disjoint h.block ha haq.symm)
      ((q.mem_support _).mpr ⟨3, rfl⟩) hh

lemma Configuration.partial_paw_card (h : Configuration c p q)
    (ha : a ∈ c.blocks) (haq : a ≠ q.support) :
    (insert (q 3) (p.support.erase (p.vertices 2) ∪ a)).card = 8 := by
  have hY : q 3 ∉ p.support.erase (p.vertices 2) ∪ a :=
    fun hh ↦ h.exposed_outside_other ha haq
      ((union_subset_union (erase_subset _ _) Subset.rfl) hh)
  have hb : p.vertices 2 ∈ p.support := by simp [Paw.support_eq, Paw.triangle]
  rw [card_insert_of_notMem hY,
    card_union_of_disjoint ((h.paw_disjoint_block ha).mono_left (erase_subset _ _)),
    card_erase_of_mem hb, p.card_support, (c.property.blocks_quad a ha).card]

theorem Configuration.no_missing_second_factor (h : Configuration c p q)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (ha : a ∈ c.blocks) (haq : a ≠ q.support) :
    ¬LocalFactor G (insert (q 3) (p.support.erase (p.vertices 2) ∪ a)) := by
  intro hf
  have hbF : p.vertices 2 ∈ p.support := by simp [Paw.support_eq, Paw.triangle]
  have hB : p.vertices 2 ∉ (p.support.erase (p.vertices 2) ∪ a) ∪ q.support := by
    simp only [mem_union, not_or]
    exact ⟨⟨notMem_erase _ _, fun hh ↦ disjoint_left.mp (h.paw_disjoint_block ha) hbF hh⟩,
      h.paw_outside 2⟩
  have hd : Disjoint (p.support.erase (p.vertices 2) ∪ a) q.support :=
    disjoint_union_left.mpr ⟨h.disjoint.mono_left (erase_subset _ _),
      c.property.blocks_disjoint ha h.block haq⟩
  obtain ⟨f⟩ := hf.partition
  let parts := BlockPartition.replacementUnion hd hB ((q.mem_support _).mpr ⟨3, rfl⟩) f
    (BlockPartition.single (QuadOn.of_clique h.second_replacement_complete.card_eq
      h.second_replacement_complete.isClique))
  have hsel : ({q.support, a} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset h.block (singleton_subset_iff.mpr ha)
  have he : insert (p.vertices 2) ((p.support.erase (p.vertices 2) ∪ a) ∪ q.support) =
      c.remainder ∪ ({q.support, a} : Finset (Finset V)).biUnion id := by
    rw [← h.paw]
    simp only [biUnion_insert, singleton_biUnion, id_eq]
    rw [← insert_union, ← insert_union, insert_erase hbF]
    ext z
    simp only [mem_union]
    tauto
  exact hn (c.complementPartition.hasPacking_of_selected_factor hcard {q.support, a} hsel
    (he ▸ parts))

theorem Configuration.no_common_leaf_third (h : Configuration c p q)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (ha : a ∈ c.blocks) (haq : a ≠ q.support) :
    ¬CommonReplacement G p.leaf (p.vertices 3) (q 3) a := by
  intro hh
  have hsub : ({p.leaf, p.center, p.vertices 3} : Finset V) ⊆ p.support := by
    rw [← p.erase_second_support]
    exact erase_subset _ _
  have hd := (h.paw_disjoint_block ha).mono_left hsub
  have hY : q 3 ∉ ({p.leaf, p.center, p.vertices 3} : Finset V) ∪ a :=
    fun hh ↦ h.exposed_outside_other ha haq ((union_subset_union hsub Subset.rfl) hh)
  have hXc : p.leaf ≠ p.vertices 3 := p.vertices.injective.ne (by decide : (0 : Fin 4) ≠ 3)
  have hf := LocalFactor.of_three_path_common p.leaf p.center (p.vertices 3) (q 3)
    hXc p.pendant p.edge13 hd hY hh
  apply h.no_missing_second_factor hcard hn ha haq
  rwa [p.erase_second_support]

theorem LowCore.no_common_column (h : LowCore c p q a) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k) :
    ∀ u ∈ a, ¬(G.Adj p.leaf u ∧ G.Adj (p.vertices 3) u) := by
  have hY : q 3 ∉ a := fun hh ↦ h.toConfiguration.exposed_outside_other h.core_block h.core_ne
    (mem_union_right _ hh)
  exact no_common_of_universal_insertion p.leaf (p.vertices 3) (q 3) a
    (h.toConfiguration.no_common_leaf_third hcard hn h.core_block h.core_ne)
    (fun _ hu ↦ (c.property.blocks_quad a h.core_block).replace_of_degree_four hY h.exposed_four hu)

theorem LowCore.third_le_one (h : LowCore c p q a) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k) : degreeIn G (p.vertices 3) a ≤ 1 := by
  have hb := degree_pair_le_card p.leaf (p.vertices 3) a (h.no_common_column hcard hn)
  rw [h.leaf_three, h.core_complete.card_eq] at hb
  omega

end UniversalTriple

end Erdos577
