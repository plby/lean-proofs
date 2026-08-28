import ErdosProblems.Erdos577.MultiScores
import ErdosProblems.Erdos577.PawTerminalExchange

/-! Exact supports for the crossing complete block in the strict CaseI score gain. -/

namespace Erdos577.JointFirst

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma crossing_clique (j : Quadrilateral G) {z1 z2 : V} (hz : G.Adj z1 z2)
    (h11 : G.Adj z1 (j 1)) (h12 : G.Adj z1 (j 2))
    (h21 : G.Adj z2 (j 1)) (h22 : G.Adj z2 (j 2)) :
    G.IsNClique 4 {z1, z2, j 1, j 2} := by
  have ht : G.IsNClique 3 {z2, j 1, j 2} :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨h21, h22, j.adjacent 1⟩
  apply ht.insert
  intro v hv
  simp only [mem_insert, mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · exact hz
  · exact h11
  · exact h12

variable [Fintype V]

theorem crossing_gain_geometry (c : TriangleChain G) {a : Finset V} (ha : a ∈ c.blocks)
    (j : Quadrilateral G) (hj : j.support ∈ c.blocks) (haj : a ≠ j.support)
    (primary : Finset V) (hp : QuadOn G primary) (hpsub : primary ⊆ c.triangle ∪ a)
    {z1 z2 : V} (h1 : z1 ∈ a) (h2 : z2 ∈ a) (h1p : z1 ∉ primary) (h2p : z2 ∉ primary)
    (hb : G.IsNClique 4 {z1, z2, j 1, j 2})
    (hx0 : G.Adj c.terminal (j 0)) (hx3 : G.Adj c.terminal (j 3)) :
    Disjoint primary {z1, z2, j 1, j 2} ∧
    primary ∪ {z1, z2, j 1, j 2} ⊆ c.remainder ∪ (a ∪ j.support) ∧
    ((c.remainder ∪ (a ∪ j.support)) \ (primary ∪ {z1, z2, j 1, j 2})).card = 4 ∧
    TriangleIn G ((c.remainder ∪ (a ∪ j.support)) \ (primary ∪ {z1, z2, j 1, j 2})) := by
  have hFJ : Disjoint c.remainder j.support :=
    c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hj)
  have hFA : Disjoint c.remainder a :=
    c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
  have hAJ : Disjoint a j.support := c.property.blocks_disjoint ha hj haj
  have hTF : c.triangle ⊆ c.remainder := subset_insert _ _
  have hPJ : Disjoint primary j.support :=
    (disjoint_union_left.mpr ⟨hFJ.mono_left hTF, hAJ⟩).mono_left hpsub
  have hjmem (i : Fin 4) : j i ∈ j.support := (j.mem_support _).mpr ⟨i, rfl⟩
  have hdis : Disjoint primary {z1, z2, j 1, j 2} :=
    disjoint_insert_right.mpr ⟨h1p, disjoint_insert_right.mpr ⟨h2p,
      disjoint_insert_right.mpr ⟨fun hh ↦ disjoint_left.mp hPJ hh (hjmem 1),
        disjoint_singleton_right.mpr (fun hh ↦ disjoint_left.mp hPJ hh (hjmem 2))⟩⟩⟩
  have hsub : primary ∪ {z1, z2, j 1, j 2} ⊆ c.remainder ∪ (a ∪ j.support) := by
    apply union_subset
    · intro v hv
      rcases mem_union.mp (hpsub hv) with hv | hv
      · exact mem_union_left _ (hTF hv)
      · exact mem_union_right _ (mem_union_left _ hv)
    · exact insert_subset (mem_union_right _ (mem_union_left _ h1))
        (insert_subset (mem_union_right _ (mem_union_left _ h2))
          (insert_subset (mem_union_right _ (mem_union_right _ (hjmem 1)))
            (singleton_subset_iff.mpr (mem_union_right _ (mem_union_right _ (hjmem 2))))))
  have hcard : ((c.remainder ∪ (a ∪ j.support)) \ (primary ∪ {z1, z2, j 1, j 2})).card = 4 := by
    rw [card_sdiff_of_subset hsub,
      card_union_of_disjoint (disjoint_union_right.mpr ⟨hFA, hFJ⟩),
      card_union_of_disjoint hAJ, card_union_of_disjoint hdis,
      c.card_remainder, (c.property.blocks_quad a ha).card, j.card_support, hp.card, hb.card_eq]
  have hxp : c.terminal ∉ primary := by
    intro hh
    rcases mem_union.mp (hpsub hh) with hh | hh
    · exact c.property.terminal_not_mem hh
    · exact c.terminal_not_mem_block ha hh
  have hxB : c.terminal ∉ ({z1, z2, j 1, j 2} : Finset V) := by
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨fun he ↦ c.terminal_not_mem_block ha (he.symm ▸ h1),
      fun he ↦ c.terminal_not_mem_block ha (he.symm ▸ h2),
      fun he ↦ c.terminal_not_mem_block hj (he.symm ▸ hjmem 1),
      fun he ↦ c.terminal_not_mem_block hj (he.symm ▸ hjmem 2)⟩
  have hjP (i : Fin 4) : j i ∉ primary := fun hh ↦ disjoint_left.mp hPJ hh (hjmem i)
  have hjB (i : Fin 4) (hi1 : i ≠ 1) (hi2 : i ≠ 2) :
      j i ∉ ({z1, z2, j 1, j 2} : Finset V) := by
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨fun he ↦ disjoint_left.mp hAJ (he ▸ h1) (hjmem i),
      fun he ↦ disjoint_left.mp hAJ (he ▸ h2) (hjmem i),
      j.injective.ne hi1, j.injective.ne hi2⟩
  have htriSub : ({c.terminal, j 0, j 3} : Finset V) ⊆
      (c.remainder ∪ (a ∪ j.support)) \ (primary ∪ {z1, z2, j 1, j 2}) := by
    apply insert_subset
    · exact mem_sdiff.mpr ⟨mem_union_left _ (mem_insert_self _ _),
        fun hh ↦ (mem_union.mp hh).elim hxp hxB⟩
    · apply insert_subset
      · exact mem_sdiff.mpr ⟨mem_union_right _ (mem_union_right _ (hjmem 0)),
          fun hh ↦ (mem_union.mp hh).elim (hjP 0) (hjB 0 (by decide) (by decide))⟩
      · exact singleton_subset_iff.mpr (mem_sdiff.mpr
          ⟨mem_union_right _ (mem_union_right _ (hjmem 3)),
            fun hh ↦ (mem_union.mp hh).elim (hjP 3) (hjB 3 (by decide) (by decide))⟩)
  have htri : G.IsNClique 3 {c.terminal, j 0, j 3} :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨hx0, hx3, (j.adjacent 3).symm⟩
  exact ⟨hdis, hsub, hcard, {c.terminal, j 0, j 3}, htriSub, htri⟩

end Erdos577.JointFirst
