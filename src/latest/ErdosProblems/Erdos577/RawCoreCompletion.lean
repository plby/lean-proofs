import ErdosProblems.Erdos577.LeafTransport

/-! Core completion for an arbitrary triangle chain, without a terminal attachment or paw. -/

namespace Erdos577.TriangleChain

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem hasPacking_of_selected_core (c : TriangleChain G) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) {a : Finset V} (ha : a ∈ c.blocks)
    (bs : Finset (Finset V)) (hbs : bs ⊆ c.blocks) (hna : a ∉ bs)
    {used : Finset V} (hu : used ⊆ c.triangle ∪ a)
    (hr : QuadOn G ((c.triangle ∪ a) \ used))
    (hf : Nonempty (BlockPartition G (insert c.terminal (used ∪ bs.biUnion id)))) :
    HasPacking G k := by
  have hRA : Disjoint c.remainder a :=
    c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
  have hRO : Disjoint c.remainder (bs.biUnion id) :=
    c.property.remainder_disjoint.mono_right (biUnion_subset_biUnion_of_subset_left id hbs)
  have hAO : Disjoint a (bs.biUnion id) := by
    apply disjoint_left.mpr
    intro v hv hvo
    obtain ⟨b, hb, hvb⟩ := mem_biUnion.mp hvo
    exact disjoint_left.mp (c.property.blocks_disjoint ha (hbs hb)
      (fun he ↦ hna (he.symm ▸ hb))) hv hvb
  have hT : c.triangle ⊆ c.remainder := subset_insert _ _
  have hKO : Disjoint (c.triangle ∪ a) (bs.biUnion id) :=
    disjoint_union_left.mpr ⟨hRO.mono_left hT, hAO⟩
  have hx : c.terminal ∉ (c.triangle ∪ a) ∪ bs.biUnion id := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · rcases mem_union.mp hh with hh | hh
      · exact c.property.terminal_not_mem hh
      · exact disjoint_left.mp hRA (mem_insert_self _ _) hh
    · exact disjoint_left.mp hRO (mem_insert_self _ _) hh
  obtain ⟨parts⟩ := TwoCore.partition_with_core_complement hKO hx hu hr hf
  have hsel : insert a bs ⊆ c.blocks := insert_subset ha hbs
  have he : insert c.terminal ((c.triangle ∪ a) ∪ bs.biUnion id) =
      c.remainder ∪ (insert a bs).biUnion id := by
    rw [← insert_union, ← insert_union]
    change c.remainder ∪ a ∪ bs.biUnion id = _
    simp only [biUnion_insert, id_eq, union_assoc]
  exact c.complementPartition.hasPacking_of_selected_factor hcard (insert a bs) hsel (he ▸ parts)

end Erdos577.TriangleChain
