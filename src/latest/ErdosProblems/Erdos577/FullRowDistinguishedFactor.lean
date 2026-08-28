import ErdosProblems.Erdos577.FullRowCommonFactor

/-! Complete an actual factor with the distinguished fourth paw vertex in either location. -/

namespace Erdos577.FullRow

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem hasPacking_of_distinguished_direct {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (p : Paw G) (hp : p.support = c.remainder)
    (bs : Finset (Finset V)) (hbs : bs ⊆ c.blocks)
    (hf : Nonempty (BlockPartition G (insert (p.vertices 3) (pathTriple p ∪ bs.biUnion id)))) :
    HasPacking G k := by
  obtain ⟨parts⟩ := hf
  have he : insert (p.vertices 3) (pathTriple p ∪ bs.biUnion id) =
      c.remainder ∪ bs.biUnion id := by
    rw [← insert_union, insert_third_pathTriple, hp]
  exact c.complementPartition.hasPacking_of_selected_factor hcard bs hbs (he ▸ parts)

theorem hasPacking_of_distinguished_other {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (p : Paw G) (hp : p.support = c.remainder)
    (bs : Finset (Finset V)) (hbs : bs ⊆ c.blocks)
    {b : Finset V} (hb : b ∈ c.blocks) (hbn : b ∉ bs) {z : V} (hz : z ∈ b)
    (hrep : QuadOn G (insert (p.vertices 3) (b.erase z)))
    (hf : Nonempty (BlockPartition G (insert z (pathTriple p ∪ bs.biUnion id)))) :
    HasPacking G k := by
  obtain ⟨parts⟩ := hf
  have hpdis : Disjoint p.support b := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hb)
  have hbsdis : Disjoint (bs.biUnion id) b := by
    rw [disjoint_biUnion_left]
    intro a ha
    exact c.property.blocks_disjoint (hbs ha) hb (fun he ↦ hbn (he ▸ ha))
  have hd : Disjoint (pathTriple p ∪ bs.biUnion id) b :=
    disjoint_union_left.mpr ⟨hpdis.mono_left (pathTriple_subset p), hbsdis⟩
  have hthird : p.vertices 3 ∈ c.remainder := hp ▸ (mem_tupleSupport p.vertices _).mpr ⟨3, rfl⟩
  have hout : p.vertices 3 ∉ (pathTriple p ∪ bs.biUnion id) ∪ b := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · rcases mem_union.mp hh with hh | hh
      · exact third_not_mem_pathTriple p hh
      · have hU := biUnion_subset_biUnion_of_subset_left id hbs hh
        exact disjoint_left.mp c.property.remainder_disjoint hthird hU
    · exact (mem_sdiff.mp (c.complementPartition.block_subset hb hh)).2 hthird
  let all := BlockPartition.replacementUnion hd hout hz parts (BlockPartition.single hrep)
  have he : insert (p.vertices 3) ((pathTriple p ∪ bs.biUnion id) ∪ b) =
      c.remainder ∪ (insert b bs).biUnion id := by
    rw [← insert_union, ← insert_union, insert_third_pathTriple, hp]
    simp only [biUnion_insert, id_eq, union_assoc, union_comm]
  exact c.complementPartition.hasPacking_of_selected_factor hcard (insert b bs)
    (insert_subset hb hbs) (he ▸ all)

end Erdos577.FullRow
