import ErdosProblems.Erdos577.FullLeafSparseSecondUnique

/-! TeX9.75: a vertex is sparsely attached to at most one heavy further block. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Maximal.sparse_attachment_unique (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {j l : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    (hl : l ∈ c.blocks) (hls : l ≠ s) (hla : l ≠ a)
    (hjheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j)
    (hlheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) l)
    {v : V} (hvj : FullLeafSparse.Attached G p s a y v j)
    (hvl : FullLeafSparse.Attached G p s a y v l) : j = l := by
  by_contra hjl
  obtain ⟨hsideJ, hrowJ⟩ := hvj
  obtain ⟨hsideL, hrowL⟩ := hvl
  rcases hsideJ with ⟨hvFirst, hjtype⟩ | ⟨hvSecond, hjtype⟩
  · rcases hsideL with ⟨_, hltype⟩ | ⟨hvSecond, _⟩
    · exact hm.1.type40_shared_row_false hcard hn hj hjs hja hl hls hla hjl
        hjheavy hlheavy hjtype hltype hvFirst (by omega) (by omega)
    · exact disjoint_left.mp hm.1.five_disjoint_core
        (mem_insert_of_mem (mem_erase.mp hvFirst).2) (hm.1.second_five_subset hvSecond)
  · rcases hsideL with ⟨hvFirst, _⟩ | ⟨_, hltype⟩
    · exact disjoint_left.mp hm.1.five_disjoint_core
        (mem_insert_of_mem (mem_erase.mp hvFirst).2) (hm.1.second_five_subset hvSecond)
    · exact hm.type41_shared_row_false hcard hn hj hjs hja hl hls hla hjl
        hjheavy hlheavy hjtype hltype hvSecond (by omega) (by omega)

end Erdos577.FullLeafCore
