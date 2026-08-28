import ErdosProblems.Erdos577.FullLeafSparseCommonFactor

/-! The neighboring columns of any shared second-side attachment have no common triple neighbor. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Maximal.type41_common_column_false (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {j l : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    (hl : l ∈ c.blocks) (hls : l ≠ s) (hla : l ≠ a) (hjl : j ≠ l)
    (hjheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j)
    (hlheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) l)
    (hjtype : FullLeafHeavy.Type41 G p a j) (hltype : FullLeafHeavy.Type41 G p a l)
    {v d e x : V} (hv : v ∈ insert (p.vertices 3) a) (hdj : d ∈ j) (hel : e ∈ l)
    (hvd : G.Adj v d) (hve : G.Adj v e) (hx : x ∈ s.erase y)
    (hxd : G.Adj x d) (hxe : G.Adj x e) : False := by
  let h := hm.1
  obtain ⟨hJcl, hJ, _⟩ := hm.type41_refinement hcard hn hj hjs hja hjheavy hjtype
  obtain ⟨hLcl, hL, _⟩ := hm.type41_refinement hcard hn hl hls hla hlheavy hltype
  have htSub : s.erase y ⊆ insert p.leaf s :=
    fun _ hw ↦ mem_insert_of_mem (mem_erase.mp hw).2
  have hd : Disjoint (s.erase y) (j ∪ l) :=
    (disjoint_union_right.mpr
      ⟨h.five_disjoint_block hj hjs, h.five_disjoint_block hl hls⟩).mono_left htSub
  have hvout : v ∉ (s.erase y) ∪ (j ∪ l) := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · exact disjoint_left.mp h.five_disjoint_core (htSub hh) (h.second_five_subset hv)
    · rcases mem_union.mp hh with hh | hh
      · exact disjoint_left.mp (h.core_disjoint_block hj hja) (h.second_five_subset hv) hh
      · exact disjoint_left.mp (h.core_disjoint_block hl hla) (h.second_five_subset hv) hh
  have hf := FullLeafSparse.common_column_factor_of_ten h.first_triple_clique.card_eq
    hJcl hLcl hd (c.property.blocks_disjoint hj hl hjl) hvout hdj hel hvd hve hJ hL hx hxd hxe
  exact h.second_no_double_partition hcard hn hv hj hjs hja hl hls hla hf

end Erdos577.FullLeafCore
