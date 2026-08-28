import ErdosProblems.Erdos577.FullLeafSparseCommonExcluded

/-! At equality, three sparse rows and two matching endpoints exhaust the second five-set. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}
variable (h : Configuration c p s a y)

include h

lemma Configuration.type41_sparse_rows_avoid_matching {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j)
    (htype : FullLeafHeavy.Type41 G p a j) :
    Disjoint ((insert (p.vertices 3) a).filter (fun v ↦ 0 < degreeIn G v (s.erase y)))
      ((insert (p.vertices 3) a).filter (fun v ↦ 0 < degreeIn G v j)) := by
  apply disjoint_left.mpr
  intro v hvm hvj
  obtain ⟨hv, hpos⟩ := mem_filter.mp hvm
  obtain ⟨x, hx⟩ := card_pos.mp hpos
  obtain ⟨hx, hvx⟩ := mem_filter.mp hx
  have hz := h.type41_matching_endpoint_zero hcard hn hj hjs hja hheavy htype hx hv hvx.symm
  have hh := (mem_filter.mp hvj).2
  omega

theorem Configuration.sparse_rows_subset_of_equality {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {j l : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    (hl : l ∈ c.blocks) (hls : l ≠ s) (hla : l ≠ a)
    (hjheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j)
    (hlheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) l)
    (hjtype : FullLeafHeavy.Type41 G p a j) (hltype : FullLeafHeavy.Type41 G p a l)
    (hrho : contacts G (s.erase y) (insert (p.vertices 3) a) = 2)
    (hthree : contacts G (insert (p.vertices 3) a) j = 3)
    {v : V} (hv : v ∈ insert (p.vertices 3) a) (hvl : 0 < degreeIn G v l) :
    0 < degreeIn G v j := by
  let m := (insert (p.vertices 3) a).filter (fun v ↦ 0 < degreeIn G v (s.erase y))
  let u := (insert (p.vertices 3) a).filter (fun v ↦ 0 < degreeIn G v j)
  have hm : m.card = 2 := by
    rw [← FullLeafSparse.contacts_eq_positive_rows (h.matching_degrees hcard hn).2,
      contacts_comm]
    exact hrho
  have hu : u.card = 3 := by
    rw [← FullLeafSparse.contacts_eq_positive_rows hjtype.1]
    exact hthree
  have hd : Disjoint m u :=
    h.type41_sparse_rows_avoid_matching hcard hn hj hjs hja hjheavy hjtype
  have heq : m ∪ u = insert (p.vertices 3) a := by
    apply eq_of_subset_of_card_le (union_subset (filter_subset _ _) (filter_subset _ _))
    rw [card_union_of_disjoint hd, hm, hu, h.second_five_card]
  have hvm : v ∉ m := fun hh ↦ disjoint_left.mp
    (h.type41_sparse_rows_avoid_matching hcard hn hl hls hla hlheavy hltype)
      hh (mem_filter.mpr ⟨hv, hvl⟩)
  have hvu : v ∈ u := (mem_union.mp (heq.symm ▸ hv)).resolve_left hvm
  exact (mem_filter.mp hvu).2

end Erdos577.FullLeafCore
