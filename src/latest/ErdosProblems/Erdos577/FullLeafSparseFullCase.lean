import ErdosProblems.Erdos577.FullLeafSparseBlockExchange

/-! The actual maximum bounds the sparse contact sum when both marked rows are full. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Maximal.type41_contacts_le_matching_add_one (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j)
    (htype : FullLeafHeavy.Type41 G p a j)
    (hX : degreeIn G p.leaf j = 4) (hY : degreeIn G y j = 4) :
    contacts G (insert (p.vertices 3) a) j ≤
      contacts G (s.erase y) (insert (p.vertices 3) a) + 1 := by
  let h := hm.1
  obtain ⟨_, hfirst, _⟩ := h.type41_preparation hj hjs hheavy htype
  obtain ⟨d, hd, hdfull⟩ := FullLeafSparse.full_column_of_seventeen
    h.first_five_clique.card_eq (c.property.blocks_quad j hj).card hfirst
  obtain ⟨e, he, _, _⟩ := h.full_marked_block_exchange hj hjs hja hX hY hd hdfull
  have hmax := hm.2 e p (insert y (j.erase d)) a y he
  rw [h.objective_eq_matching hcard hn] at hmax
  have hYout : y ∉ j.erase d := fun hv ↦
    disjoint_left.mp (c.property.blocks_disjoint h.first hj hjs.symm)
      h.exposed (mem_erase.mp hv).2
  have hzero := (h.marked_degrees_zero hcard hn).2
  have heq : contacts G (insert (p.vertices 3) a) (insert y (j.erase d)) =
      contacts G (j.erase d) (insert (p.vertices 3) a) := by
    rw [contacts_comm, contacts, sum_insert hYout, hzero, zero_add]
    rfl
  have herase := sum_erase_add (s := j) (fun v ↦ degreeIn G v (insert (p.vertices 3) a)) hd
  change contacts G (j.erase d) (insert (p.vertices 3) a) +
    degreeIn G d (insert (p.vertices 3) a) = contacts G j (insert (p.vertices 3) a) at herase
  rw [contacts_comm G j (insert (p.vertices 3) a)] at herase
  have hcol := htype.2 d hd
  rw [heq] at hmax
  omega

theorem Maximal.type41_full_marked_refinement (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j)
    (htype : FullLeafHeavy.Type41 G p a j)
    (hX : degreeIn G p.leaf j = 4) (hY : degreeIn G y j = 4) :
    10 ≤ contacts G (s.erase y) j ∧
      (contacts G (s.erase y) j = 10 → 2 ≤ contacts G (s.erase y) (insert (p.vertices 3) a)) := by
  have hsum := hm.1.matching_add_type41_contacts_le_five hcard hn hj hjs hja hheavy htype
  have hmax := hm.type41_contacts_le_matching_add_one hcard hn hj hjs hja hheavy htype hX hY
  rw [hm.1.combined_contacts, hm.1.first_contacts, hX, hY] at hheavy
  constructor <;> omega

end Erdos577.FullLeafCore
