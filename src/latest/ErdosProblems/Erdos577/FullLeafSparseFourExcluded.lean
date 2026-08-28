import ErdosProblems.Erdos577.FullLeafSparseCoreExchange

/-! Four sparse contacts would produce a strictly better maximizing configuration. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

lemma Configuration.exchanged_second_set (h : Configuration c p s a y) (z : V) :
    insert (p.vertices 2) ((p.triangle ∪ a) \ {p.center, z, p.vertices 2}) =
      insert (p.vertices 2) ((insert (p.vertices 3) a).erase z) := by
  rw [h.second_five_eq]
  ext v
  simp only [mem_insert, mem_sdiff, mem_singleton, mem_erase]
  tauto

theorem Maximal.type41_four_contacts_false (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j)
    (htype : FullLeafHeavy.Type41 G p a j) (hX : degreeIn G p.leaf j = 4)
    (hfour : contacts G (insert (p.vertices 3) a) j = 4) : False := by
  let h := hm.1
  let u := (insert (p.vertices 3) a).filter (fun v ↦ 0 < degreeIn G v j)
  have hu4 : u.card = 4 := by
    rw [← FullLeafSparse.contacts_eq_positive_rows htype.1]
    exact hfour
  obtain ⟨z, hz, hrz, hzb, hrem⟩ := h.center_path_through_four (filter_subset _ _) hu4
  obtain ⟨hzSecond, hzpos⟩ := mem_filter.mp hz
  have hzone : degreeIn G z j = 1 := by
    have hle := htype.1 z hzSecond
    omega
  have hbzero := (h.center_rows_zero_of_four hcard hn hj hjs hja hX hfour).2
  obtain ⟨e, q, w, he, _, hthird, _, _⟩ :=
    h.core_triangle_exchange hj hja hX hzSecond hrz hzb hrem hzpos
  have hmax := hm.2 e q j ((p.triangle ∪ a) \ {p.center, z, p.vertices 2}) w he
  have hbout : p.vertices 2 ∉ (insert (p.vertices 3) a).erase z :=
    fun hv ↦ (h.second_avoids (mem_erase.mp hv).2).2.2 rfl
  have herase := sum_erase_add (s := insert (p.vertices 3) a) (fun v ↦ degreeIn G v j) hzSecond
  change contacts G ((insert (p.vertices 3) a).erase z) j + degreeIn G z j =
    contacts G (insert (p.vertices 3) a) j at herase
  rw [hzone, hfour] at herase
  have hthree : contacts G (insert (q.vertices 3)
      ((p.triangle ∪ a) \ {p.center, z, p.vertices 2})) j = 3 := by
    rw [hthird, h.exchanged_second_set, contacts, sum_insert hbout, hbzero, zero_add]
    change contacts G ((insert (p.vertices 3) a).erase z) j = 3
    omega
  rw [hthree, h.objective_eq_matching hcard hn] at hmax
  have hsum := h.matching_add_type41_contacts_le_five hcard hn hj hjs hja hheavy htype
  omega

end Erdos577.FullLeafCore
