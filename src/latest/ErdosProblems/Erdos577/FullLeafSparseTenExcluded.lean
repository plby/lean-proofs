import ErdosProblems.Erdos577.FullLeafSparseRowCover

/-! A ten-contact type41 block excludes every other heavy block of that type. -/

namespace Erdos577.FullLeafSparse

open Finset

variable {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj]

lemma full_row_of_ten {t j : Finset V} (ht : t.card = 3) (hj : j.card = 4)
    (hsum : 10 ≤ contacts G t j) : ∃ x ∈ t, degreeIn G x j = 4 := by
  classical
  by_contra! hnone
  have hbound : contacts G t j ≤ 9 := by
    calc
      contacts G t j ≤ ∑ _ ∈ t, (3 : ℕ) := by
        apply sum_le_sum
        intro x hx
        have hh := hnone x hx
        have hb := degreeIn_le_card G x j
        rw [hj] at hb
        omega
      _ = 9 := by rw [sum_const, smul_eq_mul, ht]
  omega

end Erdos577.FullLeafSparse

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Maximal.type41_ten_contacts_false (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {j l : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    (hl : l ∈ c.blocks) (hls : l ≠ s) (hla : l ≠ a) (hjl : j ≠ l)
    (hjheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j)
    (hlheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) l)
    (hjtype : FullLeafHeavy.Type41 G p a j) (hltype : FullLeafHeavy.Type41 G p a l)
    (hten : contacts G (s.erase y) j = 10) : False := by
  let h := hm.1
  have hrho := (hm.type41_refinement hcard hn hj hjs hja hjheavy hjtype).2.2 hten
  have hsum := h.matching_add_type41_contacts_le_five hcard hn hj hjs hja hjheavy hjtype
  have hXbound := degreeIn_le_card G p.leaf j
  have hYbound := degreeIn_le_card G y j
  rw [(c.property.blocks_quad j hj).card] at hXbound hYbound
  have htotal := hjheavy
  rw [h.combined_contacts, h.first_contacts, hten] at htotal
  have hrhoEq : contacts G (s.erase y) (insert (p.vertices 3) a) = 2 := by omega
  have hthree : contacts G (insert (p.vertices 3) a) j = 3 := by omega
  obtain ⟨x, hx, hxFull⟩ := FullLeafSparse.full_row_of_ten h.first_triple_clique.card_eq
    (c.property.blocks_quad j hj).card hten.ge
  have hxAll := (degreeIn_eq_card_iff x j).mp
    (hxFull.trans (c.property.blocks_quad j hj).card.symm)
  have hcolumn (e : V) (hel : e ∈ l) :
      degreeIn G e (s.erase y) + degreeIn G e (insert (p.vertices 3) a) ≤ 3 := by
    have hsecond := hltype.2 e hel
    have hfirst := degreeIn_le_card G e (s.erase y)
    rw [h.first_triple_clique.card_eq] at hfirst
    by_cases hzero : degreeIn G e (insert (p.vertices 3) a) = 0
    · omega
    have hpos : 0 < degreeIn G e (insert (p.vertices 3) a) := by omega
    obtain ⟨v, hv⟩ := card_pos.mp hpos
    obtain ⟨hv, hev⟩ := mem_filter.mp hv
    have hvl : 0 < degreeIn G v l := card_pos.mpr ⟨e, mem_filter.mpr ⟨hel, hev.symm⟩⟩
    have hvj := h.sparse_rows_subset_of_equality hcard hn hj hjs hja hl hls hla
      hjheavy hlheavy hjtype hltype hrhoEq hthree hv hvl
    obtain ⟨d, hd⟩ := card_pos.mp hvj
    obtain ⟨hdj, hvd⟩ := mem_filter.mp hd
    have hnxe : ¬G.Adj x e := fun hxe ↦ hm.type41_common_column_false hcard hn
      hj hjs hja hl hls hla hjl hjheavy hlheavy hjtype hltype hv hdj hel
        hvd hev.symm hx (hxAll d hdj) hxe
    have herase := degreeIn_erase_add G e x hx
    rw [if_neg (fun hh ↦ hnxe hh.symm), add_zero] at herase
    have hbound := degreeIn_le_card G e ((s.erase y).erase x)
    rw [card_erase_of_mem hx, h.first_triple_clique.card_eq] at hbound
    omega
  have hbound := sum_le_sum hcolumn
  rw [sum_add_distrib, sum_const, smul_eq_mul, (c.property.blocks_quad l hl).card] at hbound
  change contacts G l (s.erase y) + contacts G l (insert (p.vertices 3) a) ≤ 4 * 3 at hbound
  rw [contacts_comm G l (s.erase y), contacts_comm G l (insert (p.vertices 3) a)] at hbound
  have hX := degreeIn_le_card G p.leaf l
  have hY := degreeIn_le_card G y l
  rw [(c.property.blocks_quad l hl).card] at hX hY
  rw [h.combined_contacts, h.first_contacts] at hlheavy
  omega

end Erdos577.FullLeafCore
