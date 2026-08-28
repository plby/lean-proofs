import ErdosProblems.Erdos577.WeightedFourteenWeight
import ErdosProblems.Erdos577.WeightedFourteenTerminals
import ErdosProblems.Erdos577.WeightedFourteenFactors
import ErdosProblems.Erdos577.PathMiddleReplacements
import ErdosProblems.Erdos577.TriangleRows

/-! Exclude the two low pair-sum branches when a pattern (14) terminal is heavy. -/

namespace Erdos577.WeightedFourteen

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem high_pair_seven_le {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (hheavy : 17 ≤ weight p q a)
    (hex : ∃ tag : Fin 3, 3 ≤ degreeIn G (terminal p q tag) a) :
    7 ≤ degreeIn G p.leaf a + degreeIn G (q 1) a := by
  obtain ⟨tag, h3⟩ := hex
  have hT := triangle_contacts_le_four hc hcard hn p hp hb q hq hd h tag ha hab h3
  have hcol := triangle_column_le_one hc hcard hn p hp hb q hq hd h tag ha hab h3
  have hacard : a.card = 4 := (c.property.blocks_quad a ha).card
  have hxmax : degreeIn G p.leaf a ≤ 4 := by simpa only [hacard] using degreeIn_le_card G p.leaf a
  have hymax : degreeIn G (q 1) a ≤ 4 := by simpa only [hacard] using degreeIn_le_card G (q 1) a
  have hwmax : degreeIn G (q 3) a ≤ 4 := by simpa only [hacard] using degreeIn_le_card G (q 3) a
  change 17 ≤ 2 * degreeIn G p.leaf a + 2 * degreeIn G (q 1) a + degreeIn G (q 3) a +
    contacts G p.triangle a at hheavy
  have hno := no_common_replacement hcard hn p hp hb q hq hd h ha hab
  have hda : Disjoint (p.support ∪ q.support) a := by
    rw [hp, hq, disjoint_union_left]
    refine ⟨?_, c.property.blocks_disjoint hb ha hab.symm⟩
    apply disjoint_left.mpr
    intro v hv hva
    exact (mem_sdiff.mp (c.complementPartition.block_subset ha hva)).2 hv
  have hyout : q 1 ∉ a := fun hh ↦ disjoint_left.mp hda
    (mem_union_right _ ((q.mem_support _).mpr ⟨1, rfl⟩)) hh
  by_contra! hsmall
  have h5 : 5 ≤ degreeIn G p.leaf a + degreeIn G (q 1) a := by omega
  by_cases he5 : degreeIn G p.leaf a + degreeIn G (q 1) a = 5
  · have hw3 : 3 ≤ degreeIn G (q 3) a := by omega
    have hunion : ((a.filter (G.Adj p.leaf)) ∪ (a.filter (G.Adj (q 1)))).card ≤ 4 := by
      exact (card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))).trans_eq hacard
    obtain ⟨u, hu, hxu, hyu⟩ := common_neighbor_of_union_bound p.leaf (q 1) a 4 hunion (by omega)
    exact hno 4 ⟨u, hu, hxu, hyu, terminal_universal hc p hp hb q hq hd h 2 ha hab hw3 u hu⟩
  · have he6 : degreeIn G p.leaf a + degreeIn G (q 1) a = 6 := by omega
    have hwpos : 0 < degreeIn G (q 3) a := by omega
    have hy3 : 3 ≤ degreeIn G (q 1) a := by
      by_contra! hylow
      have hx4 : degreeIn G p.leaf a = 4 := by omega
      have hy2 : degreeIn G (q 1) a = 2 := by omega
      have hcl := clique_of_full_terminal hc p hp hb q hq hd h 0 ha hab hx4
      obtain ⟨u, hu⟩ := card_pos.mp hwpos
      obtain ⟨hua, hwu⟩ := mem_filter.mp hu
      have hxu : G.Adj p.leaf u :=
        (degreeIn_eq_card_iff p.leaf a).mp (hx4.trans hacard.symm) u hua
      have hnyu : ¬G.Adj (q 1) u := fun hyu ↦ hno 0 ⟨u, hua, hyu, hwu,
        terminal_universal hc p hp hb q hq hd h 0 ha hab (by change 3 ≤ degreeIn G p.leaf a; omega)
          u hua⟩
      have he := degreeIn_erase_add G (q 1) u hua
      rw [if_neg hnyu] at he
      exact hno 2 ⟨u, hua, hxu, hwu, (clique_replace_iff_two_contacts hcl hyout hua).mpr (by omega)⟩
    have hwout : q 3 ∉ p.triangle := by
      intro hh
      exact disjoint_left.mp hd (p.support_eq ▸ mem_insert_of_mem hh)
        ((q.mem_support _).mpr ⟨3, rfl⟩)
    have hsum : contacts G a (insert (q 3) p.triangle) =
        degreeIn G (q 3) a + contacts G p.triangle a := by
      rw [contacts_comm, contacts, sum_insert hwout]
      rfl
    obtain ⟨u, hu, hdu⟩ := exists_row_gt_of_contacts (G := G) (t := a)
      (q := insert (q 3) p.triangle) (n := 1) (by rw [hacard, hsum]; omega)
    have huT := hcol u hu
    rw [degreeIn_insert G u (q 3) hwout] at hdu
    have hwu : G.Adj (q 3) u := by
      by_contra hh
      rw [if_neg (fun he ↦ hh he.symm)] at hdu
      omega
    have htpos : 0 < degreeIn G u p.triangle := by split_ifs at hdu <;> omega
    obtain ⟨j, hj⟩ := card_pos.mp htpos
    obtain ⟨hjt, huj⟩ := mem_filter.mp hj
    have hrep := terminal_universal hc p hp hb q hq hd h 1 ha hab hy3 u hu
    rcases mem_insert.mp hjt with rfl | hjt
    · exact hno 9 ⟨u, hu, huj.symm, hwu, hrep⟩
    · rcases mem_insert.mp hjt with rfl | hjt
      · exact hno 10 ⟨u, hu, huj.symm, hwu, hrep⟩
      · have hj : j = p.vertices 3 := mem_singleton.mp hjt
        subst j
        exact hno 11 ⟨u, hu, huj.symm, hwu, hrep⟩

end Erdos577.WeightedFourteen
