import ErdosProblems.Erdos577.WeightedFourteenHighLow
import ErdosProblems.Erdos577.PawColumnCount
import ErdosProblems.Erdos577.PathColumnCount

/-! A heavy terminal would force both principal rows to be full and the third row empty. -/

namespace Erdos577.WeightedFourteen

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem high_rows_full {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (hheavy : 17 ≤ weight p q a)
    (hex : ∃ tag : Fin 3, 3 ≤ degreeIn G (terminal p q tag) a) :
    G.IsNClique 4 a ∧ degreeIn G p.leaf a = 4 ∧ degreeIn G (q 1) a = 4 ∧
      degreeIn G (q 3) a = 0 ∧ 0 < degreeIn G p.center a := by
  have h7 := high_pair_seven_le hc hcard hn p hp hb q hq hd h ha hab hheavy hex
  obtain ⟨tag, h3⟩ := hex
  have hcol := triangle_column_le_one hc hcard hn p hp hb q hq hd h tag ha hab h3
  have hacard : a.card = 4 := (c.property.blocks_quad a ha).card
  have hxmax : degreeIn G p.leaf a ≤ 4 := by simpa only [hacard] using degreeIn_le_card G p.leaf a
  have hymax : degreeIn G (q 1) a ≤ 4 := by simpa only [hacard] using degreeIn_le_card G (q 1) a
  have hx3 : 3 ≤ degreeIn G p.leaf a := by omega
  have hy3 : 3 ≤ degreeIn G (q 1) a := by omega
  have hfull : degreeIn G p.leaf a = 4 ∨ degreeIn G (q 1) a = 4 := by omega
  have hcl : G.IsNClique 4 a := by
    rcases hfull with hx | hy
    · exact clique_of_full_terminal hc p hp hb q hq hd h 0 ha hab hx
    · exact clique_of_full_terminal hc p hp hb q hq hd h 1 ha hab hy
  have hrepX := terminal_universal hc p hp hb q hq hd h 0 ha hab hx3
  have hrepY := terminal_universal hc p hp hb q hq hd h 1 ha hab hy3
  have hno := no_common_replacement hcard hn p hp hb q hq hd h ha hab
  have hw0 : degreeIn G (q 3) a = 0 := by
    apply (degreeIn_eq_zero_iff (G := G) _ _).mpr
    intro u hu hwu
    rcases hfull with hx | hy
    · have hxu := (degreeIn_eq_card_iff p.leaf a).mp (hx.trans hacard.symm) u hu
      exact hno 2 ⟨u, hu, hxu, hwu, hrepY u hu⟩
    · have hyu := (degreeIn_eq_card_iff (q 1) a).mp (hy.trans hacard.symm) u hu
      exact hno 0 ⟨u, hu, hyu, hwu, hrepX u hu⟩
  have hxb (u : V) (hu : u ∈ a) (hxu : G.Adj p.leaf u) : ¬G.Adj (p.vertices 2) u :=
    fun hbu ↦ hno 6 ⟨u, hu, hxu, hbu, hrepY u hu⟩
  have hxc (u : V) (hu : u ∈ a) (hxu : G.Adj p.leaf u) : ¬G.Adj (p.vertices 3) u :=
    fun hcu ↦ hno 7 ⟨u, hu, hxu, hcu, hrepY u hu⟩
  have hcount := p.leaf_triangle_count_bound a hcol hxb hxc
  rw [hacard] at hcount
  change 17 ≤ 2 * degreeIn G p.leaf a + 2 * degreeIn G (q 1) a + degreeIn G (q 3) a +
    contacts G p.triangle a at hheavy
  have he8 : degreeIn G p.leaf a + degreeIn G (q 1) a = 8 := by
    by_contra hne
    have hr2 : 2 ≤ degreeIn G p.center a := by omega
    let I := (a.filter (G.Adj p.leaf)) ∩ (a.filter (G.Adj (q 1)))
    have hI : 3 ≤ I.card := common_intersection_three a (a.filter (G.Adj p.leaf))
      (a.filter (G.Adj (q 1))) (filter_subset _ _) (filter_subset _ _) hacard h7
    have hIa : I ⊆ a := inter_subset_left.trans (filter_subset _ _)
    have hrout : p.center ∉ a := by
      intro hh
      have hr : p.center ∈ c.remainder := hp ▸ (mem_tupleSupport p.vertices _).mpr ⟨1, rfl⟩
      exact (mem_sdiff.mp (c.complementPartition.block_subset ha hh)).2 hr
    obtain ⟨u, hu, hrep⟩ := clique_replace_in_three_candidates hcl p.center hrout hr2 I hIa hI
    obtain ⟨hux, huy⟩ := mem_inter.mp hu
    exact hno 8 ⟨u, (mem_filter.mp hux).1, (mem_filter.mp hux).2, (mem_filter.mp huy).2, hrep⟩
  exact ⟨hcl, by omega, by omega, hw0, by omega⟩

end Erdos577.WeightedFourteen
