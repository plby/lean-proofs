import ErdosProblems.Erdos577.FullRowSmallExcluded

/-! Wang's full-row obstruction, TeX9.42, with both distinguished-vertex locations explicit. -/

namespace Erdos577.FullRow

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem direct_obstruction {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (hleaf : ∀ i : Fin 4, i ≠ 3 → G.Adj p.leaf (q i))
    (hseven : 7 ≤ degreeIn G p.leaf q.support + degreeIn G (p.vertices 2) q.support)
    (hb3 : G.Adj (p.vertices 2) (q 3))
    {a : Finset V} (ha : a ∈ c.blocks) (has : a ≠ s)
    (hxfull : degreeIn G p.leaf a = 4) (hcfull : degreeIn G (p.vertices 3) a = 4)
    (hlast : degreeIn G (q 3) a = 1) : False := by
  obtain ⟨v, hv, hlabels⟩ := outside_labels ha (q 3) hlast
  obtain ⟨d, hd, ht, hT, _, _, hblocks, hnew⟩ :=
    exists_bounded_first_swap hc hcard hdeg hn p hp hs q hq hleaf hb3
  have had : a ∈ d.blocks := by
    rw [hblocks]
    exact mem_union_left _ (mem_erase.mpr ⟨has, ha⟩)
  have hinside := direct_inside_upper hc hcard hn p hp hs q hq hleaf hseven ha has
    hxfull hcfull hlast v hv d hd ht hT hblocks hnew
  obtain ⟨j, hj, hjs, hja, hjd, hheavy⟩ := direct_heavy hcard hdeg p hp q s hblocks ha has
    v hv hinside
  by_cases hdense : 9 ≤ contacts G d.remainder j
  · exact direct_dense_false hc hd hcard hdeg hn p hp hT ha had hxfull hcfull v hv
      hj hjd hja hheavy hdense
  · exact direct_small_false hc hcard hn p hp hT hs q hq ht hleaf hseven ha has had
      hxfull hcfull v hv hj hja hjs hheavy (by omega) ((hlabels 0).mpr rfl)

theorem other_obstruction {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (hleaf : ∀ i : Fin 4, i ≠ 3 → G.Adj p.leaf (q i))
    (hseven : 7 ≤ degreeIn G p.leaf q.support + degreeIn G (p.vertices 2) q.support)
    (hb3 : G.Adj (p.vertices 2) (q 3))
    {b : Finset V} (hb : b ∈ c.blocks) (hbs : b ≠ s)
    (z : V) (hz : z ∈ b) (hrz : G.Adj p.center z)
    (hrep : QuadOn G (insert (p.vertices 3) (b.erase z)))
    (hcore : ∀ u, u ∉ p.triangle ∪ b → 2 ≤ degreeIn G u (p.triangle ∪ b) →
      LocalFactor G (insert u (p.triangle ∪ b)))
    {a : Finset V} (ha : a ∈ c.blocks) (has : a ≠ s)
    (hxfull : degreeIn G p.leaf a = 4) (hzfull : degreeIn G z a = 4)
    (hlast : degreeIn G (q 3) a = 1) : False := by
  have hba : b ≠ a := fun he ↦
    full_row_outside (c.property.blocks_quad a ha) z hzfull (he ▸ hz)
  obtain ⟨v, hv, hlabels⟩ := outside_labels ha (q 3) hlast
  obtain ⟨d, hd, ht, hT, _, _, hblocks, hnew⟩ :=
    exists_bounded_first_swap hc hcard hdeg hn p hp hs q hq hleaf hb3
  have had : a ∈ d.blocks := by
    rw [hblocks]
    exact mem_union_left _ (mem_erase.mpr ⟨has, ha⟩)
  have hinside := other_inside_upper hc hcard hdeg hn p hp hs q hq hleaf hseven ha has
    hxfull hb hbs z hz hzfull hrep hcore hlast v hv d hd ht hT hblocks hnew
  obtain ⟨j, hj, hjs, hjb, hja, hjd, hheavy⟩ := other_heavy hcard hdeg p hp q s hblocks
    ha has hb hbs hba v hv hinside
  by_cases hdense : 9 ≤ contacts G d.remainder j
  · exact other_dense_false hc hd hcard hdeg hn p hp hT ha had hxfull v hv hj hjd hja
      hheavy hdense hb hjb.symm z hz hrz hzfull hrep
  · exact other_small_false hc hcard hn p hp hT hs q hq ht hleaf hseven ha has had
      hxfull v hv hj hja hjs hheavy (by omega) ((hlabels 0).mpr rfl) hb hbs hjb.symm
      z hz hrz hzfull hrep

theorem full_row_obstruction {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (hleaf : ∀ i : Fin 4, i ≠ 3 → G.Adj p.leaf (q i))
    (hseven : 7 ≤ degreeIn G p.leaf q.support + degreeIn G (p.vertices 2) q.support)
    (hb3 : G.Adj (p.vertices 2) (q 3)) (z : V)
    (hzloc : z = p.vertices 3 ∨ ∃ b ∈ c.blocks, b ≠ s ∧ z ∈ b ∧ G.Adj p.center z ∧
      QuadOn G (insert (p.vertices 3) (b.erase z)) ∧
      ∀ u, u ∉ p.triangle ∪ b → 2 ≤ degreeIn G u (p.triangle ∪ b) →
        LocalFactor G (insert u (p.triangle ∪ b))) :
    ¬∃ a ∈ c.blocks, a ≠ s ∧ degreeIn G p.leaf a = 4 ∧ degreeIn G z a = 4 ∧
      degreeIn G (q 3) a = 1 := by
  rintro ⟨a, ha, has, hxfull, hzfull, hlast⟩
  rcases hzloc with rfl | ⟨b, hb, hbs, hz, hrz, hrep, hcore⟩
  · exact direct_obstruction hc hcard hdeg hn p hp hs q hq hleaf hseven hb3 ha has
      hxfull hzfull hlast
  · exact other_obstruction hc hcard hdeg hn p hp hs q hq hleaf hseven hb3 hb hbs z hz
      hrz hrep hcore ha has hxfull hzfull hlast

end Erdos577.FullRow
