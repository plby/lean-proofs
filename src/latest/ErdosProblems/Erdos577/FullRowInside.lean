import ErdosProblems.Erdos577.FullRowInsideCounts

/-! The two six-row inside upper bounds in Wang's full-row obstruction. -/

namespace Erdos577.FullRow

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem direct_inside_upper {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (hleaf : ∀ j : Fin 4, j ≠ 3 → G.Adj p.leaf (q j))
    (hseven : 7 ≤ degreeIn G p.leaf q.support + degreeIn G (p.vertices 2) q.support)
    {a : Finset V} (ha : a ∈ c.blocks) (has : a ≠ s)
    (hxfull : degreeIn G p.leaf a = 4) (hcfull : degreeIn G (p.vertices 3) a = 4)
    (hlast : degreeIn G (q 3) a = 1)
    (v : Quadrilateral G) (hv : v.support = a)
    (d : TriangleChain G) (hd : d.Strong)
    (ht : d.terminal = q 3) (hT : d.triangle = p.triangle)
    (hblocks : d.blocks = c.blocks.erase s ∪ {insert p.leaf (s.erase (q 3))})
    (hnew : contacts G d.remainder (insert p.leaf (s.erase (q 3))) ≤ 8) :
    contacts G (CoreTransfer.rows d v)
      (d.remainder ∪ (insert p.leaf (s.erase (q 3)) ∪ a)) ≤ 33 := by
  let t := insert p.leaf (s.erase (q 3))
  have hA : a ∈ d.blocks := by
    rw [hblocks]
    exact mem_union_left _ (mem_erase.mpr ⟨has, ha⟩)
  have hvd : v.support ∈ d.blocks := hv.symm ▸ hA
  have hcover : d.remainder ∪ t = p.support ∪ q.support := by
    change d.remainder ∪ insert p.leaf (s.erase (q 3)) = _
    rw [← hq]
    exact first_swap_cover p q d ht hT
  have hlow (i : Fin 4) : degreeIn G (v i) (d.remainder ∪ (t ∪ a)) ≤ 6 := by
    rw [← union_assoc, hcover, union_assoc]
    exact direct_vertex_inside_le_six hc hcard hn p hp hs q hq hleaf hseven ha has
      hxfull hcfull (v i) (hv ▸ (v.mem_support _).mpr ⟨i, rfl⟩)
  have hself := hd.remainder_self_contacts hcard hn
  have hAc := direct_swapped_contacts hc hcard hn p hp q d ht hT ha hxfull hcfull hlast
  have hta := contacts_union_right_le (G := G) d.remainder t a
  have htotal := contacts_union_right_le (G := G) d.remainder d.remainder (t ∪ a)
  have hid := CoreTransfer.rows_contacts d v hvd (d.remainder ∪ (t ∪ a))
  have h1 := hlow 1
  have h3 := hlow 3
  change contacts G d.remainder t ≤ 8 at hnew
  change contacts G (CoreTransfer.rows d v) (d.remainder ∪ (t ∪ a)) ≤ 33
  omega

theorem other_inside_upper {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (hleaf : ∀ j : Fin 4, j ≠ 3 → G.Adj p.leaf (q j))
    (hseven : 7 ≤ degreeIn G p.leaf q.support + degreeIn G (p.vertices 2) q.support)
    {a : Finset V} (ha : a ∈ c.blocks) (has : a ≠ s) (hxfull : degreeIn G p.leaf a = 4)
    {b : Finset V} (hb : b ∈ c.blocks) (hbs : b ≠ s)
    (z : V) (hz : z ∈ b) (hzfull : degreeIn G z a = 4)
    (hrep : QuadOn G (insert (p.vertices 3) (b.erase z)))
    (hcore : ∀ w, w ∉ p.triangle ∪ b → 2 ≤ degreeIn G w (p.triangle ∪ b) →
      LocalFactor G (insert w (p.triangle ∪ b)))
    (hlast : degreeIn G (q 3) a = 1)
    (v : Quadrilateral G) (hv : v.support = a)
    (d : TriangleChain G) (hd : d.Strong)
    (ht : d.terminal = q 3) (hT : d.triangle = p.triangle)
    (hblocks : d.blocks = c.blocks.erase s ∪ {insert p.leaf (s.erase (q 3))})
    (hnew : contacts G d.remainder (insert p.leaf (s.erase (q 3))) ≤ 8) :
    contacts G (CoreTransfer.rows d v)
      (d.remainder ∪ (insert p.leaf (s.erase (q 3)) ∪ (b ∪ a))) ≤ 41 := by
  let t := insert p.leaf (s.erase (q 3))
  have hA : a ∈ d.blocks := by
    rw [hblocks]
    exact mem_union_left _ (mem_erase.mpr ⟨has, ha⟩)
  have hB : b ∈ d.blocks := by
    rw [hblocks]
    exact mem_union_left _ (mem_erase.mpr ⟨hbs, hb⟩)
  have hvd : v.support ∈ d.blocks := hv.symm ▸ hA
  have hcover : d.remainder ∪ t = p.support ∪ q.support := by
    change d.remainder ∪ insert p.leaf (s.erase (q 3)) = _
    rw [← hq]
    exact first_swap_cover p q d ht hT
  have hlow (i : Fin 4) : degreeIn G (v i) (d.remainder ∪ (t ∪ (b ∪ a))) ≤ 6 := by
    rw [← union_assoc, hcover, union_assoc]
    exact other_vertex_inside_le_six hc hcard hn p hp hs q hq hleaf hseven ha has
      hxfull hb hbs z hz hzfull hrep hcore (v i) (hv ▸ (v.mem_support _).mpr ⟨i, rfl⟩)
  have hself := hd.remainder_self_contacts hcard hn
  have hAc := other_swapped_contacts hc hcard hn p hp q d ht hT ha hxfull hb z hz hzfull
    hcore hlast
  have hBc := hd.block_contacts_le_twelve hcard hdeg hn hB
  have hba := contacts_union_right_le (G := G) d.remainder b a
  have htba := contacts_union_right_le (G := G) d.remainder t (b ∪ a)
  have htotal := contacts_union_right_le (G := G) d.remainder d.remainder (t ∪ (b ∪ a))
  have hid := CoreTransfer.rows_contacts d v hvd (d.remainder ∪ (t ∪ (b ∪ a)))
  have h1 := hlow 1
  have h3 := hlow 3
  change contacts G d.remainder t ≤ 8 at hnew
  change contacts G (CoreTransfer.rows d v) (d.remainder ∪ (t ∪ (b ∪ a))) ≤ 41
  omega

end Erdos577.FullRow
