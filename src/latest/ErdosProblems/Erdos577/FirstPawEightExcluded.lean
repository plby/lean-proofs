import ErdosProblems.Erdos577.FirstPawEightLeafExcluded

/-! Complete exclusion of pattern (8), including both possible actual high-pair terminals. -/

namespace Erdos577

open Finset FirstPawEight

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem TriangleChain.Feasible.not_first_paw_pattern8 {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (h : PawBlock.Pattern8 p q) : False := by
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    apply disjoint_left.mpr
    intro u hu hub
    exact (mem_sdiff.mp (c.complementPartition.block_subset hb hub)).2 hu
  obtain ⟨a, ha, hab, hheavy⟩ := heavy_block hcard hdeg hn p hp hb q hq hd h
  obtain ⟨v, hv, hpat, hthree, hdv, hrows⟩ :=
    exists_first_low_three hc hcard hn p hp hb q hq hd h ha hab hheavy
  have hvb := hv.trans hq
  have hheavy' : 9 ≤ contacts G (rows p v hdv) a := by rw [hrows]; exact hheavy
  obtain ⟨d, hdA, hrow, hdiag⟩ :=
    exists_outside_labels hcard hn p hp hb v hvb hdv hpat ha hab hheavy' hthree.ge
  rcases one_terminal_both_highs hc hcard hn p hp hb v hvb hdv hpat ha hab hheavy'
    d hdA hrow hdiag with ⟨hx0, hx2⟩ | ⟨hy0, hy2⟩
  · exact leaf_highs_false hc hcard hdeg hn p hp hb v hvb hdv hpat ha hab hheavy'
      d hdA hrow hdiag hx0 hx2
  · obtain ⟨c', hc', _, hp', hb', _, _, hkeep⟩ := exists_alternate hc p hp hb v hvb hdv hpat
    let p' := swappedPaw p v hdv hpat
    let q' := swappedQuad p v hdv hpat
    have hdis : Disjoint p'.support q'.support := swapped_disjoint p v hdv hpat
    have hpat' : PawBlock.Pattern8 p' q' :=
      swapped_pattern p v hdv hpat (c.paw_nonadjacent hcard hn p hp)
    have hab' : a ≠ q'.support := by
      intro he
      have hmem : v 1 ∈ a := by
        rw [he]
        exact (q'.mem_support _).mpr ⟨1, rfl⟩
      exact disjoint_left.mp (c.property.blocks_disjoint hb ha hab.symm)
        (hvb ▸ (v.mem_support _).mpr ⟨1, rfl⟩) hmem
    have hheavy'' : 9 ≤ contacts G (rows p' q' hdis) a := by
      change 9 ≤ contacts G (rows (swappedPaw p v hdv hpat) (swappedQuad p v hdv hpat)
        (swapped_disjoint p v hdv hpat)) a
      rw [swapped_rows]
      exact hheavy'
    exact leaf_highs_false hc' hcard hdeg hn p' hp' hb' q' rfl hdis hpat'
      (hkeep a ha hab) hab' hheavy'' d hdA hrow hdiag hy0 hy2

end Erdos577
