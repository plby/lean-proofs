import ErdosProblems.Erdos577.FirstPawEightHighPair
import ErdosProblems.Erdos577.CoreObstructionCounts
import ErdosProblems.Erdos577.FirstPawOutside

/-! The exposed outside lows have at most two neighbors in the old seven-vertex core. -/

namespace Erdos577.FirstPawEight

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
lemma outside_old_core {c : TriangleChain G}
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (d : Quadrilateral G) (hdA : d.support = a) (i : Fin 4) :
    d i ∉ p.support ∪ q.support := by
  have hi : d i ∈ a := hdA ▸ (d.mem_support _).mpr ⟨i, rfl⟩
  rw [hp, hq]
  intro hh
  rcases mem_union.mp hh with hh | hh
  · exact (mem_sdiff.mp (c.complementPartition.block_subset ha hi)).2 hh
  · exact disjoint_left.mp (c.property.blocks_disjoint hb ha hab.symm) hh hi

theorem leaf_row_of_highs {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {a : Finset V} (ha : a ∈ c.blocks) (d : Quadrilateral G) (hdA : d.support = a)
    (hdiag : ¬G.Adj (d 1) (d 3))
    (h0 : G.Adj p.leaf (d 0)) (h2 : G.Adj p.leaf (d 2)) :
    ∀ j : Fin 4, G.Adj p.leaf (d j) ↔ (5 : ℕ).testBit j.val = true :=
  (hc.presentPaw_feasible p hp).high_pair_row d (by change d.support ∈ c.blocks; rwa [hdA])
    hdiag h0 h2

theorem low_core_bound {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern8 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (d : Quadrilateral G) (hdA : d.support = a) (hdiag : ¬G.Adj (d 1) (d 3))
    (h0 : G.Adj p.leaf (d 0)) (h2 : G.Adj p.leaf (d 2))
    (i : Fin 4) (hi : i = 1 ∨ i = 3) : degreeIn G (d i) (p.triangle ∪ q.support) ≤ 2 := by
  let cp := c.presentPaw p hp
  have hD : d.support ∈ cp.blocks := by change d.support ∈ c.blocks; rwa [hdA]
  have r := CoreTransfer.direct_of_highs (hc.presentPaw_feasible p hp) d hD hdiag h0 h2
  have htri : degreeIn G (d i) p.triangle ≤ 1 := by
    obtain ⟨e, _, ht, hT, _⟩ := r.terminals i hi
    have hh := e.terminal_degree_le_one hcard hn
    rw [ht, hT] at hh
    exact hh
  have hblock : degreeIn G (d i) q.support ≤ 1 := by
    by_contra! hh
    have hf := h.outside_factor p q hd (d i)
      (outside_old_core p hp hb q hq ha hab d hdA i) (by omega)
    rw [hq] at hf
    exact r.no_local_factor hcard hn i hi hb (by simpa only [mem_singleton, hdA] using hab.symm) hf
  have hdis : Disjoint p.triangle q.support := hd.mono_left (by
    intro z hz
    rw [p.support_eq]
    exact mem_insert_of_mem hz)
  rw [degreeIn_union G _ hdis]
  omega

theorem inside_upper {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern8 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (d : Quadrilateral G) (hdA : d.support = a) (hdiag : ¬G.Adj (d 1) (d 3))
    (h0 : G.Adj p.leaf (d 0)) (h2 : G.Adj p.leaf (d 2)) :
    contacts G (p.support ∪ {d 1, d 3}) (p.support ∪ (q.support ∪ d.support)) ≤ 33 := by
  let cp := c.presentPaw p hp
  have hcp : cp.Strong := hc.presentPaw_strong hcard hn p hp
  have hpr : cp.remainder = p.support := p.support_eq.symm
  have hD : d.support ∈ cp.blocks := by change d.support ∈ c.blocks; rwa [hdA]
  have hbD : b ≠ d.support := by rw [hdA]; exact hab.symm
  have hrow := leaf_row_of_highs hc p hp ha d hdA hdiag h0 h2
  have hzero := CoreTransfer.terminal_low_degree_zero d p.leaf hrow
  have hlow1 := low_core_bound hc hcard hn p hp hb q hq hd h ha hab d hdA hdiag h0 h2
    1 (Or.inl rfl)
  have hlow3 := low_core_bound hc hcard hn p hp hb q hq hd h ha hab d hdA hdiag h0 h2
    3 (Or.inr rfl)
  have hself := hcp.remainder_self_contacts hcard hn
  have hold := (PawBlock.surviving_counts p q (Or.inr h)).2
  have htwo : 2 ≤ degreeIn G cp.terminal d.support := by
    change 2 ≤ degreeIn G p.leaf d.support
    rw [d.degree_eq_mask p.leaf 5 hrow]
    decide +kernel
  have hnew := hcp.block_contacts_le_eight_of_terminal_two hcard hdeg hn hD htwo
  have hlow := CoreTransfer.low_contacts_remainder_block cp d hb
  have hid := CoreTransfer.rows_inside_two_blocks cp d hD hb hbD hdiag
  change contacts G (cp.remainder ∪ {d 1, d 3}) (cp.remainder ∪ (b ∪ d.support)) = _ at hid
  rw [hpr, ← hq] at hid hlow
  change contacts G {d 1, d 3} (p.support ∪ q.support) = degreeIn G p.leaf {d 1, d 3} +
    degreeIn G (d 1) (p.triangle ∪ q.support) + degreeIn G (d 3) (p.triangle ∪ q.support) at hlow
  rw [hpr] at hself hnew
  omega

end Erdos577.FirstPawEight
