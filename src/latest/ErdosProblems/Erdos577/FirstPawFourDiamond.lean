import ErdosProblems.Erdos577.FirstPawFourLeaf
import ErdosProblems.Erdos577.FirstPawFourTerminals
import ErdosProblems.Erdos577.SmallLeafWeightedBound

/-! The five-edge block case of pattern (4) contradicts the outside weighted count. -/

namespace Erdos577.FirstPawFour

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem diamond_false {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern4 p q)
    (hheavy : 9 ≤ contacts G p.support q.support) (hdiag : ¬G.Adj (q 1) (q 3))
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (hweight : 13 ≤ weight p q a) : False := by
  obtain ⟨hleaf, hsum⟩ := leaf_bound hc hcard hn p hp hb q hq hd h hheavy ha hab hweight
  have hlow (second : Bool) : degreeIn G (q (if second then 3 else 1)) a ≤ 2 := by
    let u := q (if second then 3 else 1)
    by_contra! hlarge
    have hfour := degreeIn_le_card G u a
    rw [(c.property.blocks_quad a ha).card] at hfour
    have hum : u ∈ vertexSet p q := by cases second <;> simp [u, vertexSet]
    have herase : contacts G ((vertexSet p q).erase u) a + degreeIn G u a =
        contacts G (vertexSet p q) a := sum_erase_add _ _ hum
    have hfive : 5 ≤ contacts G ((vertexSet p q).erase u) a := by omega
    have hno := no_universal_of_five hcard hn p hp hb q hq hd h hheavy ha hab u
      (by cases second <;> simp [u, terminalSet]) hfive
    obtain ⟨d, hdf, hdterm, hkeep⟩ :=
      exists_diamond_low_terminal hc p hp hb q hq hd h hheavy hdiag second
    apply hno
    intro z hz
    have hr : 3 ≤ degreeIn G d.terminal a := by rw [hdterm]; exact hlarge
    have he := hdf.terminal_universal_replace (hkeep a ha hab) hr hz
    rw [hdterm] at he
    exact he
  obtain ⟨w, hw⟩ := c.property.blocks_quad a ha
  have hbound := hc.small_leaf_weight_le_eight hcard hdeg hn p hp ha w hw
    (by rw [hw]; exact hleaf)
  rw [hw] at hbound
  have h1 : degreeIn G (q 1) a ≤ 2 := hlow false
  have h3 : degreeIn G (q 3) a ≤ 2 := hlow true
  unfold weight at hweight
  omega

end Erdos577.FirstPawFour
