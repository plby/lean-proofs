import ErdosProblems.Erdos577.FirstPawEightGain

/-! Reflections and the actual chain involution force a terminal to meet both outside highs. -/

namespace Erdos577.FirstPawEight

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem low_leaf_gain_false {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern8 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (d : Quadrilateral G) (hdA : d.support = a) (hdiag : ¬G.Adj (d 1) (d 3))
    (hy : ∀ j : Fin 4, G.Adj (q 1) (d j) ↔ j ≠ 3)
    (hw : ∀ j : Fin 4, G.Adj (q 3) (d j) ↔ j ≠ 3)
    (hx3 : G.Adj p.leaf (d 3)) (hx : G.Adj p.leaf (d 0) ∨ G.Adj p.leaf (d 2)) : False := by
  rcases hx with hx0 | hx2
  · exact normalized_gain_false hc p hp hb q hq hd h ha hab d hdA hdiag
      ((hy 1).mpr (by decide)) ((hy 2).mpr (by decide))
      ((hw 1).mpr (by decide)) ((hw 2).mpr (by decide)) hx0 hx3
  · let v := (d.rotate 2).reverse
    have hv : v.support = a := (Quadrilateral.reverse_support _).trans
      ((d.rotate_support 2).trans hdA)
    exact normalized_gain_false hc p hp hb q hq hd h ha hab v hv hdiag
      ((hy 1).mpr (by decide)) ((hy 0).mpr (by decide))
      ((hw 1).mpr (by decide)) ((hw 0).mpr (by decide)) hx2 hx3

theorem one_terminal_both_highs {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern8 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (hheavy : 9 ≤ contacts G (rows p q hd) a)
    (d : Quadrilateral G) (hdA : d.support = a)
    (hrow : ∀ j : Fin 4, G.Adj (q 1) (d j) ↔ j ≠ 3) (hdiag : ¬G.Adj (d 1) (d 3)) :
    (G.Adj p.leaf (d 0) ∧ G.Adj p.leaf (d 2)) ∨
      (G.Adj (p.vertices 3) (d 0) ∧ G.Adj (p.vertices 3) (d 2)) := by
  by_contra! hh
  obtain ⟨hw, _, _, hx, hy, hlast⟩ := no_terminal_high_pair_shape hcard hn p hp hb q hq hd h
    ha hab hheavy d hdA hrow (fun he ↦ hh.1 he.1 he.2) (fun he ↦ hh.2 he.1 he.2)
  rcases hlast with ⟨hx3, _⟩ | ⟨_, hy3⟩
  · exact low_leaf_gain_false hc p hp hb q hq hd h ha hab d hdA hdiag hrow hw hx3 hx
  · obtain ⟨c', hc', _, hp', hb', _, _, hkeep⟩ := exists_alternate hc p hp hb q hq hd h
    let p' := swappedPaw p q hd h
    let q' := swappedQuad p q hd h
    have hdis : Disjoint p'.support q'.support := swapped_disjoint p q hd h
    have hpat : PawBlock.Pattern8 p' q' :=
      swapped_pattern p q hd h (c.paw_nonadjacent hcard hn p hp)
    have hab' : a ≠ q'.support := by
      intro he
      have hmem : q 1 ∈ a := by
        rw [he]
        exact (q'.mem_support _).mpr ⟨1, rfl⟩
      exact disjoint_left.mp (c.property.blocks_disjoint hb ha hab.symm)
        (hq ▸ (q.mem_support _).mpr ⟨1, rfl⟩) hmem
    exact low_leaf_gain_false hc' p' hp' hb' q' rfl hdis hpat (hkeep a ha hab) hab'
      d hdA hdiag hrow hw hy3 hy

end Erdos577.FirstPawEight
