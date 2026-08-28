import ErdosProblems.Erdos577.FirstPawFourLeaf
import ErdosProblems.Erdos577.SmallLeafCommon
import ErdosProblems.Erdos577.ThreeSetReplacement

/-! Pattern (4) is impossible when its original leaf and noncentral pair have seven contacts. -/

namespace Erdos577.FirstPawFour

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem large_three_false {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern4 p q)
    (hheavy : 9 ≤ contacts G p.support q.support)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (hweight : 13 ≤ weight p q a)
    (hlarge : 7 ≤ degreeIn G p.leaf a + degreeIn G (p.vertices 2) a +
      degreeIn G (p.vertices 3) a) : False := by
  obtain ⟨w, hw⟩ := c.property.blocks_quad a ha
  have hleaf := (leaf_bound hc hcard hn p hp hb q hq hd h hheavy ha hab hweight).1
  have hsmall : degreeIn G p.leaf w.support ≤ 2 := by rw [hw]; exact hleaf
  have hcommon := hc.small_leaf_common_three hcard hdeg hn p hp ha w hw hsmall
    (by rw [hw]; exact hlarge)
  have hbound := hc.small_leaf_weight_le_eight hcard hdeg hn p hp ha w hw hsmall
  rw [hw] at hcommon hbound
  have hlow : ∃ i : Fin 4, (i = 1 ∨ i = 3) ∧ 3 ≤ degreeIn G (q i) a := by
    unfold weight at hweight
    by_cases hh : 3 ≤ degreeIn G (q 1) a
    · exact ⟨1, Or.inl rfl, hh⟩
    · exact ⟨3, Or.inr rfl, by omega⟩
  obtain ⟨i, hi, hrow⟩ := hlow
  have hout : q i ∉ a := by
    intro hu
    exact disjoint_left.mp (c.property.blocks_disjoint hb ha hab.symm)
      (hq ▸ (q.mem_support _).mpr ⟨i, rfl⟩) hu
  have hrep := (c.property.blocks_quad a ha).common_replacement_of_common_three
    (p.vertices 2) (p.vertices 3) (q i) hout hrow hcommon
  have hterm : q i ∈ terminalSet p q := by
    rcases hi with rfl | rfl <;> simp [terminalSet]
  have hmem (j : Fin 4) (hj : j = 2 ∨ j = 3) : p.vertices j ∈ (vertexSet p q).erase (q i) := by
    apply mem_erase.mpr
    constructor
    · intro he
      exact disjoint_left.mp hd ((mem_tupleSupport p.vertices _).mpr ⟨j, rfl⟩)
        (he.symm ▸ (q.mem_support _).mpr ⟨i, rfl⟩)
    · rcases hj with rfl | rfl <;> simp [vertexSet]
  exact no_common_replacement hcard hn p hp hb q hq hd h hheavy ha hab
    (q i) (p.vertices 2) (p.vertices 3) hterm (hmem 2 (Or.inl rfl))
    (hmem 3 (Or.inr rfl)) (p.vertices.injective.ne (by decide)) hrep

end Erdos577.FirstPawFour
