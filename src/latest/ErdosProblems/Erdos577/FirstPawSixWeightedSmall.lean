import ErdosProblems.Erdos577.FirstPawSixWeightedLeaf
import ErdosProblems.Erdos577.FirstPawSixTerminals
import ErdosProblems.Erdos577.SmallNoncentralClassification
import ErdosProblems.Erdos577.ThreeSetReplacement

/-! The small original three-row branch of case24 needs only ordinary replacement. -/

namespace Erdos577.FirstPawSix.WeightedCase

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem small_three_false {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (hdiag : PawBlock.OnlyFirst q)
    (hrows : PawBlock.ExactRows p q (caseRows 2))
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (hweight : 13 ≤ FirstPawFour.weight p q a)
    (hsmallThree : degreeIn G p.leaf a + degreeIn G (p.vertices 2) a +
      degreeIn G (p.vertices 3) a ≤ 6) : False := by
  have hleaf := leaf_bound hc hcard hn p hp hb q hq hd hdiag hrows ha hab hweight
  obtain ⟨d, hdf, _, hp', hkeep⟩ :=
    FirstPawSix.exists_alternate hc p hp hb q hq hd hdiag 2 hrows false
  let p' := alternatePaw p q hd hdiag 2 hrows false
  have ha' : a ∈ d.blocks := hkeep a ha hab
  obtain ⟨w, hw⟩ := c.property.blocks_quad a ha
  have hsmall : degreeIn G (p'.vertices 2) w.support ≤ 2 := by rw [hw]; exact hleaf
  have hthree : 7 ≤ degreeIn G p'.leaf w.support + degreeIn G (p'.vertices 2) w.support +
      degreeIn G (p'.vertices 3) w.support := by
    rw [hw]
    change 7 ≤ degreeIn G (q 3) a + degreeIn G p.leaf a + degreeIn G (q 1) a
    unfold FirstPawFour.weight at hweight
    omega
  have hpos : 0 < degreeIn G p'.leaf w.support := by
    have hfour := degreeIn_le_card G (p'.vertices 3) w.support
    rw [w.card_support] at hfour
    omega
  obtain ⟨hcommon, hbound⟩ := hdf.small_noncentral_common_three hcard hdeg hn
    p' hp' ha' w hw hsmall hpos hthree
  rw [hw] at hcommon hbound
  change 3 ≤ ((a.filter (G.Adj (q 3))) ∩ (a.filter (G.Adj (q 1)))).card at hcommon
  change 2 * degreeIn G p.leaf a + degreeIn G (q 3) a + degreeIn G (q 1) a ≤ 8 at hbound
  have hlarge : ∃ i : Fin 4, (i = 2 ∨ i = 3) ∧ 3 ≤ degreeIn G (p.vertices i) a := by
    unfold FirstPawFour.weight at hweight
    by_cases hh : 3 ≤ degreeIn G (p.vertices 2) a
    · exact ⟨2, Or.inl rfl, hh⟩
    · exact ⟨3, Or.inr rfl, by omega⟩
  obtain ⟨i, hi, hrow⟩ := hlarge
  have hout : p.vertices i ∉ a := by
    intro hu
    have hm : p.vertices i ∈ c.remainder := hp ▸ (mem_tupleSupport p.vertices _).mpr ⟨i, rfl⟩
    exact (mem_sdiff.mp (c.complementPartition.block_subset ha hu)).2 hm
  have hrep := (c.property.blocks_quad a ha).common_replacement_of_common_three
    (q 3) (q 1) (p.vertices i) hout hrow hcommon
  exact no_noncentral_insert hcard hn p hp hb q hq hd hdiag hrows ha hab i hi hrep

end Erdos577.FirstPawSix.WeightedCase
