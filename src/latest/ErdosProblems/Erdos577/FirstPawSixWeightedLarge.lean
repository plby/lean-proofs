import ErdosProblems.Erdos577.FirstPawSixWeightedLeaf
import ErdosProblems.Erdos577.FirstPawSixTerminals
import ErdosProblems.Erdos577.SmallLeafCommon
import ErdosProblems.Erdos577.PathMiddleReplacements

/-! The large original three-row branch of case24 gives a forbidden insertion of c. -/

namespace Erdos577.FirstPawSix.WeightedCase

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem large_three_false {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (hdiag : PawBlock.OnlyFirst q)
    (hrows : PawBlock.ExactRows p q (caseRows 2))
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (hweight : 13 ≤ FirstPawFour.weight p q a)
    (hlarge : 7 ≤ degreeIn G p.leaf a + degreeIn G (p.vertices 2) a +
      degreeIn G (p.vertices 3) a) : False := by
  obtain ⟨w, hw⟩ := c.property.blocks_quad a ha
  have hleaf := leaf_bound hc hcard hn p hp hb q hq hd hdiag hrows ha hab hweight
  have hsmall : degreeIn G p.leaf w.support ≤ 2 := by rw [hw]; exact hleaf
  have hcommon := hc.small_leaf_common_three hcard hdeg hn p hp ha w hw hsmall
    (by rw [hw]; exact hlarge)
  have hbound := hc.small_leaf_weight_le_eight hcard hdeg hn p hp ha w hw hsmall
  rw [hw] at hcommon hbound
  have hc3 : 3 ≤ degreeIn G (p.vertices 3) a :=
    hcommon.trans (card_le_card inter_subset_right)
  obtain ⟨d, hdf, hdt, _, hkeep⟩ :=
    FirstPawSix.exists_alternate hc p hp hb q hq hd hdiag 2 hrows true
  change d.terminal = p.vertices 3 at hdt
  have hrow : 3 ≤ degreeIn G d.terminal a := by rw [hdt]; exact hc3
  have huBound : ((a.filter (G.Adj (q 3))) ∪ (a.filter (G.Adj (q 1)))).card ≤ 4 := by
    calc
      _ ≤ a.card := card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
      _ = 4 := (c.property.blocks_quad a ha).card
  obtain ⟨u, hu, hq3, hq1⟩ := common_neighbor_of_union_bound (q 3) (q 1) a 4 huBound (by
    unfold FirstPawFour.weight at hweight
    omega)
  have hrep := hdf.terminal_universal_replace (hkeep a ha hab) hrow hu
  rw [hdt] at hrep
  exact no_noncentral_insert hcard hn p hp hb q hq hd hdiag hrows ha hab 3 (Or.inr rfl)
    ⟨u, hu, hq3, hq1, hrep⟩

end Erdos577.FirstPawSix.WeightedCase
