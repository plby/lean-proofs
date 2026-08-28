import ErdosProblems.Erdos577.WeightedThirteenUniversal
import ErdosProblems.Erdos577.WeightedThirteenExtraFactors
import ErdosProblems.Erdos577.NeighborRowBounds

/-! The final pattern (13) rows: the first low is universal, the other has at most two contacts. -/

namespace Erdos577.WeightedThirteen

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem final_rows {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (v : Quadrilateral G) (hv : v.support = a)
    (hdis : Disjoint (p.support ∪ q.support) v.support)
    (hcl : G.IsNClique 4 v.support) (hrows : DenseRows p q v)
    {t : Finset V} (ht : t ∈ c.blocks) (htb : t ≠ b) (hta : t ≠ a)
    (hheavy : 13 ≤ denseWeight p q v t)
    (hlows : 5 ≤ degreeIn G (q 1) t + degreeIn G (q 3) t) :
    degreeIn G (q 3) t ≤ 2 ∧ 3 ≤ degreeIn G (q 1) t ∧
      (∀ u ∈ t, QuadOn G (insert (q 1) (t.erase u))) ∧
      (∀ u ∈ t, ¬(G.Adj p.leaf u ∧ G.Adj (v 1) u)) ∧
      (∀ u ∈ t, ¬(G.Adj p.leaf u ∧ G.Adj (v 2) u)) ∧
      7 ≤ 2 * degreeIn G p.leaf t + degreeIn G (v 1) t + degreeIn G (v 2) t ∧
      2 * degreeIn G p.leaf t + degreeIn G (v 1) t + degreeIn G (v 2) t ≤ 8 := by
  have ht4 := (c.property.blocks_quad t ht).card
  have hno := no_dense_common hcard hn p hp hb q hq hd h ha v hv hdis hcl hrows ht htb hta
  have hq1 := degreeIn_le_card G (q 1) t
  have hq3 := degreeIn_le_card G (q 3) t
  rw [ht4] at hq1 hq3
  have hsmall : degreeIn G (q 3) t ≤ 2 := by
    by_contra! hlarge
    have hrep := third_low_universal hc hcard hdeg hn p hp hb q hq hd h ha hab v hv hdis
      hcl hrows ht htb hta hheavy true hlarge
    have hx1 := no_common_of_universal_insertion p.leaf (v 1) (q 3) t (hno 7) hrep
    have hx2 := no_common_of_universal_insertion p.leaf (v 2) (q 3) t (hno 8) hrep
    have h12 := no_common_of_universal_insertion (v 1) (v 2) (q 3) t (hno 9) hrep
    have hxq := no_common_of_universal_insertion p.leaf (q 1) (q 3) t (hno 6) hrep
    have htri := degree_triple_le_card p.leaf (v 1) (v 2) t hx1 hx2 h12
    have hpair := degree_pair_le_card p.leaf (q 1) t hxq
    rw [ht4] at htri hpair
    unfold denseWeight at hheavy
    omega
  have hlarge : 3 ≤ degreeIn G (q 1) t := by omega
  have hrep := third_low_universal hc hcard hdeg hn p hp hb q hq hd h ha hab v hv hdis
    hcl hrows ht htb hta hheavy false hlarge
  have hx1 := no_common_of_universal_insertion p.leaf (v 1) (q 1) t (hno 11) hrep
  have hx2 := no_common_of_universal_insertion p.leaf (v 2) (q 1) t (hno 12) hrep
  have hpair1 := degree_pair_le_card p.leaf (v 1) t hx1
  have hpair2 := degree_pair_le_card p.leaf (v 2) t hx2
  rw [ht4] at hpair1 hpair2
  refine ⟨hsmall, hlarge, hrep, hx1, hx2, ?_, ?_⟩
  · unfold denseWeight at hheavy
    omega
  · omega

theorem no_new_universal {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (v : Quadrilateral G) (hv : v.support = a)
    (hdis : Disjoint (p.support ∪ q.support) v.support)
    (hcl : G.IsNClique 4 v.support) (hrows : DenseRows p q v)
    {t : Finset V} (ht : t ∈ c.blocks) (htb : t ≠ b) (hta : t ≠ a)
    (hlows : 5 ≤ degreeIn G (q 1) t + degreeIn G (q 3) t) (second : Bool) :
    ¬∀ u ∈ t, QuadOn G (insert (v (if second then 2 else 1)) (t.erase u)) := by
  intro hrep
  have hbound : (t.filter (G.Adj (q 1)) ∪ t.filter (G.Adj (q 3))).card ≤ 4 := by
    calc
      _ ≤ t.card := card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
      _ = 4 := (c.property.blocks_quad t ht).card
  obtain ⟨u, hu, h1, h3⟩ := common_neighbor_of_union_bound (q 1) (q 3) t 4 hbound (by omega)
  have hno : ¬CommonReplacement G (q 1) (q 3) (v (if second then 2 else 1)) t := by
    cases second
    · exact no_extra_common hcard hn p hp hb q hq hd h ha v hv hdis hcl hrows ht htb hta 0
    · exact no_extra_common hcard hn p hp hb q hq hd h ha v hv hdis hcl hrows ht htb hta 1
  exact hno ⟨u, hu, h1, h3, hrep u hu⟩

end Erdos577.WeightedThirteen
