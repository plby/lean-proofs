import ErdosProblems.Erdos577.WeightedThirteenDenseConsequences
import ErdosProblems.Erdos577.SmallLeafWeightedBound

/-! The third block has leaf degree at most two and low-row sum at least five. -/

namespace Erdos577.WeightedThirteen

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem dense_third_rows {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (v : Quadrilateral G) (hv : v.support = a)
    (hdis : Disjoint (p.support ∪ q.support) v.support)
    (hcl : G.IsNClique 4 v.support) (hrows : DenseRows p q v)
    {t : Finset V} (ht : t ∈ c.blocks) (htb : t ≠ b) (hta : t ≠ a)
    (hheavy : 13 ≤ denseWeight p q v t) :
    degreeIn G p.leaf t ≤ 2 ∧ 5 ≤ degreeIn G (q 1) t + degreeIn G (q 3) t := by
  have hsmall := dense_leaf_le_two hc hcard hn p hp hb q hq hd h ha v hv hdis hcl hrows
    ht htb hta hheavy
  let p' := alternatePaw p q hd h v hdis hcl hrows
  obtain ⟨d, hdS, hp', hkeep⟩ := exists_alternate_strong_chain hc hcard hn p hp q hd h
    ha v hv hdis hcl hrows
  obtain ⟨w, hw⟩ := c.property.blocks_quad t ht
  have hsmall' : degreeIn G p'.leaf w.support ≤ 2 := by
    rw [hw]
    exact hsmall
  have hbound := hdS.toFeasible.small_leaf_weight_le_eight hcard hdeg hn p' hp'
    (hkeep t ht hta) w hw hsmall'
  change 2 * degreeIn G p.leaf w.support + degreeIn G (v 1) w.support +
    degreeIn G (v 2) w.support ≤ 8 at hbound
  rw [hw] at hbound
  refine ⟨hsmall, ?_⟩
  unfold denseWeight at hheavy
  omega

theorem third_block_setup {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (v : Quadrilateral G) (hv : v.support = a)
    (hcl : G.IsNClique 4 v.support) (hrows : DenseRows p q v) :
    ∃ t ∈ c.blocks, t ≠ b ∧ t ≠ a ∧ 13 ≤ denseWeight p q v t ∧
      degreeIn G p.leaf t ≤ 2 ∧ 5 ≤ degreeIn G (q 1) t + degreeIn G (q 3) t := by
  obtain ⟨t, ht, htb, hta, hheavy⟩ := dense_heavy_block hcard hdeg hn p hp hb q hq
    hd h ha hab v hv hrows
  have hdis : Disjoint (p.support ∪ q.support) v.support := by
    rw [hp, hq, hv, disjoint_union_left]
    refine ⟨?_, c.property.blocks_disjoint hb ha hab.symm⟩
    apply disjoint_left.mpr
    intro u hu hua
    exact (mem_sdiff.mp (c.complementPartition.block_subset ha hua)).2 hu
  exact ⟨t, ht, htb, hta, hheavy,
    dense_third_rows hc hcard hdeg hn p hp hb q hq hd h ha v hv hdis hcl hrows
      ht htb hta hheavy⟩

end Erdos577.WeightedThirteen
