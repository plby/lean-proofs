import ErdosProblems.Erdos577.WeightedThirteenLeafTwo
import ErdosProblems.Erdos577.WeightedThirteenThirdSetup

/-! Complete exclusion of weighted pattern (13), Wang's Lemma 4.6. -/

namespace Erdos577

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace WeightedThirteen

theorem excluded_dense {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (v : Quadrilateral G) (hv : v.support = a)
    (hcl : G.IsNClique 4 v.support) (hrows : DenseRows p q v) : False := by
  have hdis : Disjoint (p.support ∪ q.support) v.support := by
    rw [hp, hq, hv, disjoint_union_left]
    refine ⟨?_, c.property.blocks_disjoint hb ha hab.symm⟩
    apply disjoint_left.mpr
    intro u hu hua
    exact (mem_sdiff.mp (c.complementPartition.block_subset ha hua)).2 hu
  obtain ⟨t, ht, htb, hta, hheavy, hleaf, hlows⟩ :=
    third_block_setup hc hcard hdeg hn p hp hb q hq hd h ha hab v hv hcl hrows
  obtain ⟨hsmall, hlarge, hrep, hx1, hx2, hseven, _⟩ :=
    final_rows hc hcard hdeg hn p hp hb q hq hd h ha hab v hv hdis hcl hrows
      ht htb hta hheavy hlows
  have htwo := final_leaf_at_least_two hcard hn p hp hb q hq hd h ha v hv hdis hcl hrows
    ht htb hta hlows hrep hx1 hx2 hseven
  exact final_leaf_two_false hcard hn p hp hb q hq hd h ha v hv hdis hcl hrows
    ht htb hta hheavy (by omega) hsmall hlarge hrep hx1 hx2 hseven

theorem excluded {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (h : WeightedPawBlock.Pattern13 p q) : False := by
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    apply disjoint_left.mpr
    intro u hu hub
    exact (mem_sdiff.mp (c.complementPartition.block_subset hb hub)).2 hu
  obtain ⟨swap, q', hq', h', a, ha, hab, v, hv, hcl, hrows⟩ :=
    exists_dense_block hc hcard hdeg hn p hp hb q hq hd h
  have hp' : (FirstPaw.normalizedPaw p swap).support = c.remainder := by
    rw [FirstPaw.normalizedPaw_support, hp]
  have hd' : Disjoint (FirstPaw.normalizedPaw p swap).support q'.support := by
    rw [FirstPaw.normalizedPaw_support, hq']
    exact hd
  exact excluded_dense hc hcard hdeg hn (FirstPaw.normalizedPaw p swap) hp' hb q'
    (hq'.trans hq) hd' h' ha hab v hv (hv.symm ▸ hcl) hrows

end WeightedThirteen

lemma TriangleChain.Feasible.not_weighted_pattern13 {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b) :
    ¬WeightedPawBlock.Pattern13 p q :=
  fun h ↦ WeightedThirteen.excluded hc hcard hdeg hn p hp hb q hq h

end Erdos577
