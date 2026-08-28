import ErdosProblems.Erdos577.DensePairCompletion

/-! TeX9.69: the nonvacuous dense-core obstruction, with both inside estimates explicit. -/

namespace Erdos577.DenseObstruction

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem PairConfig.false_of_two_inside_bounds {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {p : Paw G} {d : Quadrilateral G} {s : Finset V} {z : V} (h : PairConfig c p d s z)
    (hcenter : G.Adj p.center (d 1))
    (hsecondary : G.IsNClique 4 {p.vertices 2, p.vertices 3, d 0, d 3})
    (hinside1 : contacts G (JointBridge.arms p z (d 2) (d 3))
      (p.support ∪ s ∪ d.support) ≤ 22)
    (hinside2 : contacts G (JointBridge.arms p z (d 2) (d 1))
      (p.support ∪ s ∪ d.support) ≤ 22) : False := by
  have hrev := h.reverse hcenter hsecondary
  obtain ⟨j, hj, hjs, hjd, hnine⟩ := h.exists_heavy_block hcard hdeg hinside1
  have hfirst := h.common_triple hc hcard hdeg hn hj hjs hjd hnine
  have hinsideRev : contacts G (JointBridge.arms p z (d.reverse 2) (d.reverse 3))
      (p.support ∪ s ∪ d.reverse.support) ≤ 22 := by
    rw [d.reverse_support]
    exact hinside2
  obtain ⟨b, hb, hbs, hbd, hbj, hnine2⟩ := hrev.exists_second_heavy_block hc hcard hdeg hn
    hinsideRev hj hjs (by rwa [d.reverse_support])
  have hsecond := hrev.common_triple hc hcard hdeg hn hb hbs hbd hnine2
  rw [d.reverse_support] at hbd
  exact h.two_classified_false hc hcard hn hj hjs hjd hb hbs hbd hbj hfirst hsecond

end Erdos577.DenseObstruction

namespace Erdos577

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- In the source labels, `d = (a₄,a₃,a₁,a₂)`. No leaf-degree or exposed attachment is assumed. -/
theorem TriangleChain.Feasible.dense_pair_obstruction {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (d : Quadrilateral G) (hd : d.support ∈ c.blocks)
    (hds : d.support ≠ s) (hcomplete : G.IsNClique 4 d.support)
    (hdense : 11 ≤ contacts G p.triangle d.support)
    (hcenter : ∀ i : Fin 4, i ≠ 0 → G.Adj p.center (d i))
    (hprimary : G.IsNClique 4 {p.vertices 2, p.vertices 3, d 0, d 1})
    (hsecondary : G.IsNClique 4 {p.vertices 2, p.vertices 3, d 0, d 3})
    (z : V) (hz : z ∈ s) (hquad : QuadOn G (insert p.leaf (s.erase z)))
    (hscore : edgeCount G (insert p.leaf (s.erase z)) = edgeCount G s)
    (hinside : ∀ i : Fin 4, i = 1 ∨ i = 3 →
      contacts G (JointBridge.arms p z (d 2) (d i)) (p.support ∪ s ∪ d.support) ≤ 22) :
    ¬QuadOn G (insert (p.vertices 2) (s.erase z)) := by
  intro hb
  have hdis : Disjoint p.support d.support := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hd)
  have hpair : WeightedTwelve.DensePair p d :=
    ⟨hdis, hcomplete, hdense, hcenter 2 (by decide), hcenter 3 (by decide), by
      rw [JointFinal.primary_support_eq p d hdis]
      exact hprimary⟩
  have h : DenseObstruction.PairConfig c p d s z :=
    ⟨hp, hs, hd, hds, hz, hpair, hquad, hscore, hb⟩
  exact h.false_of_two_inside_bounds hc hcard hdeg hn (hcenter 1 (by decide)) hsecondary
    (hinside 3 (Or.inr rfl)) (hinside 1 (Or.inl rfl))

end Erdos577
