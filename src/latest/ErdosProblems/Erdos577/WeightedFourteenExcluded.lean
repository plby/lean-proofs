import ErdosProblems.Erdos577.WeightedFourteenDenseHeavy
import ErdosProblems.Erdos577.WeightedFourteenDenseFactors

/-! The complete exclusion of weighted pattern (14), using the actual center-two occurrence. -/

namespace Erdos577

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace WeightedFourteen

theorem excluded_center_two {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q)
    (htwo : degreeIn G p.center q.support = 2) : False := by
  have hnon := center_absent p q hd h (by rw [hp, hq]; exact c.no_local_factor hcard hn hb)
  have hcenter : ∀ j : Fin 4, G.Adj p.center (q j) ↔ (5 : ℕ).testBit j.val = true := by
    apply q.row_saturated p.center 5
    · intro j hj
      fin_cases j
      · decide
      · exact False.elim (hnon.1 hj)
      · decide
      · exact False.elim (hnon.2 hj)
    · rw [htwo]
      decide +kernel
  obtain ⟨a, ha, hab, hheavy⟩ := heavy_block hcard hdeg hn p hp hb q hq hd h
  obtain ⟨v, special, hv, hrows⟩ := Dense.rows_at_heavy hc hcard hdeg hn p hp hb q hq
    hd h ha hab hheavy
  obtain ⟨t, ht, htb, hta, h9⟩ := Dense.heavy_block hcard hdeg hn p hp hb q hq
    hd h ha hab v hv special hrows
  have hdis : Disjoint (p.support ∪ q.support) v.support := by
    rw [hp, hq, hv, disjoint_union_left]
    refine ⟨?_, c.property.blocks_disjoint hb ha hab.symm⟩
    apply disjoint_left.mpr
    intro w hw hwa
    exact (mem_sdiff.mp (c.complementPartition.block_subset ha hwa)).2 hw
  let f := Dense.Model.copy p q hd h hcenter v hdis special hrows
  have himage : univ.image f = (c.remainder ∪ b) ∪ a := by
    change univ.image (WeightedFifteen.twoBlockLabeling p q hd v hdis) = _
    rw [WeightedFifteen.twoBlockLabeling_image, hp, hq, hv]
  have hdt : Disjoint (univ.image f) t := by
    rw [himage, disjoint_union_left, disjoint_union_left]
    refine ⟨⟨?_, c.property.blocks_disjoint hb ht htb.symm⟩,
      c.property.blocks_disjoint ha ht hta.symm⟩
    apply disjoint_left.mpr
    intro w hw hwt
    exact (mem_sdiff.mp (c.complementPartition.block_subset ht hwt)).2 hw
  have h9' : 9 ≤ contacts G (Dense.Model.terminalSet.image f) t := by
    change 9 ≤ contacts G (Dense.Model.terminalSet.image
      (WeightedFifteen.twoBlockLabeling p q hd v hdis)) t
    rw [Dense.Model.labeling_terminalSet]
    exact h9
  have hrep (tag : Fin 4) (h3 : 3 ≤ degreeIn G (f (Dense.Model.terminalIndex tag)) t)
      (u : V) (hu : u ∈ t) :
      QuadOn G (insert (f (Dense.Model.terminalIndex tag)) (t.erase u)) := by
    have he := Dense.Model.copy_terminal p q hd h hcenter v hdis special hrows tag
    change f (Dense.Model.terminalIndex tag) = Dense.terminals p q v tag at he
    rw [he] at h3 ⊢
    exact Dense.terminal_universal hc p hp hb q hq hd h ha v hv special hrows tag
      ht htb hta h3 u hu
  obtain ⟨part⟩ := Dense.Model.FinalTable.factor_of_nine special f t hdt
    (c.property.blocks_quad t ht).card h9' hrep
  have hbs : ({b, a, t} : Finset (Finset V)) ⊆ c.blocks := by
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact hb
    · rcases mem_insert.mp hz with rfl | hz
      · exact ha
      · exact mem_singleton.mp hz ▸ ht
  have he : c.remainder ∪ ({b, a, t} : Finset (Finset V)).biUnion id = univ.image f ∪ t := by
    rw [himage]
    simp only [biUnion_insert, singleton_biUnion, id_eq, union_assoc]
  exact hn (c.complementPartition.hasPacking_of_selected_factor hcard {b, a, t} hbs
    (he.symm ▸ part))

theorem excluded {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (h : WeightedPawBlock.Pattern14 p q) : False := by
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    apply disjoint_left.mpr
    intro w hw hwb
    exact (mem_sdiff.mp (c.complementPartition.block_subset hb hwb)).2 hw
  obtain ⟨d, p', v, hdS, hp', hv, hpattern, htwo⟩ :=
    exists_center_two_occurrence hc hcard hdeg hn p hp hb q hq hd h
  have hdis : Disjoint p'.support v.support := by
    rw [hp']
    apply disjoint_left.mpr
    intro w hw hwb
    exact (mem_sdiff.mp (d.complementPartition.block_subset hv hwb)).2 hw
  exact excluded_center_two hdS.toFeasible hcard hdeg hn p' hp' hv v rfl hdis hpattern htwo

end WeightedFourteen

lemma TriangleChain.Feasible.not_weighted_pattern14 {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b) :
    ¬WeightedPawBlock.Pattern14 p q :=
  fun h ↦ WeightedFourteen.excluded hc hcard hdeg hn p hp hb q hq h

end Erdos577
