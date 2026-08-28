import ErdosProblems.Erdos577.WeightedFourteenDenseUpper
import ErdosProblems.Erdos577.OutsideSelectedCount

/-! The four terminal rows force a third block with at least nine contacts. -/

namespace Erdos577.WeightedFourteen.Dense

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma Model.labeling_terminalSet (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (v : Quadrilateral G)
    (hv : Disjoint (p.support ∪ q.support) v.support) :
    terminalSet.image (WeightedFifteen.twoBlockLabeling p q hd v hv) =
      univ.image (terminals p q v) := by
  rw [terminalSet_eq, image_image]
  congr 1
  funext tag
  fin_cases tag <;> rfl

variable [Fintype V] [DecidableRel G.Adj]

theorem heavy_block {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (v : Quadrilateral G) (hv : v.support = a)
    (special : Fin 3) (hrows : Rows p q v special) :
    ∃ t ∈ c.blocks, t ≠ b ∧ t ≠ a ∧ 9 ≤ contacts G (univ.image (terminals p q v)) t := by
  have hdis : Disjoint (p.support ∪ q.support) v.support := by
    rw [hp, hq, hv, disjoint_union_left]
    refine ⟨?_, c.property.blocks_disjoint hb ha hab.symm⟩
    apply disjoint_left.mpr
    intro w hw hwa
    exact (mem_sdiff.mp (c.complementPartition.block_subset ha hwa)).2 hw
  let e := WeightedFifteen.twoBlockLabeling p q hd v hdis
  have hbs : ({b, a} : Finset (Finset V)) ⊆ c.blocks := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact hb
    · exact mem_singleton.mp hx ▸ ha
  have h2 : ({b, a} : Finset (Finset V)).card = 2 := by simp [hab.symm]
  have he : c.remainder ∪ ({b, a} : Finset (Finset V)).biUnion id =
      (p.support ∪ q.support) ∪ v.support := by
    simp only [biUnion_insert, singleton_biUnion, id_eq, hp, hq, hv, union_assoc]
  have h4 : (Model.terminalSet.image e).card = 4 := by
    rw [card_image_of_injective _ e.injective, Model.terminalSet_card]
  have hinside : contacts G (Model.terminalSet.image e)
      (c.remainder ∪ ({b, a} : Finset (Finset V)).biUnion id) ≤ 18 := by
    rw [he]
    exact Model.terminal_inside_bound p q hd h v hdis special hrows
      (c.paw_nonadjacent hcard hn p hp)
      (center_absent p q hd h (by rw [hp, hq]; exact c.no_local_factor hcard hn hb))
  have hblocks := c.card_vertices
  have hsub := card_sdiff_of_subset hbs
  have hge := card_le_card hbs
  obtain ⟨t, ht, hnt, hh⟩ := c.exists_heavy_outside_selected {b, a} hbs
    (Model.terminalSet.image e) (2 * k) 8 hdeg (by rw [h4]; omega)
  rw [Model.labeling_terminalSet p q hd v hdis] at hh
  exact ⟨t, ht, fun ht ↦ hnt (mem_insert.mpr (Or.inl ht)),
    fun ht ↦ hnt (mem_insert.mpr (Or.inr (mem_singleton.mpr ht))), by omega⟩

end Erdos577.WeightedFourteen.Dense
