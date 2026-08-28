import ErdosProblems.Erdos577.FirstPawSevenTriple
import ErdosProblems.Erdos577.FirstPawSevenFinalFactor
import ErdosProblems.Erdos577.FirstPawFiveExcluded

/-! The full exclusion of pattern (7), completing the remaining case of Wang Lemma4.7. -/

namespace Erdos577

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem TriangleChain.Feasible.not_first_paw_pattern7 {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b) :
    ¬PawBlock.Pattern7 p q := by
  intro h
  have hd : Disjoint p.support q.support := by
    apply disjoint_left.mpr
    intro u hu hqu
    exact (mem_sdiff.mp (c.complementPartition.block_subset hb (hq ▸ hqu))).2 (hp ▸ hu)
  obtain ⟨a, ha, hab, hheavy⟩ := FirstPawSeven.heavy_block hcard hdeg hn p hp hb q hq hd h
  obtain ⟨v, hv, hrows, hx⟩ :=
    FirstPawSeven.common_triple hc hcard hdeg hn p hp hb q hq hd h ha hab hheavy
  have hvdis : Disjoint (p.support ∪ q.support) v.support := by
    rw [hp, hq, hv, disjoint_union_left]
    refine ⟨?_, c.property.blocks_disjoint hb ha hab.symm⟩
    apply disjoint_left.mpr
    intro u hu hua
    exact (mem_sdiff.mp (c.complementPartition.block_subset ha hua)).2 hu
  obtain ⟨parts⟩ := FirstPawSeven.final_partition p q hd h v hvdis hrows hx
  have hbs : ({b, a} : Finset (Finset V)) ⊆ c.blocks := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact hb
    · exact mem_singleton.mp hx ▸ ha
  have he : (p.support ∪ q.support) ∪ v.support =
      c.remainder ∪ ({b, a} : Finset (Finset V)).biUnion id := by
    rw [hp, hq, hv]
    simp only [biUnion_insert, singleton_biUnion, id_eq, union_assoc]
  exact hn (c.complementPartition.hasPacking_of_selected_factor hcard {b, a} hbs (he ▸ parts))

theorem TriangleChain.Feasible.not_first_paw_pattern5_or7 {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hheavy : 9 ≤ contacts G p.support q.support) :
    ¬(PawBlock.Pattern5 p q ∨ PawBlock.Pattern7 p q) := by
  rintro (h5 | h7)
  · exact hc.not_first_paw_pattern5 hcard hdeg hn p hp hb q hq hheavy h5
  · exact hc.not_first_paw_pattern7 hcard hdeg hn p hp hb q hq h7

end Erdos577
