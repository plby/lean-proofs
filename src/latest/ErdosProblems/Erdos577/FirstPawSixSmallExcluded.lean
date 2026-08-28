import ErdosProblems.Erdos577.FirstPawSixSmallTriple
import ErdosProblems.Erdos577.FirstPawSixSmallFinalFactor

/-! The common-triple contradiction excludes cases (22) and (23) of Wang Lemma4.8. -/

namespace Erdos577.FirstPawSix.SmallCases

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem excluded {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (hdiag : PawBlock.OnlyFirst q) (variant : Bool)
    (hrows : PawBlock.ExactRows p q (caseRows (caseTag variant))) : False := by
  obtain ⟨a, ha, hab, hheavy⟩ := heavy_block hcard hdeg hn p hp hb q hq hd hdiag variant hrows
  obtain ⟨v, hv, htriple, hz⟩ :=
    common_triple hc hcard hdeg hn p hp hb q hq hd hdiag variant hrows ha hab hheavy
  have hvdis : Disjoint (p.support ∪ q.support) v.support := by
    rw [hp, hq, hv, disjoint_union_left]
    refine ⟨?_, c.property.blocks_disjoint hb ha hab.symm⟩
    apply disjoint_left.mpr
    intro u hu hua
    exact (mem_sdiff.mp (c.complementPartition.block_subset ha hua)).2 hu
  obtain ⟨parts⟩ := final_partition p q hd variant hrows v hvdis htriple hz
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

end Erdos577.FirstPawSix.SmallCases
