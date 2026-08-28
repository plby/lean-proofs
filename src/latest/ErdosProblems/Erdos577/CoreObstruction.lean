import ErdosProblems.Erdos577.CoreBridgeInsideBound
import ErdosProblems.Erdos577.CoreDirectObstruction

/-! Wang 4.9: the complete seven-vertex core obstruction, with both routes and equality factors. -/

namespace Erdos577.CoreTransfer

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem core_obstruction {c : TriangleChain G} (hc : c.Strong)
    (q : Quadrilateral G) (hq : q.support ∈ c.blocks) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {b : Finset V} (hb : b ∈ c.blocks) (hbq : b ≠ q.support)
    (hcore : ∀ v, v ∉ c.triangle ∪ b → 2 ≤ degreeIn G v (c.triangle ∪ b) →
      LocalFactor G (insert v (c.triangle ∪ b)))
    (center : V) (hcenter : center ∈ c.triangle) (hcx : G.Adj center c.terminal)
    (z₁ z₂ : V) (hz₁ : z₁ ∈ c.triangle ∪ b) (hz₂ : z₂ ∈ c.triangle ∪ b)
    (hz12 : z₁ ≠ z₂) (hz1c : z₁ ≠ center) (hz2c : z₂ ≠ center)
    (hzrep : z₁ ∈ b → ∃ x ∈ c.triangle, ∃ y ∈ c.triangle,
      x ≠ y ∧ G.Adj z₁ x ∧ QuadOn G (insert y (b.erase z₁)))
    (hhigh : G.Adj c.terminal (q 0)) (hdiag : ¬G.Adj (q 1) (q 3))
    (hz10 : G.Adj z₁ (q 0)) (hz11 : G.Adj z₁ (q 1)) (hz12q : G.Adj z₁ (q 2))
    (hz20 : G.Adj z₂ (q 0)) (hz22 : G.Adj z₂ (q 2))
    (hbridge : ¬G.Adj c.terminal (q 2) → ∃ d ∈ c.blocks, d ≠ b ∧ d ≠ q.support ∧
      ∃ y ∈ d, contacts G {q 1, q 3} d ≤ 4 ∧
        QuadOn G (insert c.terminal (d.erase y)) ∧
        edgeCount G (insert c.terminal (d.erase y)) = edgeCount G d ∧
        G.Adj y (q 0) ∧ G.Adj y (q 2)) : False := by
  have hdis : Disjoint (c.triangle ∪ b) q.support := disjoint_union_left.mpr
    ⟨c.triangle_disjoint_block hq, c.property.blocks_disjoint hb hq hbq⟩
  have hq2out : q 2 ∉ c.triangle ∪ b := fun hh ↦
    disjoint_left.mp hdis hh ((q.mem_support _).mpr ⟨2, rfl⟩)
  have hq2two : 2 ≤ degreeIn G (q 2) (c.triangle ∪ b) :=
    one_lt_card.mpr ⟨z₁, mem_filter.mpr ⟨hz₁, hz12q.symm⟩,
      z₂, mem_filter.mpr ⟨hz₂, hz22.symm⟩, hz12⟩
  have hfactor := hcore (q 2) hq2out hq2two
  by_cases hh : G.Adj c.terminal (q 2)
  · exact direct_core_factor_false hc q hq hcard hdeg hn hdiag hhigh hh hb hbq hcore
      hfactor hz₁ hz11 hzrep
  · obtain ⟨d, hd, hdb, hdq, y, hy, hlowd, hrep, hscore, hy0, hy2⟩ := hbridge hh
    have hrow := bridge_row hc.toFeasible q hq hdiag hd hdq y hy hrep hscore hy0 hy2
    have r := bridge hc.toFeasible q hq hdiag hd hdq y hy hrep hscore hrow hhigh
    have hnb : b ∉ ({q.support, d} : Finset (Finset V)) := by
      simp only [mem_insert, mem_singleton, not_or]
      exact ⟨hbq, hdb.symm⟩
    have hycount : 2 ≤ degreeIn G y q.support := by
      rw [q.degree_eq_mask y 5 hrow]
      decide +kernel
    have hu := bridge_inside_upper hc q hq hcard hdeg hn hdiag hd hdq y hy hrep hycount r
      hb hnb hcore hfactor center hcenter hcx z₁ z₂ hz₁ hz₂ hz12 hz1c hz2c
      hz10 hz11 hz12q hz20 hz22 hlowd
    have hl := bridge_inside_bound hc q hq hcard hdeg hn hdiag hd hdq y hy hrep hscore
      hrow hhigh hb hbq hdb.symm hfactor hz₁ hz11 hzrep
    omega

end Erdos577.CoreTransfer
