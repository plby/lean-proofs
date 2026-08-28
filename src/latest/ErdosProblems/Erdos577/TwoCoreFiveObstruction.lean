import ErdosProblems.Erdos577.TwoCoreConclusion
import ErdosProblems.Erdos577.TwoCoreFiveInside

/-! TeX9.45: the five-contact variant needs neither center-to-core-vertex adjacency. -/

namespace Erdos577.TwoCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The smaller two-row budget permits both center-contact assumptions to be dropped.
The second distinguished core vertex may still meet the last vertex of the first block. -/
theorem five_contact_core_obstruction {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks)
    (z₁ z₂ : V) (hz₁ : z₁ ∈ b) (hz₂ : z₂ ∈ b) (hne : z₁ ≠ z₂)
    (hfull : degreeIn G (p.vertices 3) b = 4)
    (hrows : contacts G {p.center, p.vertices 2} b ≤ 5)
    (hcore : ∀ u, u ∉ p.triangle ∪ b → 2 ≤ degreeIn G u (p.triangle ∪ b) →
      LocalFactor G (insert u (p.triangle ∪ b)))
    (hr : QuadOn G ((p.triangle ∪ b) \ {z₁, z₂, p.center}))
    {s : Finset V} (hs : s ∈ c.blocks) (hbs : b ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hdiag : PawBlock.OnlyFirst q)
    (hrow : ∀ i : Fin 4, G.Adj p.leaf (q i) ↔ (9 : ℕ).testBit i.val = true)
    (hzQ : ∀ i : Fin 4, i ≠ 3 → G.Adj z₁ (q i))
    (hz₂Q : 1 ≤ degreeIn G z₂ {q 1, q 2}) : False := by
  have h0 : G.Adj p.leaf (q 0) := (hrow 0).mpr (by decide)
  have h3 : G.Adj p.leaf (q 3) := (hrow 3).mpr (by decide)
  have hinside := inside_five_bound hc hcard hdeg hn p hp hb hs hbs q hq hdiag hrow
    z₁ z₂ hz₁ hz₂ hne hfull hrows hzQ hz₂Q hcore hr
  obtain ⟨hzdegree, hBrep, hBscore⟩ := first_vertex_replacement hc hcard hdeg hn p hp hb hs hbs
    q hq h3 hdiag z₁ hz₁ hzQ hfull
  obtain ⟨_, hQrep, hQscore⟩ := third_replacement q z₁ hdiag hzQ
  have hBQ : Disjoint b q.support := by
    rw [hq]
    exact c.property.blocks_disjoint hb hs hbs
  have huniq := (first_core_unique hc hcard hn p hp hs q hq hdiag hrow hb hbs hcore
    z₁ hz₁ (hzQ 1 (by decide))).2
  have hz₂2 := (second_neighbor_of_unique q (p.triangle ∪ b) z₁ z₂
    (mem_union_right _ hz₂) hne huniq hz₂Q).2
  have hz12 := degree_three_adjacent (c.property.blocks_quad b hb) z₁ hz₁ hzdegree z₂ hz₂ hne
  have hcross := crossing_quad q z₁ z₂ (fun hh ↦ disjoint_left.mp hBQ hz₁ hh)
    (fun hh ↦ disjoint_left.mp hBQ hz₂ hh) (hzQ 1 (by decide)) hz₂2 hz12
  exact obstruction_of_inside hc hcard hdeg hn p hp hb hs hbs q hq z₁ z₂ hz₁ hz₂
    hr hcross h0 h3 hBrep hBscore hQrep hQscore hinside

end Erdos577.TwoCore
