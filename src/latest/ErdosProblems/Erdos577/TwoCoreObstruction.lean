import ErdosProblems.Erdos577.TwoCoreFinalFactors

/-! Wang4.11 / TeX9.44: the complete two-vertex core obstruction. -/

namespace Erdos577.TwoCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The source's two-vertex obstruction, with an actual complementary quadrilateral
and the exact seven-vertex core hypothesis. Both displayed center contacts are retained. -/
theorem two_vertex_core_obstruction {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks)
    (z₁ z₂ : V) (hz₁ : z₁ ∈ b) (hz₂ : z₂ ∈ b) (hne : z₁ ≠ z₂)
    (_hrz₁ : G.Adj p.center z₁) (hrz₂ : G.Adj p.center z₂)
    (hfull : degreeIn G (p.vertices 3) b = 4)
    (hrows : contacts G {p.center, p.vertices 2} b ≤ 6)
    (hcore : ∀ u, u ∉ p.triangle ∪ b → 2 ≤ degreeIn G u (p.triangle ∪ b) →
      LocalFactor G (insert u (p.triangle ∪ b)))
    (hr : QuadOn G ((p.triangle ∪ b) \ {z₁, z₂, p.center}))
    {s : Finset V} (hs : s ∈ c.blocks) (hbs : b ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hdiag : PawBlock.OnlyFirst q)
    (hrow : ∀ i : Fin 4, G.Adj p.leaf (q i) ↔ (9 : ℕ).testBit i.val = true)
    (hzQ : ∀ i : Fin 4, i ≠ 3 → G.Adj z₁ (q i))
    (hz₂Q : 1 ≤ degreeIn G z₂ {q 1, q 2}) : False := by
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have h0 : G.Adj p.leaf (q 0) := (hrow 0).mpr (by decide)
  have h3 : G.Adj p.leaf (q 3) := (hrow 3).mpr (by decide)
  have hinside := inside_bound hc hcard hdeg hn p hp hb hs hbs q hq hdiag hrow
    z₁ z₂ hz₁ hz₂ hne hrz₂ hfull hrows hzQ hz₂Q hcore hr
  obtain ⟨j, hj, hjb, hjs, hheavy⟩ := heavy_outside hcard hdeg p hp hb hs hbs q hq hd h3 hinside
  obtain ⟨hzdegree, hBrep, hBscore⟩ := first_vertex_replacement hc hcard hdeg hn p hp hb hs hbs
    q hq h3 hdiag z₁ hz₁ hzQ hfull
  obtain ⟨_, hQrep, hQscore⟩ := third_replacement q z₁ hdiag hzQ
  obtain ⟨parts, hscore, hretain⟩ := exists_path_partition p hp hb hs hbs q hq hd h3 z₁ hz₁
    hBrep hBscore hQrep hQscore
  obtain ⟨v, hv⟩ := c.property.blocks_quad j hj
  have hheavy' : 9 ≤ contacts G (exposedPath p q hd h3).support v.support := by
    rw [hv]
    exact hheavy
  have hclass := (hc.global_path_transfer hcard hdeg hn (exposedPath p q hd h3) parts hscore
    (hretain j hj hjb hjs)).2.2.2 v hv hheavy'
  rcases hclass.2.1.common_alternatives (exposedPath p q hd h3) v with hleft | hright
  · change CommonReplacement G p.center (p.vertices 2) p.leaf v.support at hleft
    rw [hv] at hleft
    exact triangle_common_false hcard hn p hp hj hleft
  · change CommonReplacement G p.leaf (q 3) p.center v.support at hright
    rw [hv] at hright
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
    exact first_common_false hcard hn p hp hb hs hbs hj hjb hjs q hq z₁ z₂ hz₁ hz₂
      hr hcross h0 hright

end Erdos577.TwoCore
