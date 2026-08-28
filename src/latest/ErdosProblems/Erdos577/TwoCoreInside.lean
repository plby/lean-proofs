import ErdosProblems.Erdos577.TwoCoreInsideBudget

/-! The four exposed path rows have at most twenty-three contacts with the twelve-vertex core. -/

namespace Erdos577.TwoCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem inside_upper {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b s : Finset V} (hb : b ∈ c.blocks) (hs : s ∈ c.blocks) (hbs : b ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hd : Disjoint p.support q.support)
    (hdiag : PawBlock.OnlyFirst q)
    (hrow : ∀ i : Fin 4, G.Adj p.leaf (q i) ↔ (9 : ℕ).testBit i.val = true)
    (h3 : G.Adj p.leaf (q 3)) (hBzero : degreeIn G p.leaf b = 0)
    (hrows : contacts G {p.center, p.vertices 2} b ≤ 6)
    (z₁ z₂ : V) (hz₁ : z₁ ∈ b) (hz₂ : z₂ ∈ b)
    (hunique : ∀ u ∈ p.triangle ∪ b, G.Adj (q 1) u ↔ u = z₁)
    (hr0 : ¬G.Adj p.center (q 0)) (hr3 : ¬G.Adj p.center (q 3))
    (hb3 : ¬G.Adj (p.vertices 2) (q 3)) (hz3 : ¬G.Adj z₂ (q 3))
    (hcoupled : degreeIn G (p.vertices 2) {q 0, q 2} = 2 → ¬G.Adj (p.vertices 3) (q 3)) :
    contacts G (exposedPath p q hd h3).support (p.support ∪ (b ∪ q.support)) ≤ 23 := by
  have hpB : Disjoint p.support b := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hb)
  have hcouple := last_core_coupled p q (c.property.blocks_quad b hb).card hpB
    z₂ hz₂ hr3 hb3 hz3 hcoupled
  exact inside_upper_of_budgets hcard hn p hp hb hs hbs q hq hd hdiag hrow h3 hBzero
    (rowBudget := 6) (coreBudget := 5) (by decide) hrows z₁ hz₁ hunique hr0 hr3 hb3 hcouple

theorem inside_bound {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b s : Finset V} (hb : b ∈ c.blocks) (hs : s ∈ c.blocks) (hbs : b ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hdiag : PawBlock.OnlyFirst q)
    (hrow : ∀ i : Fin 4, G.Adj p.leaf (q i) ↔ (9 : ℕ).testBit i.val = true)
    (z₁ z₂ : V) (hz₁ : z₁ ∈ b) (hz₂ : z₂ ∈ b) (hne : z₁ ≠ z₂)
    (hrz₂ : G.Adj p.center z₂) (hfull : degreeIn G (p.vertices 3) b = 4)
    (hrows : contacts G {p.center, p.vertices 2} b ≤ 6)
    (hzQ : ∀ i : Fin 4, i ≠ 3 → G.Adj z₁ (q i))
    (hz₂Q : 1 ≤ degreeIn G z₂ {q 1, q 2})
    (hcore : ∀ u, u ∉ p.triangle ∪ b → 2 ≤ degreeIn G u (p.triangle ∪ b) →
      LocalFactor G (insert u (p.triangle ∪ b)))
    (hr : QuadOn G ((p.triangle ∪ b) \ {z₁, z₂, p.center})) :
    contacts G (insert (q 3) (FullRow.pathTriple p)) (p.support ∪ (b ∪ q.support)) ≤ 23 := by
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hBQ : Disjoint b q.support := by
    rw [hq]
    exact c.property.blocks_disjoint hb hs hbs
  have h0 : G.Adj p.leaf (q 0) := (hrow 0).mpr (by decide)
  have h3 : G.Adj p.leaf (q 3) := (hrow 3).mpr (by decide)
  have huniq := (first_core_unique hc hcard hn p hp hs q hq hdiag hrow hb hbs hcore
    z₁ hz₁ (hzQ 1 (by decide))).2
  have hz₂2 := (second_neighbor_of_unique q (p.triangle ∪ b) z₁ z₂
    (mem_union_right _ hz₂) hne huniq hz₂Q).2
  obtain ⟨hzdegree, hBrep, _⟩ := first_vertex_replacement hc hcard hdeg hn p hp hb hs hbs
    q hq h3 hdiag z₁ hz₁ hzQ hfull
  have hz12 := degree_three_adjacent (c.property.blocks_quad b hb) z₁ hz₁ hzdegree z₂ hz₂ hne
  have hcross := crossing_quad q z₁ z₂ (fun hh ↦ disjoint_left.mp hBQ hz₁ hh)
    (fun hh ↦ disjoint_left.mp hBQ hz₂ hh) (hzQ 1 (by decide)) hz₂2 hz12
  have hQrep := (third_replacement q z₁ hdiag hzQ).2.1
  obtain ⟨hr0, hr3⟩ := center_extremes_absent hcard hn p hp hb hs hbs q hq
    z₁ z₂ hz₁ hz₂ hr hcross h0 h3
  have hb3 := noncentral_last_absent hcard hn p hp hb hs hbs q hq z₁ hz₁ hBrep hQrep h3
  have hz3 := second_core_last_absent hcard hn p hp hb hs hbs q hq z₁ z₂ hz₁ hz₂ hne
    hr hQrep hrz₂ h3
  have hcoupled := fun hh ↦ coupled_last_absent_of_degree_two hcard hn p hp hs q hq hh h3
  have hBzero := leaf_core_degree_zero hcard hn p hp hb hcore
  have hbound := inside_upper hcard hn p hp hb hs hbs q hq hd hdiag hrow h3 hBzero hrows
    z₁ z₂ hz₁ hz₂ huniq hr0 hr3 hb3 hz3 hcoupled
  rwa [exposedPath_support] at hbound

end Erdos577.TwoCore
