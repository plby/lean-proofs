import ErdosProblems.Erdos577.TwoCoreCompleteComplement
import ErdosProblems.Erdos577.TwoCoreFiveObstruction

/-! TeX9.46: a complete block with two full noncentral rows and at most two center contacts. -/

namespace Erdos577.TwoCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The complete-core variant has automatic complementary quadrilaterals and needs
neither distinguished core vertex to be adjacent to the paw center. -/
theorem complete_core_obstruction {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (hcomplete : G.IsNClique 4 b)
    (z₁ z₂ : V) (hz₁ : z₁ ∈ b) (hz₂ : z₂ ∈ b) (hne : z₁ ≠ z₂)
    (hfull2 : degreeIn G (p.vertices 2) b = 4) (hfull3 : degreeIn G (p.vertices 3) b = 4)
    (hcenter : degreeIn G p.center b ≤ 2)
    (hcore : ∀ u, u ∉ p.triangle ∪ b → 2 ≤ degreeIn G u (p.triangle ∪ b) →
      LocalFactor G (insert u (p.triangle ∪ b)))
    {s : Finset V} (hs : s ∈ c.blocks) (hbs : b ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hdiag : PawBlock.OnlyFirst q)
    (hrow : ∀ i : Fin 4, G.Adj p.leaf (q i) ↔ (9 : ℕ).testBit i.val = true)
    (hzQ : ∀ i : Fin 4, i ≠ 3 → G.Adj z₁ (q i))
    (hz₂Q : 1 ≤ degreeIn G z₂ {q 1, q 2}) : False := by
  have hpB : Disjoint p.support b := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hb)
  have hcl := complete_core_complement p hcomplete hpB z₁ z₂ hz₁ hz₂ hne hfull2 hfull3
  have hr : QuadOn G ((p.triangle ∪ b) \ {z₁, z₂, p.center}) :=
    QuadOn.of_clique hcl.card_eq hcl.isClique
  have hpair : contacts G {p.center, p.vertices 2} b =
      degreeIn G p.center b + degreeIn G (p.vertices 2) b :=
    sum_pair (p.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 2))
  by_cases hsmall : degreeIn G p.center b ≤ 1
  · have hrows : contacts G {p.center, p.vertices 2} b ≤ 5 := by
      rw [hpair, hfull2]
      omega
    exact five_contact_core_obstruction hc hcard hdeg hn p hp hb z₁ z₂ hz₁ hz₂ hne
      hfull3 hrows hcore hr hs hbs q hq hdiag hrow hzQ hz₂Q
  have htwo : degreeIn G p.center b = 2 := by omega
  obtain ⟨w, hw, hwne, hrw⟩ := exists_center_neighbor_ne p b htwo z₁
  have hwcl := complete_core_complement p hcomplete hpB z₁ w hz₁ hw hwne.symm hfull2 hfull3
  have hwquad : QuadOn G ((p.triangle ∪ b) \ {z₁, w, p.center}) :=
    QuadOn.of_clique hwcl.card_eq hwcl.isClique
  have h0 : G.Adj p.leaf (q 0) := (hrow 0).mpr (by decide)
  have h3 : G.Adj p.leaf (q 3) := (hrow 3).mpr (by decide)
  obtain ⟨_, hQrep, hQscore⟩ := third_replacement q z₁ hdiag hzQ
  have hw3 := second_core_last_absent hcard hn p hp hb hs hbs q hq z₁ w hz₁ hw hwne.symm
    hwquad hQrep hrw h3
  have hzdegree := degreeIn_clique G hcomplete.isClique hz₁
  rw [hcomplete.card_eq] at hzdegree
  obtain ⟨hBrep, hBidentity⟩ := full_replacement_score (c.property.blocks_quad b hb)
    (p.vertices 3) hfull3 z₁ hz₁
  have hBscore : edgeCount G (insert (p.vertices 3) (b.erase z₁)) = edgeCount G b := by omega
  have hBQ : Disjoint b q.support := by
    rw [hq]
    exact c.property.blocks_disjoint hb hs hbs
  have huniq := (first_core_unique hc hcard hn p hp hs q hq hdiag hrow hb hbs hcore
    z₁ hz₁ (hzQ 1 (by decide))).2
  have hz₂2 := (second_neighbor_of_unique q (p.triangle ∪ b) z₁ z₂
    (mem_union_right _ hz₂) hne huniq hz₂Q).2
  have hcross := crossing_quad q z₁ z₂ (fun hh ↦ disjoint_left.mp hBQ hz₁ hh)
    (fun hh ↦ disjoint_left.mp hBQ hz₂ hh) (hzQ 1 (by decide)) hz₂2
    (hcomplete.isClique hz₁ hz₂ hne)
  obtain ⟨hr0, hr3⟩ := center_extremes_absent hcard hn p hp hb hs hbs q hq
    z₁ z₂ hz₁ hz₂ hr hcross h0 h3
  have hb3 := noncentral_last_absent hcard hn p hp hb hs hbs q hq z₁ hz₁ hBrep hQrep h3
  have hcoupled := fun hh ↦ coupled_last_absent_of_degree_two hcard hn p hp hs q hq hh h3
  have hBzero := leaf_core_degree_zero hcard hn p hp hb hcore
  have hrows : contacts G {p.center, p.vertices 2} b ≤ 6 := by
    rw [hpair, hfull2]
    omega
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hinside := inside_upper hcard hn p hp hb hs hbs q hq hd hdiag hrow h3 hBzero hrows
    z₁ w hz₁ hw huniq hr0 hr3 hb3 hw3 hcoupled
  rw [exposedPath_support] at hinside
  exact obstruction_of_inside hc hcard hdeg hn p hp hb hs hbs q hq z₁ z₂ hz₁ hz₂
    hr hcross h0 h3 hBrep hBscore hQrep hQscore hinside

end Erdos577.TwoCore
