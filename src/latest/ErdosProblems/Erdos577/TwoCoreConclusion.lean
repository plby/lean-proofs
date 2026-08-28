import ErdosProblems.Erdos577.TwoCoreFinalFactors

/-! The shared final contradiction needs the proved inside bound and actual replacement blocks. -/

namespace Erdos577.TwoCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem obstruction_of_inside {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b s : Finset V} (hb : b ∈ c.blocks) (hs : s ∈ c.blocks) (hbs : b ≠ s)
    (q : Quadrilateral G) (hq : q.support = s)
    (z₁ z₂ : V) (hz₁ : z₁ ∈ b) (hz₂ : z₂ ∈ b)
    (hr : QuadOn G ((p.triangle ∪ b) \ {z₁, z₂, p.center}))
    (hcross : QuadOn G {z₁, q 1, q 2, z₂})
    (h0 : G.Adj p.leaf (q 0)) (h3 : G.Adj p.leaf (q 3))
    (hBrep : QuadOn G (insert (p.vertices 3) (b.erase z₁)))
    (hBscore : edgeCount G (insert (p.vertices 3) (b.erase z₁)) = edgeCount G b)
    (hQrep : QuadOn G (insert z₁ (q.support.erase (q 3))))
    (hQscore : edgeCount G (insert z₁ (q.support.erase (q 3))) = edgeCount G q.support + 1)
    (hinside : contacts G (insert (q 3) (FullRow.pathTriple p))
      (p.support ∪ (b ∪ q.support)) ≤ 23) : False := by
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  obtain ⟨j, hj, hjb, hjs, hheavy⟩ := heavy_outside hcard hdeg p hp hb hs hbs q hq hd h3 hinside
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
    exact first_common_false hcard hn p hp hb hs hbs hj hjb hjs q hq z₁ z₂ hz₁ hz₂
      hr hcross h0 hright

end Erdos577.TwoCore
