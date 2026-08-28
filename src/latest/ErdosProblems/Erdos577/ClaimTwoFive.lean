import ErdosProblems.Erdos577.WeightedTwelveExcluded

/-! TeX9.66: Wang's Claim2.5 with the original noncentral vertices and exact neighbor sets. -/

namespace Erdos577

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem TriangleChain.Feasible.heavy_weighted_leaf_le_two {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks)
    (hheavy : 7 ≤ degreeIn G p.leaf s + degreeIn G (p.vertices 2) s +
      degreeIn G (p.vertices 3) s) : degreeIn G p.leaf s ≤ 2 := by
  by_contra hlarge
  obtain ⟨swap, v, hv, hpat⟩ := JointClaims.large_weighted_patterns hc hcard hdeg hn
    p hp hs (by omega) hheavy
  let p' := FirstPaw.normalizedPaw p swap
  have hp' : p'.support = c.remainder := by rw [FirstPaw.normalizedPaw_support, hp]
  have hbound := (hc.claim_two_four hcard hdeg hn p' hp' hs).1
  rw [← hv] at hbound
  rcases hpat with h10 | h11 | h12
  · exact WeightedTwelve.ten_eleven_false p' v hbound (Or.inl h10)
  · exact WeightedTwelve.ten_eleven_false p' v hbound (Or.inr h11)
  · exact hc.not_weighted_pattern12 hcard hdeg hn p' hp' hs v hv h12

theorem TriangleChain.Feasible.claim_two_five {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (hheavy : 7 ≤ degreeIn G p.leaf s + degreeIn G (p.vertices 2) s +
      degreeIn G (p.vertices 3) s) :
    degreeIn G p.leaf s = 0 ∨
      (degreeIn G p.leaf s = 1 ∧
        degreeIn G (p.vertices 2) s + degreeIn G (p.vertices 3) s = 6 ∧
        s.filter (G.Adj (p.vertices 2)) = s.filter (G.Adj (p.vertices 3))) := by
  by_cases hz : degreeIn G p.leaf s = 0
  · exact Or.inl hz
  · have hsmall := hc.heavy_weighted_leaf_le_two hcard hdeg hn p hp hs hheavy
    obtain ⟨q, hq⟩ := c.property.blocks_quad s hs
    obtain ⟨hx, t, _, ht, h2, h3⟩ := hc.small_leaf_precise hcard hdeg hn p hp hs q hq
      (by rwa [hq]) (by rw [hq]; omega) (by rwa [hq])
    rw [hq] at hx h2 h3
    have hb : degreeIn G (p.vertices 2) s = 3 := (congrArg Finset.card h2).trans ht
    have hc3 : degreeIn G (p.vertices 3) s = 3 := (congrArg Finset.card h3).trans ht
    exact Or.inr ⟨hx, by omega, h2.trans h3.symm⟩

end Erdos577
