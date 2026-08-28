import ErdosProblems.Erdos577.WeightedFourteenJointRows

/-! The forced second block yields a strong pattern-(14) occurrence with center degree two. -/

namespace Erdos577.WeightedFourteen

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem exists_center_two_occurrence {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q) :
    ∃ d : TriangleChain G, ∃ p' : Paw G, ∃ v : Quadrilateral G,
      d.Strong ∧ p'.support = d.remainder ∧ v.support ∈ d.blocks ∧
      WeightedPawBlock.Pattern14 p' v ∧ degreeIn G p'.center v.support = 2 := by
  obtain ⟨a, ha, hab, hheavy⟩ := heavy_block hcard hdeg hn p hp hb q hq hd h
  obtain ⟨_, v, hv, hdiag, hcase, _, hw⟩ := joint_rows_at_heavy hc hcard hdeg hn p hp hb q hq
    hd h ha hab hheavy
  rcases hcase with hr | ⟨swap, hr⟩
  · let p' := alternatePaw p q hd h
    obtain ⟨d, hdS, _, _, hp', hkeep⟩ := exists_alternate_strong_chain hc hcard hn p hp hb q hq hd h
    have hpattern : WeightedPawBlock.Pattern14 p' v := by
      refine ⟨hdiag.2, ?_, ?_, ?_⟩
      · exact hw
      · exact hr 1
      · exact hr 3
    have hcenter : degreeIn G p'.center v.support = 2 := by
      change degreeIn G (p.vertices 2) v.support = 2
      rw [WeightedPawBlock.Row.degree p v 2 5 (hr 2)]
      decide +kernel
    exact ⟨d, p', v, hdS, hp', hv ▸ hkeep a ha hab, hpattern, hcenter⟩
  · let p' := FirstPaw.normalizedPaw p swap
    have hp' : p'.support = c.remainder := (FirstPaw.normalizedPaw_support p swap).trans hp
    let d := c.presentPaw p' hp'
    have hdS : d.Strong := hc.presentPaw_strong hcard hn p' hp'
    have hpattern : WeightedPawBlock.Pattern14 p' v := ⟨hdiag.2, hr 0, hr 2, hr 3⟩
    have hcenter : degreeIn G p'.center v.support = 2 := by
      change degreeIn G (p'.vertices 1) v.support = 2
      rw [WeightedPawBlock.Row.degree p' v 1 5 (hr 1)]
      decide +kernel
    have hblock : v.support ∈ d.blocks := by
      change v.support ∈ c.blocks
      rw [hv]
      exact ha
    exact ⟨d, p', v, hdS, p'.support_eq, hblock, hpattern, hcenter⟩

end Erdos577.WeightedFourteen
