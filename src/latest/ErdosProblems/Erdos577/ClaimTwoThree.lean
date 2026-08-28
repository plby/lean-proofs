import ErdosProblems.Erdos577.JointCaseOneExcluded

/-! TeX9.51: Wang's Claim2.3, for both original noncentral paw labels. -/

namespace Erdos577

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem JointClaims.full_leaf_second_bound {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (hfull : degreeIn G p.leaf s = 4) (hcenter : 0 < degreeIn G p.center s) :
    degreeIn G (p.vertices 2) s ≤ 1 := by
  by_contra hh
  obtain ⟨q, hq, hcase⟩ := case_one_labels_of_degrees hc hcard hn p hp hs hfull hcenter (by omega)
  exact case_one_false hc hcard hdeg hn p hp hs q hq hcase

theorem TriangleChain.Feasible.claim_two_three {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (hfull : degreeIn G p.leaf s = 4) (hcenter : 0 < degreeIn G p.center s) :
    degreeIn G (p.vertices 2) s ≤ 1 ∧ degreeIn G (p.vertices 3) s ≤ 1 := by
  have h2 := JointClaims.full_leaf_second_bound hc hcard hdeg hn p hp hs hfull hcenter
  have h3 := JointClaims.full_leaf_second_bound hc hcard hdeg hn p.swapNoncentral
    (by rw [Paw.swapNoncentral_support, hp]) hs
    (by simpa only [Paw.swapNoncentral_leaf] using hfull)
    (by simpa only [Paw.swapNoncentral_center] using hcenter)
  rw [Paw.swapNoncentral_apply, Equiv.swap_apply_left] at h3
  exact ⟨h2, h3⟩

end Erdos577
