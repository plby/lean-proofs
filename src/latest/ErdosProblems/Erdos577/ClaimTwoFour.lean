import ErdosProblems.Erdos577.JointClaimFourExcluded

/-! TeX9.64: Wang's Claim2.4 for both original noncentral paw labels. -/

namespace Erdos577

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem TriangleChain.Feasible.claim_two_four {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks) :
    degreeIn G p.leaf s + degreeIn G (p.vertices 2) s ≤ 6 ∧
      degreeIn G p.leaf s + degreeIn G (p.vertices 3) s ≤ 6 := by
  by_contra hbad
  have hfail : 7 ≤ degreeIn G p.leaf s + degreeIn G (p.vertices 2) s ∨
      7 ≤ degreeIn G p.leaf s + degreeIn G (p.vertices 3) s := by omega
  obtain ⟨e, p', q, a, he, hmax, _, _, _⟩ :=
    JointClaims.maximal_case_two_of_failure hc hcard hdeg hn p hp hs hfail
  obtain ⟨d, hcore⟩ := JointFinal.exists_core he.toFeasible hcard hdeg hn p' q hmax
  exact hcore.impossible he.toFeasible hcard hdeg hn

end Erdos577
