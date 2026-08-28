import ErdosProblems.Erdos577.ClaimTwoSixParity

/-! Wang's Claim2.6, with the additional finite maximum fully discharged. -/

namespace Erdos577

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem TriangleChain.Feasible.claim_two_six {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (hfull : degreeIn G p.leaf s = 4) :
    degreeIn G (p.vertices 2) s = 0 ∧ degreeIn G (p.vertices 3) s = 0 := by
  have hzero : degreeIn G (p.vertices 2) s + degreeIn G (p.vertices 3) s = 0 := by
    by_contra hne
    obtain ⟨p', a, y, hconfig, _, _⟩ := FullLeafCore.exists_configuration
      hc hcard hdeg hn p hp hs hfull (by omega)
    obtain ⟨e, q, t, b, z, hm⟩ := hconfig.exists_maximal
    exact hm.false hcard hdeg hn
  omega

end Erdos577
