import ErdosProblems.Erdos577.TripleGivenBlock

/-! Wang's Claim2.7 for every specified block and actual paw presentation. -/

namespace Erdos577

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem TriangleChain.Feasible.claim_two_seven {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (hthree : degreeIn G p.leaf s = 3) :
    degreeIn G (p.vertices 2) s + degreeIn G (p.vertices 3) s ≤ 2 := by
  by_contra hlarge
  obtain ⟨hcl, _, hrows⟩ := hc.three_leaf_preparation hcard hdeg hn p hp hs hthree (by omega)
  rcases hrows with ⟨h2, h3⟩ | ⟨h3, h2⟩
  · obtain ⟨q, _, hconfig⟩ :=
      hc.triple_configuration_of_rows hcard hdeg hn p hp hs hcl hthree h2 h3
    exact hconfig.false hc hcard hdeg hn
  · have hp' : p.swapNoncentral.support = c.remainder := p.swapNoncentral_support.trans hp
    obtain ⟨q, _, hconfig⟩ := hc.triple_configuration_of_rows hcard hdeg hn p.swapNoncentral
      hp' hs hcl (by simpa only [Paw.swapNoncentral_leaf] using hthree)
      (by
        ext v
        constructor
        · intro hv
          have hv' : v ∈ s.filter (G.Adj (p.vertices 3)) := Finset.mem_filter.mpr
            ⟨(Finset.mem_filter.mp hv).1, by
              simpa only [Paw.swapNoncentral_apply, Equiv.swap_apply_left] using
                (Finset.mem_filter.mp hv).2⟩
          exact h3 ▸ hv'
        · intro hv
          have hv' : v ∈ s.filter (G.Adj (p.vertices 3)) := h3.symm ▸ hv
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv').1, by
            simpa only [Paw.swapNoncentral_apply, Equiv.swap_apply_left] using
              (Finset.mem_filter.mp hv').2⟩)
      (by simpa only [Paw.swapNoncentral_apply, Equiv.swap_apply_right] using h2)
    exact hconfig.false hc hcard hdeg hn

end Erdos577
