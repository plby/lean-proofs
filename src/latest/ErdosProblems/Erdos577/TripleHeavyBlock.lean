import ErdosProblems.Erdos577.TripleLowSecondZero

/-! Every eleven-contact block in a triple-pattern configuration has only three positive rows. -/

namespace Erdos577.UniversalTriple

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {q : Quadrilateral G} {a : Finset V}

theorem Configuration.heavy_block (h : Configuration c p q) (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ z, 2 * k ≤ G.degree z)
    (hn : ¬HasPacking G k) (ha : a ∈ c.blocks) (haq : a ≠ q.support)
    (hheavy : 11 ≤ contacts G (insert (q 3) p.support) a) :
    G.IsNClique 4 a ∧ degreeIn G (p.vertices 2) a = 0 ∧ degreeIn G (p.vertices 3) a = 0 ∧
      11 ≤ degreeIn G p.leaf a + degreeIn G p.center a + degreeIn G (q 3) a := by
  obtain ⟨_, _, hcl⟩ := h.heavy_low_counts hc hcard hdeg hn ha haq hheavy
  have hz : degreeIn G (p.vertices 2) a = 0 ∧ degreeIn G (p.vertices 3) a = 0 := by
    by_cases hfull : degreeIn G p.leaf a = 4
    · exact hc.claim_two_six hcard hdeg hn p h.paw ha hfull
    · have hl := h.low_core_of_not_full hc hcard hdeg hn ha haq hheavy hfull
      exact ⟨hl.second_zero hc hcard hdeg hn, hl.third_zero hc hcard hdeg hn⟩
  refine ⟨hcl, hz.1, hz.2, ?_⟩
  rw [h.five_contacts, p.contacts_support, p.contacts_triangle, hz.1, hz.2] at hheavy
  change 11 ≤ degreeIn G (q 3) a + (degreeIn G p.leaf a +
    (degreeIn G p.center a + (0 + 0))) at hheavy
  omega

end Erdos577.UniversalTriple
