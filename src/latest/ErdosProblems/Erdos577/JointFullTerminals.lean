import ErdosProblems.Erdos577.JointFullHeavy

/-! Both actual terminal chains supply the local factor, density, and universal insertion bounds. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Core.exists_full_terminal_chain {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support)
    (v : Quadrilateral G) (hv : v.support = j) (z w : V)
    (hpattern : FullPattern v p.leaf (q 3) z w) (u : V) (hu : u = q 3 ∨ u = v 3) :
    ∃ e : TriangleChain G, e.Feasible ∧ e.terminal = u ∧ e.triangle = p.triangle ∧
      e.edgeScore = c.edgeScore ∧ e.completeScore = c.completeScore ∧
      ∀ b ∈ c.blocks, b ≠ q.support → b ≠ j → b ∈ e.blocks := by
  rcases hu with hu | hu
  · subst u
    obtain ⟨hp, hq, _, _, hcase, _, _⟩ := h.config
    obtain ⟨e, he, ht, hT, _, hee, hec, _, hkeep⟩ :=
      JointClaims.exists_exposed_chain hc hcard hn p hp hq q rfl
        (h.paw_disjoint hq) (Or.inr hcase)
    exact ⟨e, he.toFeasible, ht, hT, hee, hec, fun b hb hbq _ ↦ hkeep b hb hbq⟩
  · subst u
    obtain ⟨e, he, ht, hT, hee, hec, _, hkeep⟩ :=
      h.exists_full_last_chain hc hcard hn hj hjq v hv z w hpattern
    exact ⟨e, he, ht, hT, hee, hec, hkeep⟩

theorem Core.full_terminal_properties {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j b : Finset V} (h : Core c p q d a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support)
    (v : Quadrilateral G) (hv : v.support = j) (z w : V)
    (hpattern : FullPattern v p.leaf (q 3) z w)
    (hb : b ∈ c.blocks) (hbq : b ≠ q.support) (hbj : b ≠ j)
    (u : V) (hu : u = q 3 ∨ u = v 3) :
    (¬LocalFactor G (insert u (p.triangle ∪ b))) ∧
      (9 ≤ contacts G p.triangle b → degreeIn G u b ≤ 1) ∧
      (3 ≤ degreeIn G u b → ∀ t ∈ b, QuadOn G (insert u (b.erase t))) ∧
      (3 ≤ degreeIn G u b → contacts G p.triangle b ≤ 4) := by
  obtain ⟨e, he, ht, hT, _, _, hkeep⟩ :=
    h.exists_full_terminal_chain hc hcard hn hj hjq v hv z w hpattern u hu
  have hb' := hkeep b hb hbq hbj
  have hrepl (hlarge : 3 ≤ degreeIn G u b) :
      ∀ t ∈ b, QuadOn G (insert u (b.erase t)) := by
    intro t htb
    simpa only [ht] using he.terminal_universal_replace hb' (by rwa [ht]) htb
  refine ⟨?_, ?_, hrepl, ?_⟩
  · intro hf
    apply e.no_local_factor hcard hn hb'
    change LocalFactor G (insert e.terminal e.triangle ∪ b)
    rwa [ht, hT, insert_union]
  · intro hdense
    have hh := he.terminal_degree_le_one_of_dense hcard hn hb' (by rwa [hT])
    rwa [ht] at hh
  · intro hlarge
    have hcol (t : V) (htb : t ∈ b) : degreeIn G t p.triangle ≤ 1 := by
      have hr : QuadOn G (insert e.terminal (b.erase t)) := by
        rw [ht]
        exact hrepl hlarge t htb
      have hh := (e.replaceBlock b hb' (e.swapTerminal hb' htb hr)).terminal_degree_le_one hcard hn
      change degreeIn G t e.triangle ≤ 1 at hh
      rwa [hT] at hh
    rw [contacts_comm]
    calc
      _ ≤ ∑ _ ∈ b, 1 := sum_le_sum fun t htb ↦ hcol t htb
      _ = 4 := by simp [(c.property.blocks_quad b hb).card]

end Erdos577.JointFinal
