import ErdosProblems.Erdos577.JointFirstGainScore
import ErdosProblems.Erdos577.JointFirstSwap

/-! The strict crossing gain excludes its row pattern for either exposed leaf. -/

namespace Erdos577.JointFirst

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem both_leaves_crossing_gain_forbidden {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (has : a ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : JointClaims.CaseOne p q)
    (j : Quadrilateral G) (hj : j.support ∈ c.blocks) (hjs : j.support ≠ s)
    (haj : a ≠ j.support) (hje : edgeCount G j.support = 4)
    {z1 z2 : V} (h1 : z1 ∈ a) (h2 : z2 ∈ a)
    (hprimary : QuadOn G ((p.triangle ∪ a) \ {p.center, z1, z2}))
    (hpe : 5 ≤ edgeCount G ((p.triangle ∪ a) \ {p.center, z1, z2}))
    (hz : G.Adj z1 z2) (h11 : G.Adj z1 (j 1)) (h12 : G.Adj z1 (j 2))
    (h21 : G.Adj z2 (j 1)) (h22 : G.Adj z2 (j 2)) :
    ¬(G.Adj p.leaf (j 0) ∧ G.Adj p.leaf (j 3)) ∧
    ¬(G.Adj (q 1) (j 0) ∧ G.Adj (q 1) (j 3)) := by
  have h1p : z1 ∉ (p.triangle ∪ a) \ {p.center, z1, z2} :=
    fun hh ↦ (mem_sdiff.mp hh).2 (by simp)
  have h2p : z2 ∉ (p.triangle ∪ a) \ {p.center, z1, z2} :=
    fun hh ↦ (mem_sdiff.mp hh).2 (by simp)
  constructor
  · rintro ⟨hx0, hx3⟩
    exact strict_crossing_gain (hc.presentPaw_feasible p hp) ha j hj haj hje
      ((p.triangle ∪ a) \ {p.center, z1, z2}) hprimary sdiff_subset hpe
      h1 h2 h1p h2p hz h11 h12 h21 h22 hx0 hx3
  · rintro ⟨hv0, hv3⟩
    obtain ⟨d, hd, ht, hT, _, _, _, hkeep⟩ :=
      exists_center_terminal hc hcard hn p hp hs q hq hcase
    have hsub : (p.triangle ∪ a) \ {p.center, z1, z2} ⊆ d.triangle ∪ a := by
      rw [hT]
      exact sdiff_subset
    apply strict_crossing_gain hd.toFeasible (hkeep a ha has) j (hkeep j.support hj hjs)
      haj hje ((p.triangle ∪ a) \ {p.center, z1, z2}) hprimary hsub hpe
      h1 h2 h1p h2p hz h11 h12 h21 h22
    · rwa [ht]
    · rwa [ht]

end Erdos577.JointFirst
