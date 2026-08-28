import ErdosProblems.Erdos577.JointBridgeRowBounds
import ErdosProblems.Erdos577.JointFirstDirect
import ErdosProblems.Erdos577.JointFirstGainScore

/-! The generic core and score obstructions apply in both bridge terminal chains. -/

namespace Erdos577.JointBridge

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem both_high_pairs_forbidden {c d : TriangleChain G} (hc : c.Feasible) (hd : d.Strong)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    (u : V) (ht : d.terminal = u) (hT : d.triangle = p.triangle)
    {a : Finset V} (ha : a ∈ c.blocks) (had : a ∈ d.blocks)
    (j : Quadrilateral G) (hj : j.support ∈ c.blocks) (hjd : j.support ∈ d.blocks)
    (haj : a ≠ j.support) (hdiag : ¬G.Adj (j 1) (j 3))
    (hcore : ∀ v, v ∉ p.triangle ∪ a → 2 ≤ degreeIn G v (p.triangle ∪ a) →
      LocalFactor G (insert v (p.triangle ∪ a)))
    {z w : V} (hz : z ∈ a) (hw : w ∈ a) (hne : z ≠ w)
    (hrz : G.Adj p.center z) (hrep : QuadOn G (insert (p.vertices 3) (a.erase z)))
    (hz1 : G.Adj z (j 1)) (hz2 : G.Adj z (j 2)) (hw2 : G.Adj w (j 2)) :
    ¬(G.Adj p.leaf (j 0) ∧ G.Adj p.leaf (j 2)) ∧
      ¬(G.Adj u (j 0) ∧ G.Adj u (j 2)) := by
  have hx := JointFirst.terminal_high_pair_forbidden (hc.presentPaw_strong hcard hn p hp)
    hcard hdeg hn p rfl ha j hj haj hdiag hcore hz hw hne hrz hrep hz1 hz2 hw2
  have hu := JointFirst.terminal_high_pair_forbidden hd hcard hdeg hn p hT had j hjd haj
    hdiag hcore hz hw hne hrz hrep hz1 hz2 hw2
  rw [ht] at hu
  exact ⟨hx, hu⟩

theorem both_crossing_gains_forbidden {c d : TriangleChain G} (hc : c.Feasible) (hd : d.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    (u : V) (ht : d.terminal = u) (hT : d.triangle = p.triangle)
    {a : Finset V} (ha : a ∈ c.blocks) (had : a ∈ d.blocks)
    (j : Quadrilateral G) (hj : j.support ∈ c.blocks) (hjd : j.support ∈ d.blocks)
    (haj : a ≠ j.support) (hje : edgeCount G j.support = 4)
    {z1 z2 : V} (h1 : z1 ∈ a) (h2 : z2 ∈ a)
    (hprimary : QuadOn G ((p.triangle ∪ a) \ {p.center, z1, z2}))
    (hpe : 5 ≤ edgeCount G ((p.triangle ∪ a) \ {p.center, z1, z2}))
    (hz : G.Adj z1 z2) (h11 : G.Adj z1 (j 1)) (h12 : G.Adj z1 (j 2))
    (h21 : G.Adj z2 (j 1)) (h22 : G.Adj z2 (j 2)) :
    ¬(G.Adj p.leaf (j 0) ∧ G.Adj p.leaf (j 3)) ∧
      ¬(G.Adj u (j 0) ∧ G.Adj u (j 3)) := by
  have h1p : z1 ∉ (p.triangle ∪ a) \ {p.center, z1, z2} :=
    fun hh ↦ (mem_sdiff.mp hh).2 (by simp)
  have h2p : z2 ∉ (p.triangle ∪ a) \ {p.center, z1, z2} :=
    fun hh ↦ (mem_sdiff.mp hh).2 (by simp)
  constructor
  · rintro ⟨hx0, hx3⟩
    exact JointFirst.strict_crossing_gain (hc.presentPaw_feasible p hp) ha j hj haj hje
      ((p.triangle ∪ a) \ {p.center, z1, z2}) hprimary sdiff_subset hpe
      h1 h2 h1p h2p hz h11 h12 h21 h22 hx0 hx3
  · rintro ⟨hu0, hu3⟩
    have hsub : (p.triangle ∪ a) \ {p.center, z1, z2} ⊆ d.triangle ∪ a := by
      rw [hT]
      exact sdiff_subset
    apply JointFirst.strict_crossing_gain hd had j hjd haj hje
      ((p.triangle ∪ a) \ {p.center, z1, z2}) hprimary hsub hpe
      h1 h2 h1p h2p hz h11 h12 h21 h22
    · rwa [ht]
    · rwa [ht]

end Erdos577.JointBridge
