import ErdosProblems.Erdos577.TwoExposedDense

/-! Both corrected Wang4.14 routes preserve the triangle, both scores, and all unselected blocks. -/

namespace Erdos577.TwoExposed

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem one_route {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (z : V) (hz : z ∈ s) (hrep : QuadOn G (insert p.leaf (s.erase z)))
    (hscore : edgeCount G (insert p.leaf (s.erase z)) = edgeCount G s) :
    ∃ d : TriangleChain G, d.Feasible ∧ d.terminal = z ∧ d.triangle = p.triangle ∧
      d.edgeScore = c.edgeScore ∧ d.completeScore = c.completeScore ∧
      ∀ a ∈ c.blocks, a ≠ s → a ∈ d.blocks := by
  obtain ⟨d, hd, ht, hT, he, hcomp, hblocks⟩ :=
    (hc.presentPaw_feasible p hp).exists_terminal_swap hs hz hrep hscore
  refine ⟨d, hd, ht, hT, he, hcomp, ?_⟩
  intro a ha has
  rw [hblocks]
  exact mem_union_left _ (mem_erase.mpr ⟨has, ha⟩)

theorem two_route {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder) {s b : Finset V}
    (hs : s ∈ c.blocks) (hb : b ∈ c.blocks) (hbs : b ≠ s)
    (z y : V) (hz : z ∈ s) (hy : y ∈ b)
    (hfirst : QuadOn G (insert p.leaf (b.erase y)))
    (hfirstScore : edgeCount G (insert p.leaf (b.erase y)) = edgeCount G b)
    (hsecond : QuadOn G (insert y (s.erase z)))
    (hsecondScore : edgeCount G (insert y (s.erase z)) = edgeCount G s) :
    ∃ d : TriangleChain G, d.Feasible ∧ d.terminal = z ∧ d.triangle = p.triangle ∧
      d.edgeScore = c.edgeScore ∧ d.completeScore = c.completeScore ∧
      ∀ a ∈ c.blocks, a ≠ s → a ≠ b → a ∈ d.blocks := by
  obtain ⟨e, he, heY, heT, heScore, heComp, hkeep⟩ := one_route hc p hp hb y hy hfirst hfirstScore
  have hs' := hkeep s hs hbs.symm
  have hrep : QuadOn G (insert e.terminal (s.erase z)) := by rw [heY]; exact hsecond
  have hscore : edgeCount G (insert e.terminal (s.erase z)) = edgeCount G s := by
    rw [heY]
    exact hsecondScore
  obtain ⟨d, hd, hdZ, hdT, hdScore, hdComp, hblocks⟩ := he.exists_terminal_swap hs' hz hrep hscore
  refine ⟨d, hd, hdZ, hdT.trans heT, hdScore.trans heScore, hdComp.trans heComp, ?_⟩
  intro a ha has hab
  rw [hblocks]
  exact mem_union_left _ (mem_erase.mpr ⟨has, hkeep a ha hab⟩)

end Erdos577.TwoExposed
