/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-- A finite simple graph with `⌊n² / 4⌋ + t` edges, where `t < ⌊n / 2⌋`,
contains at least `t * ⌊n / 2⌋` unordered triangles. -/
theorem erdos_1010 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {t : ℕ}
    (ht : t < Fintype.card V / 2)
    (hE : G.edgeFinset.card = Fintype.card V ^ 2 / 4 + t) :
    t * (Fintype.card V / 2) ≤ (G.cliqueFinset 3).card := by
  sorry
