/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos758

/-! # Erdős Problem 758

The cochromatic number of a finite graph is the least number of vertex colours
for which every colour class is either a clique or an independent set.  The
quantity `z n` is the least number that works uniformly for every graph on
`Fin n`; for finite labelled graphs this is exactly the maximum of their
individual cochromatic numbers.
-/

/-- A colouring is cochromatic when each colour fibre is a clique or an independent set. -/
def IsCochromaticColoring {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (c : V → Fin k) : Prop :=
  ∀ i : Fin k,
    (∀ u v, c u = i → c v = i → u ≠ v → G.Adj u v) ∨
    (∀ u v, c u = i → c v = i → u ≠ v → ¬ G.Adj u v)

/-- `G` admits a cochromatic colouring using at most `k` colours. -/
def CochromaticColorable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, IsCochromaticColoring G c

instance instDecidableIsCochromaticColoring {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (c : V → Fin k) : Decidable (IsCochromaticColoring G c) := by
  unfold IsCochromaticColoring
  exact Fintype.decidableForallFintype

instance instDecidableCochromaticColorable {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    Decidable (CochromaticColorable G k) := by
  unfold CochromaticColorable
  exact Fintype.decidableExistsFintype

/-- A graph on `Fin n` is cochromatically colourable with `n` singleton colours. -/
theorem cochromaticColorable_fin (G : SimpleGraph (Fin n)) :
    CochromaticColorable G n := by
  refine ⟨id, ?_⟩
  intro i
  right
  intro u v hu hv huv
  exact (huv (hu.trans hv.symm)).elim

/-- `z n` is the least number uniformly sufficient for every graph on `n` vertices. -/
noncomputable def z (n : ℕ) : ℕ :=
  by
  classical
  exact Nat.find (show ∃ k, ∀ G : SimpleGraph (Fin n), CochromaticColorable G k from
    ⟨n, cochromaticColorable_fin⟩)

theorem erdos_758 : z 12 = 4 := by
  sorry

end Erdos758
