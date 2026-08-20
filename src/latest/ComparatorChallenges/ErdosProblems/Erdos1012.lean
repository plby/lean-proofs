import Mathlib

open scoped Sym2
open Finset SimpleGraph

namespace Erdos1012

universe u

attribute [local instance] Classical.propDecidable Classical.decEq

/-- `G` contains a simple cycle with exactly `d` edges. -/
def HasCycleLength {V : Type u} (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = d

/-- The extremal edge count immediately below Woodall's threshold. -/
def woodallBound (n k : ℕ) : ℕ :=
  (n - k - 1).choose 2 + (k + 2).choose 2

/-- The exact assertion demanded at a fixed pair `(n,k)`. -/
def WoodallConclusion (n k : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n),
    woodallBound n k + 1 ≤ G.edgeFinset.card →
      ∀ d, 3 ≤ d → d ≤ n - k → HasCycleLength G d

/-- `N` is a valid eventual cutoff in Erdős Problem 1012. -/
def ValidCutoff (k N : ℕ) : Prop :=
  ∀ n, N ≤ n → WoodallConclusion n k

/-- Woodall's sharp theorem supplies every cycle length through `n - k`. -/
theorem erdos_1012 : ∀ k : ℕ, ValidCutoff k (2 * k + 3) := by
  sorry

end Erdos1012
