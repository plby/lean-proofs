/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped BigOperators
open SimpleGraph

noncomputable section


namespace Erdos88

universe u

open scoped Classical in
def RamseyFree {n : ℕ} (C : ℝ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ S : Finset (Fin n),
    (G.IsClique (S : Set (Fin n)) ∨ G.IsIndepSet (S : Set (Fin n))) →
      (S.card : ℝ) < C * Real.logb 2 n

open scoped Classical in
def neighborsIn {V : Type u}
    (G : SimpleGraph V) (v : V) (W : Finset V) : Finset V :=
  letI := Classical.decPred fun w ↦ G.Adj v w
  W.filter fun w ↦ G.Adj v w

end Erdos88

namespace Erdos637

open scoped Classical in
def degreeInto {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) (W : Finset V) : ℕ :=
  (Erdos88.neighborsIn G v W).card

end Erdos637

namespace Erdos637

open scoped Classical in
def numDistinctDegrees {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) : ℕ :=
  (W.image fun v ↦ degreeInto G v W).card

end Erdos637

namespace Erdos637

open scoped Classical in
theorem erdos637 :
    ∀ C : ℝ, 0 < C →
      ∃ α : ℝ, 0 < α ∧
      ∃ β : ℝ, 0 < β ∧
      ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
        Erdos88.RamseyFree C G →
          ∃ W : Finset (Fin n),
            α * (n : ℝ) ≤ W.card ∧
            β * Real.sqrt n ≤ numDistinctDegrees G W := by
  sorry

end Erdos637

end
