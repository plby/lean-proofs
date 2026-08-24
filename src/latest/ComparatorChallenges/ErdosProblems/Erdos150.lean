/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos150

variable {V : Type*} [Fintype V] [DecidableEq V]

def IsSeparator (G : SimpleGraph V) (u v : V) (T : Finset V) : Prop :=
  u ∉ T ∧ v ∉ T ∧ ∀ w : G.Walk u v, ∃ x ∈ w.support, x ∈ T

def IsMinSeparator (G : SimpleGraph V) (u v : V) (T : Finset V) : Prop :=
  IsSeparator G u v T ∧ ∀ T' : Finset V, T' ⊂ T → ¬IsSeparator G u v T'
section BradacFull

def IsMinCut (G : SimpleGraph V) (T : Finset V) : Prop :=
  ∃ u v : V, u ≠ v ∧ IsMinSeparator G u v T

def minCutSet (G : SimpleGraph V) : Set (Finset V) :=
  {T | IsMinCut G T}

noncomputable def numMinCuts (G : SimpleGraph V) : ℕ :=
  (minCutSet G).ncard

noncomputable def c (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj), numMinCuts G = k}
end BradacFull

theorem erdos_150 :
    ∃ α, Filter.Tendsto (fun n ↦ (c n : ℝ) ^ (1 / n : ℝ)) .atTop (nhds α) ∧
      α < 2 := by
  sorry

end Erdos150
