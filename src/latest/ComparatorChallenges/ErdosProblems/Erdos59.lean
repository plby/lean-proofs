/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos59

abbrev LabelledFreeGraphs {W : Type*} (H : SimpleGraph W) (n : ℕ) :=
  {G : SimpleGraph (Fin n) // H.Free G}

noncomputable def labelledFreeGraphCount {W : Type*} (H : SimpleGraph W) (n : ℕ) : ℕ :=
  Nat.card (LabelledFreeGraphs H n)

def HasErdos59UpperBound {W : Type*} (H : SimpleGraph W) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (labelledFreeGraphCount H n : ℝ) ≤
      Real.rpow 2 ((1 + ε) * (SimpleGraph.extremalNumber n H : ℝ))

def lowerBoundIndices {W : Type*} (H : SimpleGraph W) (c : ℝ) : Set ℕ :=
  {n | Real.rpow 2 ((1 + c) * (SimpleGraph.extremalNumber n H : ℝ)) ≤
    (labelledFreeGraphCount H n : ℝ)}

def HasMorrisSaxtonLowerBound {W : Type*} (H : SimpleGraph W) : Prop :=
  ∃ c : ℝ, 0 < c ∧ (lowerBoundIndices H c).Infinite

theorem not_erdos_59 :
    HasMorrisSaxtonLowerBound (SimpleGraph.cycleGraph 6) ∧
      ¬ HasErdos59UpperBound (SimpleGraph.cycleGraph 6) := by
  sorry

end Erdos59
