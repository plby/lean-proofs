import Mathlib

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace Erdos59

abbrev LabelledFreeGraphs {W : Type*} (H : SimpleGraph W) (n : ℕ) :=
  {G : SimpleGraph (Fin n) // H.Free G}

end Erdos59

namespace Erdos59

noncomputable def labelledFreeGraphCount {W : Type*} (H : SimpleGraph W) (n : ℕ) : ℕ :=
  Nat.card (LabelledFreeGraphs H n)

end Erdos59

namespace Erdos59

def HasErdos59UpperBound {W : Type*} (H : SimpleGraph W) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (labelledFreeGraphCount H n : ℝ) ≤
      Real.rpow 2 ((1 + ε) * (SimpleGraph.extremalNumber n H : ℝ))

end Erdos59

namespace Erdos59

def lowerBoundIndices {W : Type*} (H : SimpleGraph W) (c : ℝ) : Set ℕ :=
  {n | Real.rpow 2 ((1 + c) * (SimpleGraph.extremalNumber n H : ℝ)) ≤
    (labelledFreeGraphCount H n : ℝ)}

end Erdos59

namespace Erdos59

def HasMorrisSaxtonLowerBound {W : Type*} (H : SimpleGraph W) : Prop :=
  ∃ c : ℝ, 0 < c ∧ (lowerBoundIndices H c).Infinite

end Erdos59

namespace Erdos59

theorem erdos_59 :
    HasMorrisSaxtonLowerBound (SimpleGraph.cycleGraph 6) ∧
      ¬ HasErdos59UpperBound (SimpleGraph.cycleGraph 6) := by
  sorry

end Erdos59

end
