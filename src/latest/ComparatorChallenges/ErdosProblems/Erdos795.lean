/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos795

def interval (N : ℕ) : Finset ℕ := Finset.Icc 1 N

def subsetProduct (S : Finset ℕ) : ℕ := ∏ n ∈ S, n

def DistinctSubsetProducts (A : Finset ℕ) : Prop :=
  Set.InjOn subsetProduct (A.powerset : Set (Finset ℕ))

open scoped Classical in
noncomputable def g (N : ℕ) : ℕ :=
  ((interval N).powerset.filter DistinctSubsetProducts).sup Finset.card

theorem erdos_795 :
    ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (g N : ℝ) ≤ Nat.primeCounting N +
        Nat.primeCounting (Nat.sqrt N) +
          ε * (Real.sqrt N / Real.log N) := by
  sorry

end Erdos795
