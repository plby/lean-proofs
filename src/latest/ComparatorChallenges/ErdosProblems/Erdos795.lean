/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Finset Nat Real Asymptotics
open scoped BigOperators Topology

noncomputable section

namespace Erdos795

open scoped Classical in
def interval (N : ℕ) : Finset ℕ := Finset.Icc 1 N

end Erdos795

namespace Erdos795

open scoped Classical in
def subsetProduct (S : Finset ℕ) : ℕ := ∏ n ∈ S, n

end Erdos795

namespace Erdos795

open scoped Classical in
def DistinctSubsetProducts (A : Finset ℕ) : Prop :=
  Set.InjOn subsetProduct (A.powerset : Set (Finset ℕ))

end Erdos795

namespace Erdos795

open scoped Classical in
def g (N : ℕ) : ℕ :=
  ((interval N).powerset.filter DistinctSubsetProducts).sup Finset.card

end Erdos795

namespace Erdos795

open scoped Classical in
theorem erdos_795 :
    ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (g N : ℝ) ≤ Nat.primeCounting N +
        Nat.primeCounting (Nat.sqrt N) +
          ε * (Real.sqrt N / Real.log N) := by
  sorry

end Erdos795

end
