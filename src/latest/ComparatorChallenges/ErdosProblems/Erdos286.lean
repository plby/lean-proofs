/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Erdős Problem 286

The supplied statement asks for, asymptotically in the number k of terms,
k distinct positive integers in a real interval of width
(exp 1 - 1 + o(1)) * k whose unit fractions sum to one.

The local formalization of Martin's theorem supplies, for every sufficiently
large k, an exact k-term representation whose largest denominator is
(exp 1 / (exp 1 - 1) + o(1)) * k.  The elementary strict inequality

exp 1 / (exp 1 - 1) < exp 1 - 1

therefore lets us enlarge the containing interval to the width requested here.
-/

namespace Erdos286

open Filter Finset
open scoped BigOperators Topology

noncomputable section

/-- A literal ordered k-term representation of one by positive natural
denominators lying in the real interval [a, b]. -/
def IntervalRepresentation (k : ℕ) (a b : ℝ) : Prop :=
  ∃ n : Fin k → ℕ,
    StrictMono n ∧
    0 ∉ Set.range n ∧
    1 = ∑ i, (1 : ℝ) / n i ∧
    ∀ i, (n i : ℝ) ∈ Set.Icc a b

/-- Increasing enumeration of an arbitrary finite set with prescribed
cardinality. -/
def enumerate {k : ℕ} (A : Finset ℕ) (hA : A.card = k) : Fin k → ℕ :=
  A.orderEmbOfFin hA

theorem erdos_286 :
    ∃ o : ℕ → ℝ,
      o =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ᶠ k : ℕ in atTop,
        2 ≤ k ∧
          ∃ a b : ℝ,
            b - a = (Real.exp 1 - 1 + o k) * k ∧
            IntervalRepresentation k a b := by
  sorry

end

end Erdos286
