/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open ContinuousMap Filter Set
open scoped BigOperators Topology

namespace Erdos671

abbrev Interval := Set.Icc (-1 : ℝ) 1

/-- Exactly `n` distinct interpolation nodes in the interval. -/
structure Row (n : ℕ) where
  ι : Type
  fintypeι : Fintype ι
  decidableEqι : DecidableEq ι
  card_ι : Fintype.card ι = n
  node : ι ↪ Interval

attribute [instance] Row.fintypeι Row.decidableEqι

/-- The fundamental Lagrange polynomial evaluated at a real point. -/
noncomputable def basisValue {n : ℕ} (X : Row n) (i : X.ι) (x : ℝ) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, (x - X.node j) / (X.node i - X.node j)

noncomputable def interpolation {n : ℕ} (X : Row n) (f : C(Interval, ℝ))
    (x : ℝ) : ℝ := ∑ i, f (X.node i) * basisValue X i x

noncomputable def lebesgueFunction {n : ℕ} (X : Row n) (x : ℝ) : ℝ :=
  ∑ i, |basisValue X i x|

/-- Both questions: Lebesgue functions are cofinally unbounded everywhere,
and each continuous function has a point of convergence of all interpolants. -/
theorem erdos_671 :
    ∃ X : ∀ n : ℕ, Row (n + 1),
      (∀ x : Interval, ∀ A : ℝ, ∀ N : ℕ,
        ∃ n ≥ N, A ≤ lebesgueFunction (X n) x) ∧
      ∀ f : C(Interval, ℝ), ∃ x : Interval,
        Tendsto (fun n ↦ interpolation (X n) f x) atTop (𝓝 (f x)) ∧
        ∀ A : ℝ, ∀ N : ℕ, ∃ n ≥ N, A ≤ lebesgueFunction (X n) x := by
  sorry

end Erdos671
