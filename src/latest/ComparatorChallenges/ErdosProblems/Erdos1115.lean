/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Tactic

open Filter MeasureTheory

/-!
# Erdős Problem 1115

There are finite-order entire functions with no asymptotic curve over infinity
whose length in the disk of radius `r` is `O(r)`. An arbitrarily slowly
divergent factor multiplying the growth threshold `(log r)²` already
permits a counterexample.
-/

namespace Erdos1115

/-- The maximum modulus of `f` on the circle of radius `r`.  Only nonnegative radii are used. -/
noncomputable def maximumModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  ⨆ z : {z : ℂ // ‖z‖ = r}, ‖f z‖

/-- The elementary growth formulation of finite order used in this development. -/
def EntireOfFiniteOrder (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∃ ρ : ℝ, 0 ≤ ρ ∧
      ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (‖z‖ ^ ρ)

/-- A curve represented with speed at most one.  Every locally rectifiable curve going to infinity
has such an arclength parametrization; allowing speed below one only increases the time (and hence
the arclength upper parameter) spent in a disk. -/
def IsArcLengthPath (γ : ℝ → ℂ) : Prop :=
  LipschitzWith 1 γ

/-- Both the curve and its image under `f` tend to infinity. -/
def EscapesAlong (f : ℂ → ℂ) (γ : ℝ → ℂ) : Prop :=
  Tendsto (fun t ↦ ‖γ t‖) atTop atTop ∧
    Tendsto (fun t ↦ ‖f (γ t)‖) atTop atTop

/-- Length in the open disk, for a speed-at-most-one arclength parameter.  Properness of an
escaping curve makes the displayed measure finite; `toReal` then recovers ordinary length. -/
noncomputable def lengthInDisc (γ : ℝ → ℂ) (r : ℝ) : ℝ :=
  ENNReal.toReal (volume {t | 0 ≤ t ∧ ‖γ t‖ < r})

/-- The assertion `ℓ(r) = O(r)` in the question. -/
def HasLinearLength (γ : ℝ → ℂ) : Prop :=
  (fun r : ℝ ↦ lengthInDisc γ r) =O[atTop] (fun r ↦ r)

/-- The one-sided growth estimate `log M(r,f) = O(φ(r) (log r)²)`. -/
def HasGolbergEremenkoGrowth (φ : ℝ → ℝ) (f : ℂ → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ r : ℝ in atTop,
      Real.log (maximumModulus f r) ≤ C * φ r * (Real.log r) ^ 2

/-- An asymptotic curve over infinity in the arclength model used by the theorem. -/
def IsAsymptoticPath (f : ℂ → ℂ) (γ : ℝ → ℂ) : Prop :=
  IsArcLengthPath γ ∧ EscapesAlong f γ

/-- A geometric wall whose eventual avoidance costs at least `cost` units of arclength before
leaving the disk of radius `outer`.  This definition contains no analytic information about `f`;
the spiral lemma below supplies it for the explicit walls. -/
def IsLengthBarrier (S : Set ℂ) (inner outer cost : ℝ) : Prop :=
  ∀ γ : ℝ → ℂ, IsArcLengthPath γ →
    Tendsto (fun t ↦ ‖γ t‖) atTop atTop →
    ∀ t₀ : ℝ, 0 ≤ t₀ → ‖γ t₀‖ < inner →
    (∀ t ≥ t₀, γ t ∉ S) →
    cost ≤ lengthInDisc γ outer

/-- A certificate of bounded-value
walls at radii tending to infinity, whose unavoidable length divided by radius tends to infinity. -/
def HasEscapingBarriers (f : ℂ → ℂ) : Prop :=
  ∃ (S : ℕ → Set ℂ) (inner outer cost : ℕ → ℝ),
    (∀ n, 0 < outer n) ∧
    Tendsto inner atTop atTop ∧
    Tendsto outer atTop atTop ∧
    Tendsto (fun n ↦ cost n / outer n) atTop atTop ∧
    ∀ n, (∀ z ∈ S n, ‖f z‖ ≤ 1) ∧
      IsLengthBarrier (S n) (inner n) (outer n) (cost n)

theorem not_erdos_1115 :
    ∀ φ : ℝ → ℝ, Tendsto φ atTop atTop →
      ∃ f : ℂ → ℂ,
        (∃ z w : ℂ, f z ≠ f w) ∧
        ¬Bornology.IsBounded (Set.range f) ∧
        EntireOfFiniteOrder f ∧
        HasGolbergEremenkoGrowth φ f ∧
        HasEscapingBarriers f ∧
        ∀ γ : ℝ → ℂ, IsAsymptoticPath f γ → ¬HasLinearLength γ := by
  sorry

end Erdos1115
