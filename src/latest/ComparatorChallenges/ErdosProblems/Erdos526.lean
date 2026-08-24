/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter MeasureTheory

namespace Erdos526

def IsDecreasingRearrangement (a b : ℕ → ℝ) : Prop :=
  Antitone b ∧
    ∃ e : ℕ ≃ {n : ℕ // 0 < a n}, ∀ k : ℕ, b k = a (e k : ℕ)

abbrev Circle := UnitAddCircle

abbrev Sample := ℕ → Circle

noncomputable def uniformCircle : Measure Circle := AddCircle.haarAddCircle

noncomputable def sampleMeasure : Measure Sample :=
  Measure.infinitePi (fun _ : ℕ ↦ uniformCircle)

def arc (z : Circle) (length : ℝ) : Set Circle :=
  Metric.ball z (length / 2)

def CoversFrom (a : ℕ → ℝ) (ω : Sample) (N : ℕ) : Prop :=
  ∀ x : Circle, ∃ n : ℕ, N ≤ n ∧ x ∈ arc (ω n) (a n)

def CoversInfinitelyOften (a : ℕ → ℝ) (ω : Sample) : Prop :=
  ∀ N : ℕ, CoversFrom a ω N

def fullCoverageEvent (a : ℕ → ℝ) : Set Sample :=
  {ω | CoversInfinitelyOften a ω}

def prefixLength (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, a k

noncomputable def sheppTerm (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.exp (prefixLength a (n + 1)) / ((n + 1 : ℕ) : ℝ) ^ 2

def SheppCondition (a : ℕ → ℝ) : Prop :=
  ¬ Summable (sheppTerm a)

theorem erdos_526
    {a : ℕ → ℝ}
    (ha₀ : ∀ n, 0 ≤ a n)
    (halim : Tendsto a atTop (nhds 0))
    (hdiv : ¬ Summable a) :
    ∃ b : ℕ → ℝ, IsDecreasingRearrangement a b ∧
      (sampleMeasure (fullCoverageEvent a) = 1 ↔ SheppCondition b) := by
  sorry

end Erdos526
