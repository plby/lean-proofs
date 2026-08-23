import Mathlib

open Filter MeasureTheory

noncomputable section


namespace Erdos526

open scoped Classical in
def IsDecreasingRearrangement (a b : ℕ → ℝ) : Prop :=
  Antitone b ∧
    ∃ e : ℕ ≃ {n : ℕ // 0 < a n}, ∀ k : ℕ, b k = a (e k : ℕ)

end Erdos526

namespace Erdos526

open scoped Classical in
abbrev Circle := UnitAddCircle

end Erdos526

namespace Erdos526

open scoped Classical in
abbrev Sample := ℕ → Circle

end Erdos526

namespace Erdos526

open scoped Classical in
def uniformCircle : Measure Circle := AddCircle.haarAddCircle

end Erdos526

namespace Erdos526

open scoped Classical in
def sampleMeasure : Measure Sample :=
  Measure.infinitePi (fun _ : ℕ ↦ uniformCircle)

end Erdos526

namespace Erdos526

open scoped Classical in
def arc (z : Circle) (length : ℝ) : Set Circle :=
  Metric.ball z (length / 2)

end Erdos526

namespace Erdos526

open scoped Classical in
def CoversFrom (a : ℕ → ℝ) (ω : Sample) (N : ℕ) : Prop :=
  ∀ x : Circle, ∃ n : ℕ, N ≤ n ∧ x ∈ arc (ω n) (a n)

end Erdos526

namespace Erdos526

open scoped Classical in
def CoversInfinitelyOften (a : ℕ → ℝ) (ω : Sample) : Prop :=
  ∀ N : ℕ, CoversFrom a ω N

end Erdos526

namespace Erdos526

open scoped Classical in
def fullCoverageEvent (a : ℕ → ℝ) : Set Sample :=
  {ω | CoversInfinitelyOften a ω}

end Erdos526

namespace Erdos526

open scoped Classical in
def prefixLength (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, a k

end Erdos526

namespace Erdos526

open scoped Classical in
def sheppTerm (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.exp (prefixLength a (n + 1)) / ((n + 1 : ℕ) : ℝ) ^ 2

end Erdos526

namespace Erdos526

open scoped Classical in
def SheppCondition (a : ℕ → ℝ) : Prop :=
  ¬ Summable (sheppTerm a)

end Erdos526

namespace Erdos526

open scoped Classical in
theorem erdos_526_resolution
    {a : ℕ → ℝ}
    (ha₀ : ∀ n, 0 ≤ a n)
    (halim : Tendsto a atTop (nhds 0))
    (hdiv : ¬ Summable a) :
    ∃ b : ℕ → ℝ, IsDecreasingRearrangement a b ∧
      (sampleMeasure (fullCoverageEvent a) = 1 ↔ SheppCondition b) := by
  sorry

end Erdos526

end
