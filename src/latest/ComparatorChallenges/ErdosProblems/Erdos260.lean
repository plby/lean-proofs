import Mathlib

open Filter

namespace Erdos260

/-- The integer-sequence formulation permits any finite initial segment. -/
theorem erdos_260 :
    ∀ a : ℕ → ℤ, ∀ s : ℝ,
      StrictMono a →
      Tendsto (fun n => (a n : ℝ) / n) atTop atTop →
      HasSum (fun n => (a n : ℝ) / 2 ^ a n) s →
      Irrational s := by
  sorry

/-- For positive natural sequences the convergence hypothesis is unnecessary. -/
theorem erdos_260_nat (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hgrowth : Tendsto (fun n => (a n : ℝ) / (n + 1)) atTop atTop) :
    Irrational (∑' n : ℕ, (a n : ℝ) / 2 ^ a n) := by
  sorry

end Erdos260
