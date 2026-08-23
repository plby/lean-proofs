import Mathlib


open scoped BigOperators
open ArithmeticFunction

namespace Erdos259

open scoped Classical in
theorem erdos_259 :
    Irrational
      (∑' (n : ℕ), ((moebius n ^ 2 : ℤ) : ℝ) * (n : ℝ) / (2 : ℝ) ^ n) := by
  sorry

end Erdos259
