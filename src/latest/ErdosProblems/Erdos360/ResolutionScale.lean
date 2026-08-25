import Mathlib

namespace Erdos360

/-- The real-valued scale in the Conlon--Fox--Pham resolution. -/
noncomputable def resolutionScale (n : ℕ) : ℝ :=
  Real.rpow (n : ℝ) (1 / 3 : ℝ) *
      ((n : ℝ) / (Nat.totient n : ℝ)) /
    (Real.rpow (Real.log n) (1 / 3 : ℝ) *
      Real.rpow (Real.log (Real.log n)) (2 / 3 : ℝ))

end Erdos360
