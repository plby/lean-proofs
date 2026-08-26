import Mathlib

open Filter

namespace Erdos768

/-- Every prime divisor has a nontrivial divisor congruent to one modulo it. -/
def SylowDivisor (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → ∃ d : ℕ, d ∣ n ∧ 1 < d ∧ d % p = 1

open scoped Classical in
/-- The number of positive integers at most `x` with the Sylow divisor condition. -/
noncomputable def Acount (x : ℝ) : ℕ :=
  ((Finset.Icc 1 ⌊x⌋₊).filter SylowDivisor).card

noncomputable def c₀ : ℝ := 1 / (2 * Real.sqrt (Real.log 2))

/-- The counting function has the asserted logarithmic asymptotic. -/
theorem erdos_768 :
    Tendsto
      (fun x : ℝ =>
        Real.log (x / (Acount x : ℝ)) / (Real.sqrt (Real.log x) * Real.log (Real.log x)))
      atTop (nhds c₀) := by
  sorry

end Erdos768
