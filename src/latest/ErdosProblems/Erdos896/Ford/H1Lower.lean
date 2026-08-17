/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Ford.H1Count
import ErdosProblems.Erdos896.Ford.IsolatedSum
import ErdosProblems.Erdos896.Ford.StirlingScale

/-!
# Ford's fixed-dyadic exact-one-divisor lower bound

This file assembles the finite exact-one-divisor construction, the
reciprocal isolated-divisor mass estimate, and the critical-index Stirling
conversion.  The main statement is uniform in the polynomial range
`y ^ 3 ≤ N` and keeps the natural cutoff `N * y` exactly.

The scaled companion is stated with cross-multiplied endpoints.  Thus its
window is literally

`N < 2 * p * d ∧ p * d ≤ N`,

with no floor or ceiling convention at `N / (2p)` and `N / p`.
-/

namespace Erdos896.Ford

open Filter Asymptotics

/-! ## The natural dyadic window as an exact scaled window -/

theorem scaledDivisorWindow_two_mul_one (n y : ℕ) :
    scaledDivisorWindow (2 * y) 1 n = divisorWindow n y (2 * y) := by
  ext d
  simp only [mem_scaledDivisorWindow, mem_divisorWindow]
  constructor
  · rintro ⟨hdn, hn0, hlower, hupper⟩
    exact ⟨hdn, hn0, by omega, by simpa using hupper⟩
  · rintro ⟨hdn, hn0, hlower, hupper⟩
    exact ⟨hdn, hn0, by omega, by simpa using hupper⟩

theorem scaledTau_two_mul_one (n y : ℕ) :
    scaledTau (2 * y) 1 n = tau n y (2 * y) := by
  simp [scaledTau, tau, scaledDivisorWindow_two_mul_one]

theorem scaledH1Set_two_mul_one (X y : ℕ) :
    scaledH1Set (2 * y) 1 X = HrSet 1 X y (2 * y) := by
  ext n
  simp [scaledH1Set, HrSet, scaledTau_two_mul_one]

/-- The fixed dyadic count is exactly the cross-multiplied count with
numerator `2y` and scaling factor `1`. -/
theorem scaledH1_two_mul_one (X y : ℕ) :
    scaledH1 (2 * y) 1 X = H1 X y (2 * y) := by
  simp [scaledH1, H1, Hr, scaledH1Set_two_mul_one]

end Erdos896.Ford
