/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos69.CorrectionErrorBounds

/-!
# Erdős Problem 69: elementary six-term cancellation proof

The development uses six-term cancellation and pairwise coprime composite
dilations, followed by elementary prime estimates and finite CRT moments.

The six-term pattern cancels the initial tail terms. Composite dilations
replace prime-tuple inputs, with an explicit correction whose mean tends
to zero. Finite CRT moment comparison then forces the characteristic
function of the remaining signed tail to tend to zero. Rationality would
force the same characteristic function to tend to one.

The earlier analytic modules `HalaszMean`, `MinorArc`, and `RoughSelberg`
remain available as separate imports; they are not used by this proof.
-/

namespace Erdos69.Elementary

/-- Irrationality of the binary Lambert series of the number of distinct
prime factors. The terms at zero and one vanish. -/
theorem irrational_binaryOmegaSum : Irrational binaryOmegaSum := by
  by_contra h
  obtain ⟨q, hq, z, hz⟩ := exists_integer_multiple_of_not_irrational h
  have hzero := tendsto_fullCharacteristic_norm (q := (q : ℝ)) (by exact_mod_cast hq)
  have hone := tendsto_full_sub_one_norm_of_rational hz
  have hlim := hzero.add hone
  simp only [add_zero] at hlim
  have hbound (m : ℕ) : (1 : ℝ) ≤ ‖fullCharacteristic q m‖ + ‖fullCharacteristic q m - 1‖ := by
    simpa only [norm_one] using norm_le_norm_add_norm_sub (fullCharacteristic q m) (1 : ℂ)
  have hfalse : (1 : ℝ) ≤ 0 := ge_of_tendsto' hlim hbound
  norm_num at hfalse

end Erdos69.Elementary

namespace Erdos69

/-- Erdős problem 69, with the exact series starting at `n = 2`. -/
theorem irrational_omega_series :
    Irrational (∑' n : ℕ, (ArithmeticFunction.cardDistinctFactors (n + 2) : ℝ) / 2 ^ (n + 2)) := by
  rw [← Elementary.binaryOmegaSum_eq_tsum_from_two]
  exact Elementary.irrational_binaryOmegaSum

/-- The binary series counting distinct prime factors is irrational. -/
theorem erdos_69 :
    Irrational (∑' n : ℕ,
      (ArithmeticFunction.cardDistinctFactors (n + 2) : ℝ) / 2 ^ (n + 2)) :=
  irrational_omega_series

end Erdos69
