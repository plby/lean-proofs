import ErdosProblems.Erdos67b.LogPhaseSum
import ErdosProblems.Erdos1149.HigherDerivative

/-!
# The logarithmic twist as a real Fourier phase

This is the exact normalization adapter between the complex-power notation
used for Dirichlet series and the `e(x) = exp(2πix)` notation used by the
finite higher-derivative estimates.
-/

open scoped BigOperators

namespace Erdos67b.LogPhaseSum

noncomputable section

/-- The real Fourier argument of `n⁻ⁱᵗ`. -/
def normalizedLogArgument (t x : ℝ) : ℝ :=
  -t * Real.log x / (2 * Real.pi)

/-- On the positive real axis, the two definitions of the logarithmic phase
agree exactly. -/
theorem higherDerivative_phase_normalizedLogArgument
    (t : ℝ) {x : ℝ} (hx : 0 < x) :
    Erdos1149.HigherDerivative.phase (normalizedLogArgument t x) =
      logPhase t x := by
  rw [Erdos1149.HigherDerivative.phase, Real.fourierChar_apply]
  unfold normalizedLogArgument logPhase
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'),
    ← Complex.ofReal_log hx.le]
  congr 1
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hpi]

/-- Natural-number specialization of
`higherDerivative_phase_normalizedLogArgument`. -/
theorem higherDerivative_phase_normalizedLogArgument_nat
    (t : ℝ) {n : ℕ} (hn : 0 < n) :
    Erdos1149.HigherDerivative.phase (normalizedLogArgument t n) =
      natLogTwist n t := by
  unfold natLogTwist
  exact higherDerivative_phase_normalizedLogArgument t (Nat.cast_pos.mpr hn)

/-- A finite positive-index sum of logarithmic twists may therefore be fed
directly to the controlled higher-derivative machinery. -/
theorem sum_higherDerivative_phase_normalizedLogArgument_nat
    (t : ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, 0 < n) :
    (∑ n ∈ s,
        Erdos1149.HigherDerivative.phase (normalizedLogArgument t n)) =
      ∑ n ∈ s, natLogTwist n t := by
  apply Finset.sum_congr rfl
  intro n hn
  exact higherDerivative_phase_normalizedLogArgument_nat t (hs n hn)

end

end Erdos67b.LogPhaseSum
