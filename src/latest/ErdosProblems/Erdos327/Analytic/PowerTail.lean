import ErdosProblems.Erdos327.Analytic.PowerConvolution
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons

/-!
# Explicit tails of negative real powers

The scheduled mixed bulk begins at a dyadic index comparable with
`log L`.  To retain that moving lower endpoint, we use the integral test
with an explicit constant rather than merely the qualitative summability
of the profile.
-/

namespace Erdos327.Analytic

open Finset Real Set

noncomputable section

/-- Constant in the integral-test bound for a power below `-1`. -/
def powerTailConstant (r : ℝ) : ℝ := (-(r + 1))⁻¹

theorem powerTailConstant_pos
    {r : ℝ} (hr : r < -1) :
    0 < powerTailConstant r := by
  unfold powerTailConstant
  exact inv_pos.mpr (by linarith)

/-- A finite tail of `j ↦ (j+1)^r`, for `r < -1`, is bounded by the
expected power of its lower endpoint. -/
theorem sum_Ico_add_one_rpow_le
    {r : ℝ} (hr : r < -1)
    {J M : ℕ} (hJ : 1 ≤ J) :
    (∑ j ∈ Ico J M, (((j + 1 : ℕ) : ℝ) ^ r)) ≤
      powerTailConstant r * (J : ℝ) ^ (r + 1) := by
  let f : ℝ → ℝ := fun x ↦ x ^ r
  have hr0 : r ≤ 0 := by linarith
  have hJpos : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hanti :
      AntitoneOn f (Icc (J : ℝ) (M : ℝ)) := by
    exact
      (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hr0).mono
        (by
          intro x hx
          exact hJpos.trans_le hx.1)
  have hint :=
    hanti.sum_Ico_le_integral
      (integrableOn_Ioi_rpow_of_lt hr hJpos)
      (by
        intro x hx
        exact Real.rpow_nonneg
          (hJpos.le.trans (mem_Ioi.mp hx).le) _)
  rw [integral_Ioi_rpow_of_lt hr hJpos] at hint
  calc
    (∑ j ∈ Ico J M, (((j + 1 : ℕ) : ℝ) ^ r))
        ≤ -(J : ℝ) ^ (r + 1) / (r + 1) := by
          simpa [f] using hint
    _ = powerTailConstant r * (J : ℝ) ^ (r + 1) := by
      unfold powerTailConstant
      have hne : r + 1 ≠ 0 := by linarith
      field_simp

end

end Erdos327.Analytic
