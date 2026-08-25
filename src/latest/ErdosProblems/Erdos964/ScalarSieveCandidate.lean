import ErdosProblems.Erdos964.GGPYIntegralComparison
import ErdosProblems.Erdos964.SelbergChangeDensity

/-!
# The scalar polynomial candidate

The chosen divisor coefficient is `P(log(R/r)/log R)`, with `P(x)=1+6x`,
cut off at `1 ≤ r < R`. No singular-series multiplier is included: a
common positive scale on all coefficients cancels from the sieve test.
-/

namespace Erdos964

noncomputable def scalarLinearY (R r : ℕ) : ℝ :=
  if 1 ≤ r ∧ r < R then linearSieveWeight (Real.log r / Real.log R) else 0

theorem scalarLinearY_eq_zero_of_radius (R r : ℕ) (hr : R ≤ r) : scalarLinearY R r = 0 := by
  exact if_neg (fun h => hr.not_gt h.2)

theorem scalarLinearY_bounds (R r : ℕ) : 0 ≤ scalarLinearY R r ∧ scalarLinearY R r ≤ 7 := by
  unfold scalarLinearY
  by_cases hr : 1 ≤ r ∧ r < R
  · rw [if_pos hr]
    have hR : (1 : ℝ) < R := by exact_mod_cast hr.1.trans_lt hr.2
    have hrpos : (0 : ℝ) < r := by exact_mod_cast hr.1
    have hlogR := Real.log_pos hR
    have hlogr := Real.log_natCast_nonneg r
    have hlogle : Real.log (r : ℝ) ≤ Real.log (R : ℝ) :=
      Real.log_le_log hrpos (by exact_mod_cast hr.2.le)
    have hlo : 0 ≤ Real.log (r : ℝ) / Real.log (R : ℝ) := div_nonneg hlogr hlogR.le
    have hhi : Real.log (r : ℝ) / Real.log (R : ℝ) ≤ 1 := (div_le_one hlogR).mpr hlogle
    dsimp [linearSieveWeight]
    constructor <;> linarith
  · rw [if_neg hr]
    norm_num

theorem abs_scalarLinearY_le (R r : ℕ) : |scalarLinearY R r| ≤ 7 := by
  rw [abs_of_nonneg (scalarLinearY_bounds R r).1]
  exact (scalarLinearY_bounds R r).2

theorem scalarLinearY_eq_ggpyPolynomial (R r : ℕ) (hr : 1 ≤ r) (hrR : r < R) :
    scalarLinearY R r = ggpyPolynomial (Real.log ((R : ℝ) / r) / Real.log R) := by
  have hR : (1 : ℝ) < R := by exact_mod_cast hr.trans_lt hrR
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hlogR : Real.log (R : ℝ) ≠ 0 := (Real.log_pos hR).ne'
  rw [scalarLinearY, if_pos ⟨hr, hrR⟩, Real.log_div (by linarith : (R : ℝ) ≠ 0) hrpos.ne']
  dsimp [linearSieveWeight, ggpyPolynomial]
  field_simp
  ring

theorem scalarLinearY_nonneg_transform (s : BoundingSieve) (R r : ℕ) :
    0 ≤ scalarSemiprimeTransform s.prodPrimes (scalarLinearY R) r := by
  unfold scalarSemiprimeTransform
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro u _
  split_ifs
  · exact div_nonneg (scalarLinearY_bounds R u).1 (Nat.cast_nonneg _)
  · exact le_refl 0

end Erdos964
