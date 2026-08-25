import ErdosProblems.Erdos157.PrimePowerSeries
import ErdosProblems.Erdos157.InverseRootSeries
import ErdosProblems.Erdos157.CharacterZeroFree

/-! The elementary quantitative estimate for weighted prime-power sums. -/

namespace Erdos157.Elementary.PolynomialCharacters

open Polynomial

variable {K : Type*} [Field K] [DecidableEq K] [Fintype K]

/-- The prime-power and inverse-root expansions have identical scalar coefficients. -/
theorem primePowerCoefficient_eq_rootPowerCoefficient (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (hχ : χ ≠ 1) (n : ℕ) :
    primePowerCoefficient g χ n = rootPowerCoefficient (inverseRootAt (lPolynomial g χ)) n := by
  let q : ℝ := Fintype.card K
  have hq : 0 < q := by dsimp only [q]; exact_mod_cast Fintype.card_pos (α := K)
  let r : ℝ := 1 / (2 * q)
  have hr : 0 < r := by dsimp only [r]; positivity
  have hqr : q * r < 1 := by
    have heq : q * r = 1 / 2 := by dsimp only [r]; field_simp
    rw [heq]
    norm_num
  let f := fun z : ℂ => z * ((lPolynomial g χ).derivative.eval z / (lPolynomial g χ).eval z)
  have ha := summable_norm_primePowerCoefficient g hg χ r hr hqr
  have hb := summable_norm_rootPowerCoefficient (inverseRootAt (lPolynomial g χ)) r hr.le
    (fun i => (mul_le_mul_of_nonneg_right (lPolynomial_inverseRoot_norm_le g hg χ hχ i)
      hr.le).trans_lt hqr)
  have heq := scalar_coefficients_eq (primePowerCoefficient g χ)
    (rootPowerCoefficient (inverseRootAt (lPolynomial g χ))) f r hr ha hb
    (fun z hz => hasSum_primePowerCoefficient g hg χ hχ r hr hqr z hz)
    (fun z hz => hasSum_lPolynomial_rootPowerCoefficient g hg χ hχ z
      ((mul_le_mul_of_nonneg_left hz.le (by positivity)).trans_lt hqr))
  exact congrFun heq n

/-- Quantitative cancellation in each positive-degree weighted prime-power sum. -/
theorem norm_primePowerCoefficient_le (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (hχ : χ ≠ 1) (hχ2 : χ ^ 2 ≠ 1)
    (n : ℕ) (hn : 0 < n) :
    ‖primePowerCoefficient g χ n‖ ≤
      (g.natDegree : ℝ) * (Fintype.card K : ℝ) ^ n *
        Real.exp (-(n : ℝ) / (100 * (g.natDegree : ℝ))) := by
  rw [primePowerCoefficient_eq_rootPowerCoefficient g hg χ hχ,
    rootPowerCoefficient, if_neg hn.ne', norm_neg]
  exact norm_inverseRoot_powerSum_le g hg χ hχ hχ2 n

end Erdos157.Elementary.PolynomialCharacters
