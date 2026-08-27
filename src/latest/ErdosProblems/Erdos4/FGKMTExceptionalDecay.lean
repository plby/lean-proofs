import ErdosProblems.Erdos4.FGKMTExceptionalKernel
import BoundedGaps.BombieriVinogradov.Analytic.SiegelWalfiszScale

/-! Square-root-logarithmic decay from the common exceptional zero gap. -/

namespace Erdos4.FGKMT

theorem exceptional_power_decay {U Q : ℕ} (hU : 2 ≤ U) (hQ : 2 ≤ Q)
    {x : ℝ} (hx : 0 < x) (hlog : 1 ≤ Real.log x)
    (hQheight : (Q : ℝ) ≤ Real.exp (Real.sqrt (Real.log x))) :
    x ^ (1 - exceptionalWidth U Q) ≤
      x * Real.exp (-(1 / (4 * (U : ℝ) ^ 2)) * Real.sqrt (Real.log x)) := by
  let u := Real.sqrt (Real.log x)
  have hu1 : 1 ≤ u := Real.one_le_sqrt.mpr hlog
  have hu0 : 0 < u := zero_lt_one.trans_le hu1
  have hUs : (0 : ℝ) < U := by exact_mod_cast (by omega : 0 < U)
  have hQr : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQpos : (0 : ℝ) < Q := by linarith
  have hlogQ : Real.log (Q : ℝ) ≤ u := by
    have hh := Real.log_le_log hQpos hQheight
    simpa only [Real.log_exp] using hh
  have hLpos : 0 < Real.log (2 * (Q : ℝ) ^ 2) := Real.log_pos (by nlinarith)
  have hL : Real.log (2 * (Q : ℝ) ^ 2) ≤ 4 * u := by
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ hQpos.ne'), Real.log_pow]
    have hlog2 : Real.log 2 ≤ 1 := Real.log_two_lt_d9.le.trans (by norm_num)
    norm_num
    linarith
  have hwidth : 1 / (4 * (U : ℝ) ^ 2 * u) ≤ exceptionalWidth U Q := by
    apply one_div_le_one_div_of_le (mul_pos (sq_pos_of_pos hUs) hLpos)
    have hh := mul_le_mul_of_nonneg_left hL (sq_nonneg (U : ℝ))
    nlinarith
  have husq : u ^ 2 = Real.log x := Real.sq_sqrt (zero_le_one.trans hlog)
  have hscale : (1 / (4 * (U : ℝ) ^ 2)) * u ≤ exceptionalWidth U Q * Real.log x := by
    calc
      _ = (1 / (4 * (U : ℝ) ^ 2 * u)) * Real.log x := by
        rw [← husq]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hwidth (zero_le_one.trans hlog)
  have hright : x * Real.exp (-(1 / (4 * (U : ℝ) ^ 2)) * u) =
      Real.exp (Real.log x - (1 / (4 * (U : ℝ) ^ 2)) * u) := by
    conv_lhs => lhs; rw [← Real.exp_log hx]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Real.rpow_def_of_pos hx, hright]
  apply Real.exp_le_exp.mpr
  nlinarith

end Erdos4.FGKMT
