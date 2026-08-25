import Util.Linnik.EffectiveGap
import Util.Linnik.StrongPsi
import ErdosProblems.Erdos48.EndpointPowerScale

/-!
# Polynomial endpoint and truncation scales

We truncate at height `n^4` and use an endpoint `n^L`, with a fixed large
exponent.  The associated logarithm is between `log n` and `6 log n`.
-/

namespace Linnik

open Filter Erdos48 BoundedGaps.Maynard
open scoped Topology

noncomputable def logScale (n : ℕ) : ℝ := Real.log ((n : ℝ) * ((n : ℝ) ^ 4 + 2))

theorem logScale_bounds {n : ℕ} (hn : 2 ≤ n) :
    Real.log (n : ℝ) ≤ logScale n ∧ logScale n ≤ 6 * Real.log (n : ℝ) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hp : 2 ≤ (n : ℝ) ^ 4 := by nlinarith [sq_nonneg ((n : ℝ) ^ 2 - 2)]
  have hprod : (n : ℝ) * ((n : ℝ) ^ 4 + 2) ≤ (n : ℝ) ^ 6 := by
    calc
      _ ≤ (n : ℝ) * ((n : ℝ) ^ 4 + (n : ℝ) ^ 4) := by gcongr
      _ = 2 * (n : ℝ) ^ 5 := by ring
      _ ≤ (n : ℝ) * (n : ℝ) ^ 5 := by gcongr
      _ = _ := by ring
  constructor
  · apply Real.log_le_log hnpos
    nlinarith [pow_nonneg hnpos.le 4]
  · calc
      logScale n ≤ Real.log ((n : ℝ) ^ 6) := Real.log_le_log (by positivity) hprod
      _ = 6 * Real.log (n : ℝ) := by rw [Real.log_pow]; norm_num

theorem tendsto_logScale : Tendsto logScale atTop atTop := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply tendsto_atTop.2
  intro b
  filter_upwards [hlog.eventually_ge_atTop b, eventually_ge_atTop 2] with n hn hn₂
  exact hn.trans (logScale_bounds hn₂).1

theorem tendsto_nat_pow {L : ℕ} (hL : 1 ≤ L) :
    Tendsto (fun n : ℕ ↦ n ^ L) atTop atTop := by
  apply Filter.tendsto_atTop_mono (f := fun n : ℕ ↦ n)
  · intro n
    exact Nat.le_pow (by omega)
  · exact tendsto_id

theorem logScale_mul_le_log_pow {n L : ℕ} {D : ℝ}
    (hn : 2 ≤ n) (hD : 0 ≤ D) (hL : 6 * D ≤ L) :
    D * logScale n ≤ Real.log ((n ^ L : ℕ) : ℝ) := by
  rw [log_natCast_pow]
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have h := mul_le_mul_of_nonneg_left (logScale_bounds hn).2 hD
  have h' := mul_le_mul_of_nonneg_right hL hlog
  nlinarith

theorem logScale_le_six_log_pow {n L : ℕ} (hn : 2 ≤ n) (hL : 1 ≤ L) :
    logScale n ≤ 6 * Real.log ((n ^ L : ℕ) : ℝ) := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  rw [log_natCast_pow]
  nlinarith [(logScale_bounds hn).2]

theorem eventually_abs_psi_pow_sub_mul_logScale_sq_le
    {epsilon : ℝ} (hepsilon : 0 < epsilon) {L : ℕ} (hL : 1 ≤ L) :
    ∀ᶠ n : ℕ in atTop,
      |Chebyshev.psi ((n ^ L : ℕ) : ℝ) - ((n ^ L : ℕ) : ℝ)| * logScale n ^ 2 ≤
        epsilon * ((n ^ L : ℕ) : ℝ) := by
  have hpsi := (tendsto_nat_pow hL).eventually
    (eventually_abs_psi_sub_mul_log_sq_le (show 0 < epsilon / 36 by positivity))
  filter_upwards [hpsi, eventually_ge_atTop 2] with n hn hn₂
  have hnL : 1 ≤ n ^ L := Nat.one_le_pow L n (by omega)
  have hlog : 0 ≤ Real.log ((n ^ L : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast hnL)
  have hH₀ : 0 ≤ logScale n := (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))).trans
    (logScale_bounds hn₂).1
  have hH := logScale_le_six_log_pow hn₂ hL
  have hsq : logScale n ^ 2 ≤ 36 * Real.log ((n ^ L : ℕ) : ℝ) ^ 2 := by nlinarith
  have h := mul_le_mul_of_nonneg_left hsq
    (abs_nonneg (Chebyshev.psi ((n ^ L : ℕ) : ℝ) - ((n ^ L : ℕ) : ℝ)))
  nlinarith

theorem powerScale_explicitError_eq {n L K : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ 2 * ((K : ℝ) * dirichletExplicitFormulaErrorScale
      ((n ^ L : ℕ) : ℝ) n ((n ^ 4 : ℕ) : ℝ)) =
      ((n ^ L : ℕ) : ℝ) * ((K : ℝ) * ((L : ℝ) + 1) ^ 2 *
        (Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold dirichletExplicitFormulaErrorScale
  rw [Nat.cast_pow, Nat.cast_pow, Real.log_mul (by positivity) hnR.ne', Real.log_pow]
  field_simp

theorem powerScale_farKernel_le {n L A : ℕ} (hn : 2 ≤ n) (hL : 64 ≤ L) :
    (n : ℝ) ^ 2 * (96 * (A : ℝ) *
      (((n ^ L : ℕ) : ℝ) ^ (15 / 16 : ℝ)) * logScale n ^ 2) ≤
      ((n ^ L : ℕ) : ℝ) * ((3456 * (A : ℝ)) *
        (Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ 2)) := by
  have hpow := natPow_rpow_fifteen_sixteen_le_div_four (by omega : 1 ≤ n) hL
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hH := logScale_bounds hn
  have hsq : logScale n ^ 2 ≤ 36 * Real.log (n : ℝ) ^ 2 := by nlinarith
  calc
    _ ≤ (n : ℝ) ^ 2 * (96 * (A : ℝ) *
        (((n ^ L : ℕ) : ℝ) / (n : ℝ) ^ 4) * (36 * Real.log (n : ℝ) ^ 2)) := by gcongr
    _ = _ := by field_simp; ring

end Linnik
