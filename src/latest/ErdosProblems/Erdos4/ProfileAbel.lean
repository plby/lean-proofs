import ErdosProblems.Erdos4.ProfileSmooth
import BoundedGaps.Maynard.LogarithmicAbelMain

/-!
# Abel transfer for the explicit logarithmic profile

The main term is evaluated using its known primitive. The error costs at
most twice the cumulative error, uniformly in the completion endpoint.
-/

open MeasureTheory
open scoped BigOperators Topology

namespace Erdos4.ProfileAbel

open PrimitiveProfile ProfileSmooth BoundedGaps.Maynard

theorem main_term_eq {m k : ℝ} (hm : 0 < m) (hk : 0 ≤ k)
    {R T : ℕ} (hR : 2 ≤ R) (hT : 1 ≤ T) (ρ : ℝ) :
    logarithmicAbelMain T ρ (scaled m k R) =
      ρ * Real.log R * primitive m k (Real.log T / Real.log R) := by
  have hTreal : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hR)
  have hfcont : ContinuousOn (scaled m k R) (Set.Icc (1 : ℝ) T) := by
    intro x hx
    exact (hasDerivAt_scaled hm hk hR hx.1).continuousAt.continuousWithinAt
  have hfderiv : ∀ x ∈ Set.Icc (1 : ℝ) T,
      HasDerivAt (scaled m k R) (deriv (scaled m k R) x) x := by
    intro x hx
    have hd := hasDerivAt_scaled hm hk hR hx.1
    simpa only [hd.deriv] using hd
  have hdcont : ContinuousOn (deriv (scaled m k R)) (Set.uIcc (1 : ℝ) T) := by
    rw [Set.uIcc_of_le hTreal]
    exact continuousOn_deriv_scaled hm hk hR T
  rw [logarithmicAbelMain_eq_intervalIntegral_div hT hfcont hfderiv hdcont.intervalIntegrable]
  let F : ℝ → ℝ := fun x => ρ * Real.log R * primitive m k (Real.log x / Real.log R)
  have hF : ∀ x ∈ Set.uIcc (1 : ℝ) T,
      HasDerivAt F (scaled m k R x * (ρ / x)) x := by
    intro x hx
    rw [Set.uIcc_of_le hTreal] at hx
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
    have ht : 0 ≤ Real.log x / Real.log R := div_nonneg (Real.log_nonneg hx.1) hlog.le
    have hd := ((hasDerivAt_primitive hm hk ht).comp x
      ((Real.hasDerivAt_log hxpos.ne').div_const (Real.log R))).const_mul (ρ * Real.log R)
    have heq : ρ * Real.log R * (profile m k (Real.log x / Real.log R) * (x⁻¹ / Real.log R)) =
        scaled m k R x * (ρ / x) := by
      unfold scaled
      field_simp
    exact heq ▸ hd
  have hfU : ContinuousOn (scaled m k R) (Set.uIcc (1 : ℝ) T) := by
    rw [Set.uIcc_of_le hTreal]
    exact hfcont
  have hratio : ContinuousOn (fun x : ℝ => ρ / x) (Set.uIcc (1 : ℝ) T) := by
    apply continuousOn_const.div continuousOn_id
    intro x hx
    rw [Set.uIcc_of_le hTreal] at hx
    exact (lt_of_lt_of_le zero_lt_one hx.1).ne'
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hF (hfU.mul hratio).intervalIntegrable
  simpa only [F, Real.log_one, zero_div, primitive_zero, mul_zero, sub_zero] using hh

/-- A cumulative error `E` costs at most `2E` for this profile. -/
theorem weighted_error_le {m k : ℝ} (hm : 1 ≤ m) (hk : 0 ≤ k)
    {R T : ℕ} (hR : 2 ≤ R) (hT : 1 ≤ T) {c : ℕ → ℝ} (hc : c 0 = 0)
    {ρ E : ℝ} (hE : 0 ≤ E)
    (happrox : ∀ x ∈ Set.Icc (1 : ℝ) T,
      |abelCumulative c x - ρ * Real.log x| ≤ E) :
    |(∑ n ∈ Finset.Icc 0 T, scaled m k R n * c n) -
      ρ * Real.log R * primitive m k (Real.log T / Real.log R)| ≤ 2 * E := by
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hTreal : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hdcont := continuousOn_deriv_scaled hmpos hk hR (T : ℝ)
  have hdint : IntegrableOn (deriv (scaled m k R)) (Set.Icc (1 : ℝ) T) :=
    hdcont.integrableOn_Icc
  have hnormint : IntegrableOn (fun x => |deriv (scaled m k R) x|) (Set.Ioc (1 : ℝ) T) := by
    exact hdcont.abs.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hlogcont : ContinuousOn (fun x : ℝ => ρ * Real.log x) (Set.Icc (1 : ℝ) T) :=
    continuousOn_const.mul (continuousOn_id.log (fun x hx => (lt_of_lt_of_le zero_lt_one hx.1).ne'))
  have hmainint : IntegrableOn (fun x => deriv (scaled m k R) x * (ρ * Real.log x))
      (Set.Ioc (1 : ℝ) T) := (hdcont.mul hlogcont).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hvariation : (∫ x in Set.Ioc (1 : ℝ) T, |deriv (scaled m k R) x|) ≤ 1 := by
    rw [← intervalIntegral.integral_of_le hTreal]
    exact variation_le_one hm hk hR hTreal
  have hh := abs_weightedSum_sub_logarithmicAbelMain_le hT hc hE
    (fun x hx => (hasDerivAt_scaled hmpos hk hR hx.1).differentiableAt)
    hdint hnormint hmainint happrox hvariation
  rw [main_term_eq hmpos hk hR hT ρ] at hh
  have ht : 0 ≤ Real.log (T : ℝ) / Real.log R :=
    div_nonneg (Real.log_natCast_nonneg T) (Real.log_natCast_nonneg R)
  have hendpoint : |scaled m k R T| ≤ 1 := by
    unfold scaled
    rw [abs_of_nonneg (profile_pos hmpos.le hk ht).le]
    exact profile_le_one hm hk ht
  exact hh.trans ((mul_le_mul_of_nonneg_left (by linarith : |scaled m k R T| + 1 ≤ 2) hE).trans_eq (by ring))

end Erdos4.ProfileAbel
