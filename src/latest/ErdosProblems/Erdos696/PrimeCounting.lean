import ErdosProblems.Erdos696.AnalyticDefinitions
import ErdosProblems.Erdos696.SiegelWalfiszScales
import BoundedGaps.PrimeNumberTheorem.Analytic.StrongChebyshev
import BoundedGaps.BombieriVinogradov.Analytic.CenteredPrimeAbel

/-! # The global prime-counting estimate with an exponential error -/

namespace Erdos696

open Filter MeasureTheory

lemma exists_eventually_uniform_psi_sw :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ c ≤ 1 ∧
      ∀ᶠ x : ℕ in atTop, ∀ n : ℕ, n ≤ x →
        |Chebyshev.psi (n : ℝ) - n| ≤ C * swError c x := by
  apply exists_eventually_uniform_sw
  · refine ⟨Real.log 4 + 5, by positivity, ?_⟩
    intro n
    calc
      _ ≤ |Chebyshev.psi (n : ℝ)| + |(n : ℝ)| := abs_sub _ _
      _ = Chebyshev.psi (n : ℝ) + n := by
        rw [abs_of_nonneg (Chebyshev.psi_nonneg _), abs_of_nonneg (Nat.cast_nonneg n)]
      _ ≤ (Real.log 4 + 5) * n := by
        have h := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
        linarith only [h]
  · obtain ⟨C, c, hC, hc, N, _, hbound⟩ :=
      BoundedGaps.PrimeNumberTheorem.exists_abs_chebyshevPsi_sub_natCast_le_exp_neg_sqrtLog
    exact ⟨C, c, hC, hc, N, hbound⟩

/-- Uniformity over real endpoints additionally costs the bounded floor error. -/
lemma exists_eventually_uniform_theta_sw :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ c ≤ 1 ∧
      ∀ᶠ x : ℕ in atTop, ∀ t : ℝ, 2 ≤ t → t ≤ x →
        |Chebyshev.theta t - t| ≤ C * swError c x := by
  obtain ⟨C, c, hC, hc, hc1, hbound⟩ := exists_eventually_uniform_psi_sw
  obtain ⟨K, hK⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨C + max K 0 + 1, c, by positivity, hc, hc1, ?_⟩
  have hlogTop : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hbound, eventually_ge_atTop 4, hlogTop.eventually_ge_atTop 4]
    with x hx hx4 hlog
  intro t ht htx
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have ht0 : 0 ≤ t := by linarith only [ht]
  have hn : ⌊t⌋₊ ≤ x := by simpa only [Nat.floor_natCast] using Nat.floor_le_floor htx
  have hfloor := Nat.floor_le ht0
  have hfloorLt := Nat.lt_floor_add_one t
  have hfloorGap : |(⌊t⌋₊ : ℝ) - t| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hfloor)]
    linarith only [hfloorLt]
  have hs : Real.sqrt (x : ℝ) ≤ swError c x := sqrt_le_swError hc1 hx0 hlog
  have hE1 : 1 ≤ swError c x := by
    apply le_trans _ hs
    apply (Real.le_sqrt zero_le_one hx0.le).mpr
    norm_num
    exact_mod_cast (show 1 ≤ x by omega)
  have htheta : |Chebyshev.theta (⌊t⌋₊ : ℝ) - Chebyshev.psi (⌊t⌋₊ : ℝ)| ≤
      max K 0 * swError c x := by
    rw [abs_of_nonpos (sub_nonpos.mpr (Chebyshev.theta_le_psi _)), neg_sub]
    calc
      _ ≤ K * Real.sqrt (⌊t⌋₊ : ℝ) := hK _
      _ ≤ max K 0 * Real.sqrt (⌊t⌋₊ : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
      _ ≤ max K 0 * swError c x :=
        mul_le_mul_of_nonneg_left
          ((Real.sqrt_le_sqrt (by exact_mod_cast hn)).trans hs) (le_max_right _ _)
  rw [Chebyshev.theta_eq_theta_coe_floor]
  have htri : |Chebyshev.theta (⌊t⌋₊ : ℝ) - t| ≤
      |Chebyshev.theta (⌊t⌋₊ : ℝ) - Chebyshev.psi (⌊t⌋₊ : ℝ)| +
        |Chebyshev.psi (⌊t⌋₊ : ℝ) - ⌊t⌋₊| + |(⌊t⌋₊ : ℝ) - t| := by
    calc
      _ ≤ |Chebyshev.theta (⌊t⌋₊ : ℝ) - Chebyshev.psi (⌊t⌋₊ : ℝ)| +
          |Chebyshev.psi (⌊t⌋₊ : ℝ) - t| := abs_sub_le _ _ _
      _ ≤ _ := by
        simpa only [add_assoc] using add_le_add
          (le_rfl : |Chebyshev.theta (⌊t⌋₊ : ℝ) - Chebyshev.psi (⌊t⌋₊ : ℝ)| ≤ _)
          (abs_sub_le (Chebyshev.psi (⌊t⌋₊ : ℝ)) (⌊t⌋₊ : ℝ) t)
  have hpsi := hx ⌊t⌋₊ hn
  nlinarith only [htri, htheta, hpsi, hfloorGap, hE1]

lemma inv_log_continuousOn {x : ℝ} (hx : 2 ≤ x) :
    ContinuousOn (fun t : ℝ => (Real.log t)⁻¹) (Set.uIcc 2 x) := by
  intro t ht
  have ht2 : 2 ≤ t := (Set.uIcc_of_le hx ▸ ht).1
  have ht0 : t ≠ 0 := by linarith only [ht2]
  have hlog0 : Real.log t ≠ 0 := (Real.log_pos (by linarith only [ht2])).ne'
  exact ContinuousAt.continuousWithinAt (by fun_prop)

lemma inv_log_intervalIntegrable {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) volume 2 x :=
  (inv_log_continuousOn hx).intervalIntegrable

lemma inv_log_sq_intervalIntegrable {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t : ℝ => (Real.log t ^ 2)⁻¹) volume 2 x := by
  convert! ((inv_log_continuousOn hx).pow 2).intervalIntegrable (μ := volume) using 1
  funext t
  simp only [Pi.pow_apply, inv_pow]

lemma li_eq_abel {x : ℝ} (hx : 2 ≤ x) :
    li x = x / Real.log x - 2 / Real.log 2 +
      ∫ t in (2 : ℝ)..x, (Real.log t ^ 2)⁻¹ := by
  have hderiv (t : ℝ) (ht : t ∈ Set.uIcc (2 : ℝ) x) :
      HasDerivAt (fun u : ℝ => u / Real.log u)
        ((Real.log t)⁻¹ - (Real.log t ^ 2)⁻¹) t := by
    have ht2 : 2 ≤ t := (Set.uIcc_of_le hx ▸ ht).1
    have ht0 : t ≠ 0 := by linarith only [ht2]
    have hl0 : Real.log t ≠ 0 := (Real.log_pos (by linarith only [ht2])).ne'
    convert! (hasDerivAt_id t).div (Real.hasDerivAt_log ht0) hl0 using 1 <;>
      simp only [id_eq] <;> field_simp <;> ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((inv_log_intervalIntegrable hx).sub (inv_log_sq_intervalIntegrable hx))
  rw [intervalIntegral.integral_sub (inv_log_intervalIntegrable hx)
    (inv_log_sq_intervalIntegrable hx)] at hFTC
  simp only [li, one_div]
  linarith only [hFTC]

lemma primeCounting_error_le_uniform {x : ℕ} (hx : 2 ≤ x) (M : ℝ)
    (hM : ∀ t : ℝ, 2 ≤ t → t ≤ x → |Chebyshev.theta t - t| ≤ M) :
    |(Nat.primeCounting x : ℝ) - li x| ≤ (M + 2) / Real.log 2 := by
  have hxR : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogx : 0 < Real.log (x : ℝ) := Real.log_pos (by linarith only [hxR])
  have hthetaInt : IntervalIntegrable
      (fun t : ℝ => Chebyshev.theta t / (t * Real.log t ^ 2)) volume 2 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hxR).mpr
      (Chebyshev.integrableOn_theta_div_id_mul_log_sq _)
  have hkernelInt : IntervalIntegrable
      (fun t : ℝ => (t * Real.log t ^ 2)⁻¹) volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht2 : 2 ≤ t := (Set.uIcc_of_le hxR ▸ ht).1
    have ht0 : t ≠ 0 := by linarith only [ht2]
    have hlog : Real.log t ≠ 0 := (Real.log_pos (by linarith only [ht2])).ne'
    have hden : t * Real.log t ^ 2 ≠ 0 := mul_ne_zero ht0 (pow_ne_zero 2 hlog)
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hintEq :
      (∫ t in (2 : ℝ)..(x : ℝ), (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) =
        (∫ t in (2 : ℝ)..(x : ℝ), Chebyshev.theta t / (t * Real.log t ^ 2)) -
          ∫ t in (2 : ℝ)..(x : ℝ), (Real.log t ^ 2)⁻¹ := by
    rw [← intervalIntegral.integral_sub hthetaInt (inv_log_sq_intervalIntegrable hxR)]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht2 : 2 ≤ t := (Set.uIcc_of_le hxR ▸ ht).1
    have ht0 : t ≠ 0 := by linarith only [ht2]
    field_simp
  have heq : (Nat.primeCounting x : ℝ) - li x =
      (Chebyshev.theta (x : ℝ) - x) / Real.log (x : ℝ) +
        (∫ t in (2 : ℝ)..(x : ℝ), (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) +
          2 / Real.log 2 := by
    have hpi := Chebyshev.primeCounting_eq_theta_div_log_add_integral hxR
    rw [Nat.floor_natCast] at hpi
    rw [hpi, li_eq_abel hxR, hintEq]
    ring
  have hintBound :
      |∫ t in (2 : ℝ)..(x : ℝ), (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| ≤
        M * ∫ t in (2 : ℝ)..(x : ℝ), (t * Real.log t ^ 2)⁻¹ := by
    rw [← Real.norm_eq_abs, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.norm_integral_le_of_norm_le hxR _ (hkernelInt.const_mul M)
    filter_upwards [] with t ht
    have ht2 : 2 ≤ t := ht.1.le
    have ht0 : 0 < t := by linarith only [ht2]
    have hlog : 0 < Real.log t := Real.log_pos (by linarith only [ht2])
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos ht0 (sq_pos_of_pos hlog)),
      div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hM t ht2 ht.2) (by positivity)
  have hend : |(Chebyshev.theta (x : ℝ) - x) / Real.log (x : ℝ)| ≤
      M * (Real.log (x : ℝ))⁻¹ := by
    rw [abs_div, abs_of_pos hlogx, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hM x hxR le_rfl) (by positivity)
  rw [heq]
  calc
    _ ≤ |(Chebyshev.theta (x : ℝ) - x) / Real.log (x : ℝ)| +
        |∫ t in (2 : ℝ)..(x : ℝ), (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| +
          |2 / Real.log 2| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ M * (Real.log (x : ℝ))⁻¹ +
        M * (∫ t in (2 : ℝ)..(x : ℝ), (t * Real.log t ^ 2)⁻¹) + 2 / Real.log 2 := by
      rw [abs_of_pos (div_pos (by norm_num) hlog2)]
      exact add_le_add (add_le_add hend hintBound) le_rfl
    _ = (M + 2) / Real.log 2 := by
      rw [← mul_add, BoundedGaps.Maynard.primeCountingAbelKernel_mass hx]
      ring

lemma exists_eventually_primeCounting_sw :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ c ≤ 1 ∧
      ∀ᶠ x : ℕ in atTop, |(Nat.primeCounting x : ℝ) - li x| ≤ C * swError c x := by
  obtain ⟨C, c, hC, hc, hc1, hbound⟩ := exists_eventually_uniform_theta_sw
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(C + 2) / Real.log 2, c, by positivity, hc, hc1, ?_⟩
  have hlogTop : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hbound, eventually_ge_atTop 4, hlogTop.eventually_ge_atTop 4]
    with x hx hx4 hlog
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hE1 : 1 ≤ swError c x := by
    apply le_trans _ (sqrt_le_swError hc1 hx0 hlog)
    apply (Real.le_sqrt zero_le_one hx0.le).mpr
    norm_num
    exact_mod_cast (show 1 ≤ x by omega)
  calc
    _ ≤ (C * swError c x + 2) / Real.log 2 :=
      primeCounting_error_le_uniform (by omega) _ hx
    _ ≤ ((C + 2) * swError c x) / Real.log 2 := by
      apply div_le_div_of_nonneg_right _ hlog2.le
      nlinarith only [hE1]
    _ = _ := by ring

end Erdos696
