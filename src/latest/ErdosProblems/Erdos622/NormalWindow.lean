import Mathlib

/-!
# The Gaussian window in the proof of Erdős Problem 622

This file proves the analytic inequality used in Draganić--Keevash--Müyesser,
Lemma 4.7.  If `u v = 1 / 2`, then the standard Gaussian mass of
`[-u, v]` is strictly larger than one half.  The parameters in the paper are
`u = α * √2 / 4` and `v = √2 / α`.

The proof below is deliberately elementary.  In the central range it uses
`exp (-t²/2) ≥ 1 - t²/2`; outside that range it uses the elementary Mills
bound obtained by comparing the Gaussian tail with `t / x` times its density.
-/

open Filter MeasureTheory Set
open scoped Interval

namespace Erdos622

noncomputable section

/-- The unnormalised standard Gaussian density. -/
def gaussianKernel (x : ℝ) : ℝ := Real.exp (-(x ^ 2) / 2)

/-- Its integral from zero to a nonnegative endpoint. -/
def gaussianHalfInterval (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, gaussianKernel t

/-- The standard Gaussian mass of `[-u,v]`, written using evenness. -/
def gaussianWindow (u v : ℝ) : ℝ :=
  (gaussianHalfInterval u + gaussianHalfInterval v) / Real.sqrt (2 * Real.pi)

/-- The one-parameter window occurring in DKM Lemma 4.7. -/
def normalWindow (α : ℝ) : ℝ :=
  gaussianWindow (α * Real.sqrt 2 / 4) (Real.sqrt 2 / α)

/-- The amount of internal linear forest available on the first side in
DKM Lemma 4.7. -/
def dkmM1 (α β : ℝ) : ℝ := max (α / 4) (2 / β - α)

/-- The amount of internal linear forest available on the second side in
DKM Lemma 4.7. -/
def dkmM2 (α β : ℝ) : ℝ := max (β / 4) (1 / α)

/-- The full Gaussian window supplied by the two forest bounds. -/
def dkmGaussianWindow (α β : ℝ) : ℝ :=
  gaussianWindow (dkmM1 α β * Real.sqrt 2) (dkmM2 α β * Real.sqrt 2)

lemma gaussianKernel_pos (x : ℝ) : 0 < gaussianKernel x := by
  exact Real.exp_pos _

lemma gaussianKernel_nonneg (x : ℝ) : 0 ≤ gaussianKernel x :=
  (gaussianKernel_pos x).le

lemma gaussianKernel_continuous : Continuous gaussianKernel := by
  unfold gaussianKernel
  fun_prop

lemma gaussianKernel_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable gaussianKernel volume a b :=
  gaussianKernel_continuous.intervalIntegrable a b

lemma gaussianHalfInterval_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    gaussianHalfInterval a ≤ gaussianHalfInterval b := by
  rw [gaussianHalfInterval, gaussianHalfInterval]
  apply intervalIntegral.integral_mono_interval le_rfl ha hab
  · filter_upwards with t
    exact gaussianKernel_nonneg t
  · exact gaussianKernel_intervalIntegrable 0 b

lemma dkmM1_ge_quarter (α β : ℝ) : α / 4 ≤ dkmM1 α β :=
  le_max_left _ _

lemma dkmM2_ge_inv (α β : ℝ) : 1 / α ≤ dkmM2 α β :=
  le_max_right _ _

/-- The elementary lower bound used on the central part of the proof. -/
lemma one_sub_sq_div_two_le_gaussianKernel (x : ℝ) :
    1 - x ^ 2 / 2 ≤ gaussianKernel x := by
  have h := Real.add_one_le_exp (-(x ^ 2) / 2)
  simpa [gaussianKernel] using (show 1 - x ^ 2 / 2 ≤ Real.exp (-(x ^ 2) / 2) by linarith)

/-- Integrating the elementary exponential lower bound. -/
lemma gaussianHalfInterval_lower {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 ≤ gaussianHalfInterval x := by
  have hpoly : IntervalIntegrable (fun t : ℝ ↦ 1 - t ^ 2 / 2) volume 0 x := by
    exact (by fun_prop : Continuous fun t : ℝ ↦ 1 - t ^ 2 / 2).intervalIntegrable 0 x
  have hmono := intervalIntegral.integral_mono_on hx hpoly
    (gaussianKernel_intervalIntegrable 0 x)
    (fun t _ ↦ one_sub_sq_div_two_le_gaussianKernel t)
  rw [gaussianHalfInterval]
  calc
    x - x ^ 3 / 6 = ∫ t : ℝ in (0 : ℝ)..x, (1 - t ^ 2 / 2) := by
      calc
        _ = (∫ _t : ℝ in (0 : ℝ)..x, (1 : ℝ)) -
            ∫ t : ℝ in (0 : ℝ)..x, t ^ 2 / 2 := by
          norm_num [intervalIntegral.integral_const, integral_pow]
          ring
        _ = _ := by
          exact (intervalIntegral.integral_sub intervalIntegrable_const
            (((continuous_pow 2).div_const 2).intervalIntegrable 0 x)).symm
    _ ≤ ∫ t : ℝ in (0 : ℝ)..x, gaussianKernel t := hmono

/-- The Gaussian integral on the positive half-line in our normalisation. -/
lemma gaussianKernel_integral_Ioi :
    ∫ t : ℝ in Ioi 0, gaussianKernel t = Real.sqrt (2 * Real.pi) / 2 := by
  rw [show gaussianKernel = fun t : ℝ ↦ Real.exp (-(1 / 2 : ℝ) * t ^ 2) by
    ext t
    simp [gaussianKernel]
    ring]
  rw [integral_gaussian_Ioi]
  congr 2
  ring

/-- Splitting the positive half-line at a positive endpoint. -/
lemma gaussianHalfInterval_add_tail {x : ℝ} (hx : 0 ≤ x) :
    gaussianHalfInterval x + ∫ t : ℝ in Ioi x, gaussianKernel t =
      Real.sqrt (2 * Real.pi) / 2 := by
  rw [← gaussianKernel_integral_Ioi]
  simpa [gaussianHalfInterval] using intervalIntegral.integral_interval_add_Ioi
    ((integrable_exp_neg_mul_sq one_half_pos).congr
      (ae_of_all _ fun t ↦ by simp [gaussianKernel]; ring)).integrableOn
    (((integrable_exp_neg_mul_sq one_half_pos).congr
      (ae_of_all _ fun t ↦ by simp [gaussianKernel]; ring)).integrableOn.mono_set
        (Ioi_subset_Ioi hx))

/-- The weighted tail has an exact elementary antiderivative. -/
lemma gaussianKernel_weighted_tail {x : ℝ} (hx : 0 ≤ x) :
    ∫ t : ℝ in Ioi x, t * gaussianKernel t = gaussianKernel x := by
  have hderiv : ∀ t ∈ Ici x,
      HasDerivAt (fun y : ℝ ↦ -gaussianKernel y) (t * gaussianKernel t) t := by
    intro t _
    have hinner : HasDerivAt (fun y : ℝ ↦ -(y ^ 2) / 2) (-t) t := by
      have hinner' := (((hasDerivAt_id t).pow 2).neg.div_const 2)
      have hinner'' : HasDerivAt (fun y : ℝ ↦ -(y ^ 2) / 2)
          (-(2 * t) / 2) t := by simpa [div_eq_mul_inv] using hinner'
      exact hinner''.congr_deriv (by ring)
    have he := (Real.hasDerivAt_exp (-(t ^ 2) / 2)).comp t hinner
    have hneg := he.neg.congr_deriv (show -(Real.exp (-(t ^ 2) / 2) * -t) =
      t * gaussianKernel t by simp [gaussianKernel, mul_comm])
    apply hneg.congr_of_eventuallyEq
    filter_upwards with y
    simp [gaussianKernel, Function.comp_def]
  have hnonneg : ∀ t ∈ Ioi x, 0 ≤ t * gaussianKernel t := by
    intro t ht
    exact mul_nonneg (hx.trans ht.le) (gaussianKernel_nonneg t)
  have htop : Tendsto (fun y : ℝ ↦ -gaussianKernel y) atTop (nhds 0) := by
    have hsq : Tendsto (fun y : ℝ ↦ y ^ 2 / 2) atTop atTop :=
      (Filter.tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).atTop_div_const
        (by norm_num)
    have hbase : Tendsto
        (fun y : ℝ ↦ -Real.exp (-(y ^ 2 / 2))) atTop (nhds 0) := by
      simpa only [Function.comp_apply, neg_zero] using
        (Real.tendsto_exp_neg_atTop_nhds_zero.comp hsq).neg
    apply hbase.congr'
    filter_upwards with y
    simp [gaussianKernel]
    ring
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hnonneg htop
  simpa [gaussianKernel] using h

/-- Mills' elementary upper bound for the unnormalised standard Gaussian tail. -/
lemma gaussianKernel_tail_le {x : ℝ} (hx : 0 < x) :
    ∫ t : ℝ in Ioi x, gaussianKernel t ≤ gaussianKernel x / x := by
  have hkfull : Integrable gaussianKernel := by
    convert integrable_exp_neg_mul_sq one_half_pos using 1
    ext t
    unfold gaussianKernel
    congr 1
    ring
  have hk : IntegrableOn gaussianKernel (Ioi x) := hkfull.integrableOn
  have htk : IntegrableOn (fun t : ℝ ↦ (t / x) * gaussianKernel t) (Ioi x) := by
    have hbase : Integrable (fun t : ℝ ↦ t * gaussianKernel t) :=
      by
        convert integrable_mul_exp_neg_mul_sq one_half_pos using 1
        ext t
        unfold gaussianKernel
        congr 2
        ring
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      hbase.const_mul x⁻¹ |>.integrableOn
  calc
    (∫ t : ℝ in Ioi x, gaussianKernel t) ≤
        ∫ t : ℝ in Ioi x, (t / x) * gaussianKernel t := by
      apply integral_mono_ae hk htk
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hone : (1 : ℝ) ≤ t / x := (le_div_iff₀ hx).2 (by simpa using ht.le)
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hone (gaussianKernel_nonneg t)
    _ = (∫ t : ℝ in Ioi x, t * gaussianKernel t) / x := by
      simp_rw [div_mul_eq_mul_div, ← integral_div]
    _ = gaussianKernel x / x := by rw [gaussianKernel_weighted_tail hx.le]

/-- Algebraic lower bound for the central range. -/
lemma central_polynomial_bound {u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) (huv : u * v = 1 / 2)
    (hu' : u ≤ 3 / 2) (hv' : v ≤ 3 / 2) :
    (1639 : ℝ) / 1296 ≤
      (u - u ^ 3 / 6) + (v - v ^ 3 / 6) := by
  have hu_lower : 1 / 3 ≤ u := by
    nlinarith [mul_le_mul_of_nonneg_left hv' hu.le]
  have hs_upper : u + v ≤ 11 / 6 := by
    have hfac : (u - 1 / 3) * (u - 3 / 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hu_lower) (sub_nonpos.2 hu')
    nlinarith
  have hs_pos : 0 < u + v := add_pos hu hv
  have hs_lower : 7 / 5 ≤ u + v := by
    have hsq : 2 ≤ (u + v) ^ 2 := by nlinarith [sq_nonneg (u - v)]
    nlinarith [sq_nonneg (u + v - 7 / 5)]
  have hbracket :
      0 ≤ 2 * ((u + v) ^ 2 + (u + v) * (11 / 6) + (11 / 6) ^ 2) - 15 := by
    nlinarith [sq_nonneg (u + v - 7 / 5)]
  have hq :
      5 * (11 / 6 : ℝ) / 4 - (11 / 6 : ℝ) ^ 3 / 6 ≤
        5 * (u + v) / 4 - (u + v) ^ 3 / 6 := by
    have hprod := mul_nonneg (sub_nonneg.2 hs_upper) hbracket
    nlinarith
  calc
    (1639 : ℝ) / 1296 =
        5 * (11 / 6 : ℝ) / 4 - (11 / 6 : ℝ) ^ 3 / 6 := by norm_num
    _ ≤ 5 * (u + v) / 4 - (u + v) ^ 3 / 6 := hq
    _ = (u - u ^ 3 / 6) + (v - v ^ 3 / 6) := by
      nlinarith [huv]

/-- The explicit rational central lower bound beats the half Gaussian mass. -/
lemma sqrt_two_pi_div_two_lt_centralConstant :
    Real.sqrt (2 * Real.pi) / 2 < (1639 : ℝ) / 1296 := by
  have hc : 0 < (2 * (1639 : ℝ) / 1296) := by norm_num
  have hsqrt : Real.sqrt (2 * Real.pi) < 2 * (1639 : ℝ) / 1296 := by
    rw [Real.sqrt_lt' hc]
    nlinarith [Real.pi_lt_d4]
  linarith

/-- The DKM Gaussian-window inequality in its symmetric two-parameter form. -/
theorem gaussianWindow_gt_half {u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) (huv : u * v = 1 / 2) :
    1 / 2 < gaussianWindow u v := by
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (mul_pos two_pos Real.pi_pos)
  have hmass : Real.sqrt (2 * Real.pi) / 2 <
      gaussianHalfInterval u + gaussianHalfInterval v := by
    rcases le_or_gt u (3 / 2) with hu_small | hu_large
    · rcases le_or_gt v (3 / 2) with hv_small | hv_large
      · have hpoly := central_polynomial_bound hu hv huv hu_small hv_small
        have hu_int := gaussianHalfInterval_lower hu.le
        have hv_int := gaussianHalfInterval_lower hv.le
        have hconst := sqrt_two_pi_div_two_lt_centralConstant
        linarith
      · have hult : u < 1 / 3 := by
          have := mul_lt_mul_of_pos_left hv_large hu
          nlinarith
        have hk : gaussianKernel v < 2 / 5 := by
          calc
            gaussianKernel v = Real.exp (-(v ^ 2) / 2) := rfl
            _ < Real.exp (-1) := Real.exp_lt_exp.mpr (by nlinarith [sq_nonneg (v - 3 / 2)])
            _ < 2 / 5 := Real.exp_neg_one_lt_d9.trans (by norm_num)
        have hu_sq : u ^ 2 < 1 / 9 := by nlinarith [sq_nonneg (u - 1 / 3)]
        have hvu3 : v * u ^ 3 = u ^ 2 / 2 := by
          calc
            v * u ^ 3 = (u * v) * u ^ 2 := by ring
            _ = u ^ 2 / 2 := by rw [huv]; ring
        have hscaled : 2 / 5 < v * (u - u ^ 3 / 6) := by
          calc
            2 / 5 < v * u - (u ^ 2 / 2) / 6 := by nlinarith
            _ = v * (u - u ^ 3 / 6) := by rw [← hvu3]; ring
        have htail_lt : (∫ t : ℝ in Ioi v, gaussianKernel t) <
            gaussianHalfInterval u := by
          calc
            (∫ t : ℝ in Ioi v, gaussianKernel t) ≤ gaussianKernel v / v :=
              gaussianKernel_tail_le hv
            _ < u - u ^ 3 / 6 := by
              rw [div_lt_iff₀ hv]
              simpa [mul_comm] using hk.trans hscaled
            _ ≤ gaussianHalfInterval u := gaussianHalfInterval_lower hu.le
        nlinarith [gaussianHalfInterval_add_tail hv.le]
    · have hvlt : v < 1 / 3 := by
        have := mul_lt_mul_of_pos_right hu_large hv
        nlinarith
      have hk : gaussianKernel u < 2 / 5 := by
        calc
          gaussianKernel u = Real.exp (-(u ^ 2) / 2) := rfl
          _ < Real.exp (-1) := Real.exp_lt_exp.mpr (by nlinarith [sq_nonneg (u - 3 / 2)])
          _ < 2 / 5 := Real.exp_neg_one_lt_d9.trans (by norm_num)
      have hv_sq : v ^ 2 < 1 / 9 := by nlinarith [sq_nonneg (v - 1 / 3)]
      have huv3 : u * v ^ 3 = v ^ 2 / 2 := by
        calc
          u * v ^ 3 = (u * v) * v ^ 2 := by ring
          _ = v ^ 2 / 2 := by rw [huv]; ring
      have hscaled : 2 / 5 < u * (v - v ^ 3 / 6) := by
        calc
          2 / 5 < u * v - (v ^ 2 / 2) / 6 := by nlinarith
          _ = u * (v - v ^ 3 / 6) := by rw [← huv3]; ring
      have htail_lt : (∫ t : ℝ in Ioi u, gaussianKernel t) <
          gaussianHalfInterval v := by
        calc
          (∫ t : ℝ in Ioi u, gaussianKernel t) ≤ gaussianKernel u / u :=
            gaussianKernel_tail_le hu
          _ < v - v ^ 3 / 6 := by
            rw [div_lt_iff₀ hu]
            simpa [mul_comm] using hk.trans hscaled
          _ ≤ gaussianHalfInterval v := gaussianHalfInterval_lower hv.le
      nlinarith [gaussianHalfInterval_add_tail hu.le]
  rw [gaussianWindow, lt_div_iff₀ hsqrt]
  nlinarith

/-- The Gaussian window in DKM Lemma 4.7 has mass strictly above `1/2`. -/
theorem normalWindow_gt_half {α : ℝ} (hα : 0 < α) :
    1 / 2 < normalWindow α := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  apply gaussianWindow_gt_half
  · positivity
  · positivity
  · have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp [hα.ne']
    nlinarith

/-- The full `m₁,m₂` window contains the one-parameter window used in the
analytic estimate.  This is the formal version of
`I[-m₁,m₂] ≥ I[-α/4,1/α]`. -/
theorem normalWindow_le_dkmGaussianWindow {α β : ℝ} (hα : 0 < α) :
    normalWindow α ≤ dkmGaussianWindow α β := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hm1 : α * Real.sqrt 2 / 4 ≤ dkmM1 α β * Real.sqrt 2 := by
    have := mul_le_mul_of_nonneg_right (dkmM1_ge_quarter α β) hsqrt.le
    nlinarith
  have hm2 : Real.sqrt 2 / α ≤ dkmM2 α β * Real.sqrt 2 := by
    have := mul_le_mul_of_nonneg_right (dkmM2_ge_inv α β) hsqrt.le
    rw [div_mul_eq_mul_div] at this
    simpa only [one_mul] using this
  have hu := gaussianHalfInterval_mono
    (by positivity : 0 ≤ α * Real.sqrt 2 / 4) hm1
  have hv := gaussianHalfInterval_mono
    (by positivity : 0 ≤ Real.sqrt 2 / α) hm2
  have hden : 0 ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
  rw [normalWindow, dkmGaussianWindow, gaussianWindow, gaussianWindow]
  exact div_le_div_of_nonneg_right (add_le_add hu hv) hden

/-- On every compact positive parameter interval, the Gaussian advantage has
a uniform positive margin. -/
theorem normalWindow_uniform_margin {η M : ℝ}
    (hη : 0 < η) (hηM : η ≤ M) :
    ∃ margin : ℝ, 0 < margin ∧ ∀ α ∈ Set.Icc η M, 1 / 2 + margin ≤ normalWindow α := by
  have hhalf : Continuous gaussianHalfInterval :=
    intervalIntegral.continuous_primitive gaussianKernel_intervalIntegrable 0
  have hcont : ContinuousOn normalWindow (Icc η M) := by
    apply continuousOn_of_forall_continuousAt
    intro α hα
    have hα0 : α ≠ 0 := ne_of_gt (hη.trans_le hα.1)
    have hu : ContinuousAt (fun x : ℝ ↦ x * Real.sqrt 2 / 4) α := by fun_prop
    have hv : ContinuousAt (fun x : ℝ ↦ Real.sqrt 2 / x) α := by fun_prop
    change ContinuousAt
      (fun x : ℝ ↦ (gaussianHalfInterval (x * Real.sqrt 2 / 4) +
        gaussianHalfInterval (Real.sqrt 2 / x)) / Real.sqrt (2 * Real.pi)) α
    exact (((hhalf.continuousAt.comp hu).add (hhalf.continuousAt.comp hv)).div_const
      (Real.sqrt (2 * Real.pi)))
  obtain ⟨α₀, hα₀, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hηM) hcont
  have hα₀pos : 0 < α₀ := hη.trans_le hα₀.1
  have hstrict : 1 / 2 < normalWindow α₀ := normalWindow_gt_half hα₀pos
  refine ⟨(normalWindow α₀ - 1 / 2) / 2, by linarith, ?_⟩
  intro α hα
  have hle := hmin hα
  change normalWindow α₀ ≤ normalWindow α at hle
  linarith

/-- The same compact uniform margin holds for every positive second cover
parameter, because the `m₁,m₂` window is larger. -/
theorem dkmGaussianWindow_uniform_margin {η M : ℝ}
    (hη : 0 < η) (hηM : η ≤ M) :
    ∃ margin : ℝ, 0 < margin ∧
      ∀ α ∈ Set.Icc η M, ∀ β : ℝ, 1 / 2 + margin ≤ dkmGaussianWindow α β := by
  obtain ⟨margin, hmargin, hwindow⟩ := normalWindow_uniform_margin hη hηM
  refine ⟨margin, hmargin, ?_⟩
  intro α hα β
  exact (hwindow α hα).trans (normalWindow_le_dkmGaussianWindow (hη.trans_le hα.1))

end

end Erdos622
