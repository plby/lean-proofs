/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos783.GSLocalKernelChange
import ErdosProblems.Erdos783.GSSection6

/-! # Proposition 6.1 estimates of Granville--Soundararajan -/

open MeasureTheory Set Finset

namespace Erdos783

noncomputable section

/-- The finite alternating exponential sum through degree `N`. -/
def gsExpAlternatingSum (z : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1), (-1 : ℝ) ^ j * z ^ j / j.factorial

lemma gs_fill_even_prefix_eq_exp
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {u0 u : ℝ} (hu0 : 1 ≤ u0) (hu : 1 ≤ u)
    (r : ℕ) (hfit : ((2 * r : ℕ) : ℝ) * u0 ≤ u) :
    (∑ j ∈ Finset.range (2 * r + 1),
        (-1 : ℝ) ^ j * gsMoment (gsFillAbove chi u0) j u /
          j.factorial) =
      gsExpAlternatingSum (gsLogScale chi u0) (2 * r) := by
  unfold gsExpAlternatingSum
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have hjr : j ≤ 2 * r := by omega
  have hu00 : 0 ≤ u0 := zero_le_one.trans hu0
  have hjfit : (j : ℝ) * u0 ≤ u := by
    calc
      (j : ℝ) * u0 ≤ ((2 * r : ℕ) : ℝ) * u0 := by
        gcongr
      _ ≤ u := hfit
  rw [gsMoment_gsFillAbove_eq_pow hchi hu0 j hjfit]

/-- The first `2r+2` terms of the filled-kernel moment expansion dominate
the corresponding alternating exponential polynomial. -/
lemma gs_fill_odd_prefix_ge_exp
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi)
    {u0 u : ℝ} (hu0 : 1 ≤ u0) (hu0u : u0 ≤ u) (hu : 1 ≤ u)
    (r : ℕ) (hfit : ((2 * r : ℕ) : ℝ) * u0 ≤ u) :
    gsExpAlternatingSum (gsLogScale chi u0) (2 * r + 1) ≤
      ∑ j ∈ Finset.range (2 * r + 2),
        (-1 : ℝ) ^ j * gsMoment (gsFillAbove chi u0) j u /
          j.factorial := by
  let z : ℝ := gsLogScale chi u0
  let theta : ℝ → ℝ := gsFillAbove chi u0
  have hfill := isGSKernel_gsFillAbove hchi u0
  have hprefix := gs_fill_even_prefix_eq_exp hchi hu0 hu r hfit
  have hM := gsMoment_le_logScale_pow hfill (2 * r + 1) hu
  rw [gsLogScale_gsFillAbove_of_ge hchi hu0 hu0u] at hM
  have hsign : (-1 : ℝ) ^ (2 * r + 1) = -1 := by
    rw [show 2 * r + 1 = 2 * r + 1 by rfl, pow_add, pow_mul]
    norm_num
  have hexp : gsExpAlternatingSum z (2 * r + 1) =
      gsExpAlternatingSum z (2 * r) +
        (-1 : ℝ) ^ (2 * r + 1) * z ^ (2 * r + 1) /
          (2 * r + 1).factorial := by
    unfold gsExpAlternatingSum
    rw [show 2 * r + 1 + 1 = (2 * r + 1) + 1 by omega,
      Finset.sum_range_succ]
  have hactual : (∑ j ∈ Finset.range (2 * r + 2),
        (-1 : ℝ) ^ j * gsMoment theta j u / j.factorial) =
      (∑ j ∈ Finset.range (2 * r + 1),
        (-1 : ℝ) ^ j * gsMoment theta j u / j.factorial) +
        (-1 : ℝ) ^ (2 * r + 1) *
          gsMoment theta (2 * r + 1) u / (2 * r + 1).factorial := by
    rw [show 2 * r + 2 = (2 * r + 1) + 1 by omega,
      Finset.sum_range_succ]
  rw [hexp, hactual]
  change _ + ((-1 : ℝ) ^ (2 * r + 1) * z ^ (2 * r + 1) /
      (2 * r + 1).factorial) ≤
    _ + ((-1 : ℝ) ^ (2 * r + 1) * gsMoment theta (2 * r + 1) u /
      (2 * r + 1).factorial)
  rw [← hprefix]
  rw [hsign]
  dsimp only [z, theta]
  have hfac : (0 : ℝ) < (2 * r + 1).factorial := by positivity
  have hterm := div_le_div_of_nonneg_right (neg_le_neg hM) hfac.le
  norm_num at hterm ⊢
  linarith

/-- Equation (4.14), with the sharper first-order kernel-change loss proved
above: the filled solution is bounded below by the alternating exponential
polynomial through the next odd degree. -/
theorem gs_fill_exp_perturb_lower
    {chi sigma : ℝ → ℝ} (hchi : IsGSKernel chi)
    (hsigma : IsGSSolution chi sigma)
    {u0 u : ℝ} (hu0 : 1 ≤ u0) (hu0u : u0 ≤ u) (hu : 1 ≤ u)
    (r : ℕ) (hfit : ((2 * r : ℕ) : ℝ) * u0 ≤ u) :
    gsExpAlternatingSum (gsLogScale chi u0) (2 * r + 1) -
        (gsLogScale chi u - gsLogScale chi u0) ≤ sigma u := by
  have hodd := gs_fill_odd_perturb_lower hchi hsigma hu0 hu0u hu r
  have hprefix := gs_fill_odd_prefix_ge_exp hchi hu0 hu0u hu r hfit
  exact sub_le_iff_le_add.mpr <| hprefix.trans <|
    (sub_le_iff_le_add.mp hodd)

/-- Paired Bonferroni estimate (equation (4.15) before replacing its positive
moment by a lower product-box bound). -/
theorem gs_fill_paired_perturb_lower
    {chi sigma : ℝ → ℝ} (hchi : IsGSKernel chi)
    (hsigma : IsGSSolution chi sigma)
    {u0 u : ℝ} (hu0 : 1 ≤ u0) (hu0u : u0 ≤ u) (hu : 1 ≤ u)
    (r : ℕ) (hfit : ((2 * r : ℕ) : ℝ) * u0 ≤ u)
    (hz : gsLogScale chi u0 ≤ ((2 * r + 3 : ℕ) : ℝ)) :
    gsExpAlternatingSum (gsLogScale chi u0) (2 * r + 1) +
        gsMoment (gsFillAbove chi u0) (2 * r + 2) u /
            (2 * r + 2).factorial *
          (1 - gsLogScale chi u0 / ((2 * r + 3 : ℕ) : ℝ)) -
        (gsLogScale chi u - gsLogScale chi u0) ≤ sigma u := by
  let z : ℝ := gsLogScale chi u0
  let theta : ℝ → ℝ := gsFillAbove chi u0
  let I2 : ℝ := gsMoment theta (2 * r + 2) u
  let I3 : ℝ := gsMoment theta (2 * r + 3) u
  have hfill := isGSKernel_gsFillAbove hchi u0
  have hodd := gs_fill_odd_perturb_lower hchi hsigma hu0 hu0u hu (r + 1)
  have hprefix := gs_fill_odd_prefix_ge_exp hchi hu0 hu0u hu r hfit
  have hI3 := gsMoment_succ_le_logScale_mul hfill (2 * r + 2) hu
  rw [gsLogScale_gsFillAbove_of_ge hchi hu0 hu0u] at hI3
  have hsign2 : (-1 : ℝ) ^ (2 * r + 2) = 1 := by
    rw [show 2 * r + 2 = 2 * (r + 1) by omega, pow_mul]
    norm_num
  have hsign3 : (-1 : ℝ) ^ (2 * r + 3) = -1 := by
    rw [show 2 * r + 3 = 2 * (r + 1) + 1 by omega, pow_add, pow_mul]
    norm_num
  have hfac2 : (0 : ℝ) < (2 * r + 2).factorial := by positivity
  have hfac3 : (((2 * r + 3).factorial : ℕ) : ℝ) =
      ((2 * r + 3 : ℕ) : ℝ) * (((2 * r + 2).factorial : ℕ) : ℝ) := by
    rw [show 2 * r + 3 = (2 * r + 2) + 1 by omega, Nat.factorial_succ]
    norm_num
  have hcoef : 0 ≤ 1 - z / ((2 * r + 3 : ℕ) : ℝ) := by
    dsimp only [z]
    have hden : (0 : ℝ) < ((2 * r + 3 : ℕ) : ℝ) := by positivity
    rw [sub_nonneg, div_le_one hden]
    exact hz
  have hpair : I2 / (2 * r + 2).factorial *
        (1 - z / ((2 * r + 3 : ℕ) : ℝ)) ≤
      ((-1 : ℝ) ^ (2 * r + 2) * I2 / (2 * r + 2).factorial) +
        ((-1 : ℝ) ^ (2 * r + 3) * I3 / (2 * r + 3).factorial) := by
    rw [hsign2, hsign3, hfac3]
    have hden : (0 : ℝ) < ((2 * r + 3 : ℕ) : ℝ) := by positivity
    have hfac : (0 : ℝ) < (((2 * r + 2).factorial : ℕ) : ℝ) := by positivity
    dsimp only [I2, I3, z, theta] at hI3 ⊢
    calc
      gsMoment (gsFillAbove chi u0) (2 * r + 2) u /
            (((2 * r + 2).factorial : ℕ) : ℝ) *
          (1 - gsLogScale chi u0 / ((2 * r + 3 : ℕ) : ℝ)) =
          gsMoment (gsFillAbove chi u0) (2 * r + 2) u /
              (((2 * r + 2).factorial : ℕ) : ℝ) -
            (gsLogScale chi u0 *
              gsMoment (gsFillAbove chi u0) (2 * r + 2) u) /
              (((2 * r + 3 : ℕ) : ℝ) *
                (((2 * r + 2).factorial : ℕ) : ℝ)) := by field_simp
      _ ≤ gsMoment (gsFillAbove chi u0) (2 * r + 2) u /
              (((2 * r + 2).factorial : ℕ) : ℝ) -
            gsMoment (gsFillAbove chi u0) (2 * r + 3) u /
              (((2 * r + 3 : ℕ) : ℝ) *
                (((2 * r + 2).factorial : ℕ) : ℝ)) := by
          apply sub_le_sub_left
          exact div_le_div_of_nonneg_right hI3 (mul_pos hden hfac).le
      _ = _ := by ring
  have hsum : gsExpAlternatingSum z (2 * r + 1) +
        I2 / (2 * r + 2).factorial *
          (1 - z / ((2 * r + 3 : ℕ) : ℝ)) ≤
      gsAlternatingMomentSum theta (2 * (r + 1) + 1) u := by
    have hactual : gsAlternatingMomentSum theta (2 * (r + 1) + 1) u =
        ((∑ j ∈ Finset.range (2 * r + 2),
            (-1 : ℝ) ^ j * gsMoment theta j u / j.factorial) +
          (-1 : ℝ) ^ (2 * r + 2) * I2 / (2 * r + 2).factorial) +
          (-1 : ℝ) ^ (2 * r + 3) * I3 / (2 * r + 3).factorial := by
      unfold gsAlternatingMomentSum
      rw [show 2 * (r + 1) + 1 + 1 = (2 * r + 3) + 1 by omega,
        Finset.sum_range_succ,
        show 2 * r + 3 = (2 * r + 2) + 1 by omega,
        Finset.sum_range_succ]
    rw [hactual]
    linarith
  dsimp only [z, theta, I2] at hsum ⊢
  linarith

/-- Equation (4.15) with the positive moment replaced by the mass of any
product box `[1,y]^(2r+2)` which fits in the simplex. -/
theorem gs_fill_paired_logScale_lower
    {chi sigma : ℝ → ℝ} (hchi : IsGSKernel chi)
    (hsigma : IsGSSolution chi sigma)
    {u0 y u : ℝ} (hu0 : 1 ≤ u0) (hu0u : u0 ≤ u) (hu : 1 ≤ u)
    (hy : 1 ≤ y) (r : ℕ)
    (hfit : ((2 * r : ℕ) : ℝ) * u0 ≤ u)
    (hyfit : ((2 * r + 2 : ℕ) : ℝ) * y ≤ u)
    (hz : gsLogScale chi u0 ≤ ((2 * r + 3 : ℕ) : ℝ)) :
    gsExpAlternatingSum (gsLogScale chi u0) (2 * r + 1) +
        gsLogScale (gsFillAbove chi u0) y ^ (2 * r + 2) /
            (2 * r + 2).factorial *
          (1 - gsLogScale chi u0 / ((2 * r + 3 : ℕ) : ℝ)) -
        (gsLogScale chi u - gsLogScale chi u0) ≤ sigma u := by
  have hbase := gs_fill_paired_perturb_lower hchi hsigma hu0 hu0u hu r hfit hz
  have hfill := isGSKernel_gsFillAbove hchi u0
  have hmoment := gsLogScale_pow_le_gsMoment hfill hy (2 * r + 2) hyfit
  have hden : (0 : ℝ) < ((2 * r + 3 : ℕ) : ℝ) := by positivity
  have hcoef : 0 ≤
      1 - gsLogScale chi u0 / ((2 * r + 3 : ℕ) : ℝ) := by
    rw [sub_nonneg, div_le_one hden]
    exact hz
  have hscaled := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hmoment
      (show (0 : ℝ) ≤ (2 * r + 2).factorial by positivity)) hcoef
  linarith

/-- A sharp elementary upper bound on the first nonconstant
method-of-steps interval. -/
lemma dickmanRho_le_refined_two_three
    {e : ℝ} (he2 : 2 ≤ e) (he3 : e ≤ 3) :
    dickmanRho e ≤
      1 - Real.log e + Real.log (e - 1) ^ 2 / 4 +
        Real.log (e - 1) ^ 3 / 12 := by
  let F : ℝ → ℝ := fun t ↦
    Real.log (t - 1) ^ 2 / 4 + Real.log (t - 1) ^ 3 / 12
  let f : ℝ → ℝ := fun t ↦ Real.log (t - 1) / t
  let g : ℝ → ℝ := fun t ↦
    Real.log (t - 1) / (2 * (t - 1)) +
      Real.log (t - 1) ^ 2 / (4 * (t - 1))
  have hinterval : (2 : ℝ) ≤ e := he2
  have hFcont : ContinuousOn F (Icc (2 : ℝ) e) := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    dsimp only [F]
    fun_prop (disch := (norm_num at ht ⊢; linarith))
  have hFderiv : ∀ t ∈ Ioo (2 : ℝ) e, HasDerivAt F (g t) t := by
    intro t ht
    rcases ht with ⟨htlow, hthigh⟩
    have hne : t - 1 ≠ 0 := by linarith
    have hz : HasDerivAt (fun x : ℝ ↦ Real.log (x - 1)) (1 / (t - 1)) t := by
      simpa only [id_eq, one_div] using
        (((hasDerivAt_id t).sub_const 1).log hne)
    dsimp only [F, g]
    convert ((hz.pow 2).div_const 4).add ((hz.pow 3).div_const 12) using 1 <;>
      norm_num [Function.id_def]
    all_goals first | rfl | (field_simp [hne] <;> ring)
  have hgInt : IntervalIntegrable g volume 2 e := by
    have hc : ContinuousOn g (Icc (2 : ℝ) e) := by
      intro t ht
      apply ContinuousAt.continuousWithinAt
      dsimp only [g]
      fun_prop (disch := (norm_num at ht ⊢; linarith [ht.1]))
    exact hc.intervalIntegrable_of_Icc hinterval
  have hfInt : IntervalIntegrable f volume 2 e := by
    have hc : ContinuousOn f (Icc (2 : ℝ) e) := by
      intro t ht
      apply ContinuousAt.continuousWithinAt
      dsimp only [f]
      fun_prop (disch := (norm_num at ht ⊢; linarith))
    exact hc.intervalIntegrable_of_Icc hinterval
  have hpoint : ∀ t ∈ Icc (2 : ℝ) e, f t ≤ g t := by
    intro t ht
    rcases ht with ⟨htlow, hthigh⟩
    have ht0 : 0 < t := by linarith
    have htm : 0 < t - 1 := by linarith
    have hx0 : 0 ≤ t - 2 := by linarith
    have hlog0 : 0 ≤ Real.log (t - 1) :=
      Real.log_nonneg (by linarith)
    have hlogLower := Real.le_log_one_add_of_nonneg hx0
    have harg : 1 + (t - 2) = t - 1 := by ring
    rw [harg] at hlogLower
    have hbase : 2 * (t - 2) ≤ Real.log (t - 1) * t := by
      have htden : 0 < (t - 2) + 2 := by linarith
      rw [div_le_iff₀ htden] at hlogLower
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hbase hlog0
    dsimp only [f, g]
    rw [div_le_iff₀ ht0]
    rw [show (Real.log (t - 1) / (2 * (t - 1)) +
        Real.log (t - 1) ^ 2 / (4 * (t - 1))) * t =
      (2 * Real.log (t - 1) * t + Real.log (t - 1) ^ 2 * t) /
        (4 * (t - 1)) by field_simp; ring]
    rw [le_div_iff₀ (by positivity : 0 < 4 * (t - 1))]
    nlinarith
  have hint := intervalIntegral.integral_mono_on hinterval hfInt hgInt hpoint
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hinterval hFcont hFderiv hgInt
  have hFeval : (∫ t : ℝ in 2..e, g t) =
      Real.log (e - 1) ^ 2 / 4 + Real.log (e - 1) ^ 3 / 12 := by
    rw [hfund]
    dsimp only [F]
    norm_num
  rw [hFeval] at hint
  have hrho := dickmanRho_eq_one_sub_log_add_shifted he2 he3
  dsimp only [f] at hint
  rw [hrho]
  linarith

/-- On the first method-of-steps interval, the Dickman correction integral
is bounded by the cubic which occurs in the degree-three alternating
exponential polynomial. -/
lemma dickmanRho_le_cubic_two_three
    {e : ℝ} (he2 : 2 ≤ e) (he3 : e ≤ 3) :
    dickmanRho e ≤
      1 - Real.log e + Real.log (e - 1) ^ 2 / 2 -
        Real.log (e - 1) ^ 3 / 6 := by
  have hrho := dickmanRho_le_refined_two_three he2 he3
  have hz0 : 0 ≤ Real.log (e - 1) :=
    Real.log_nonneg (by linarith)
  have hz1 : Real.log (e - 1) ≤ 1 := by
    have hlog := Real.log_le_sub_one_of_pos (by linarith : 0 < e - 1)
    nlinarith
  have hpoly : Real.log (e - 1) ^ 2 / 4 +
        Real.log (e - 1) ^ 3 / 12 ≤
      Real.log (e - 1) ^ 2 / 2 - Real.log (e - 1) ^ 3 / 6 := by
    have := mul_nonneg (sq_nonneg (Real.log (e - 1)))
      (sub_nonneg.mpr hz1)
    nlinarith
  linarith

lemma log_two_lt_347_div_500 :
    Real.log 2 < (347 / 500 : ℝ) := by
  have h := log_le_logAtanhUpper_of_eq
    (q := (2 : ℝ)) (x := (1 / 3 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 7
  norm_num [logAtanhUpper, logAtanhPartial] at h ⊢
  linarith

lemma log_four_lt_two :
    Real.log 4 < (2 : ℝ) := by
  rw [show (4 : ℝ) = 2 * 2 by norm_num,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num)]
  nlinarith [log_two_lt_347_div_500]

lemma log_two_lt_13863_div_20000 :
    Real.log 2 < (13863 / 20000 : ℝ) := by
  have h := log_le_logAtanhUpper_of_eq
    (q := (2 : ℝ)) (x := (1 / 3 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 9
  norm_num [logAtanhUpper, logAtanhPartial] at h ⊢
  linarith

lemma log_three_gt_109861_div_100000 :
    (109861 / 100000 : ℝ) < Real.log 3 := by
  have h := logAtanhPartial_le_log_of_eq
    (q := (3 : ℝ)) (x := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 10
  norm_num [logAtanhPartial] at h ⊢
  linarith

lemma log_three_lt_eleven_tenths :
    Real.log 3 < (11 / 10 : ℝ) := by
  have h := log_le_logAtanhUpper_of_eq
    (q := (3 : ℝ)) (x := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 8
  norm_num [logAtanhUpper, logAtanhPartial] at h ⊢
  linarith

lemma log_six_lt_two :
    Real.log 6 < (2 : ℝ) := by
  rw [show (6 : ℝ) = 2 * 3 by norm_num,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num)]
  nlinarith [log_two_lt_347_div_500, log_three_lt_eleven_tenths]

lemma log_six_lt_nine_fifths :
    Real.log 6 < (9 / 5 : ℝ) := by
  rw [show (6 : ℝ) = 2 * 3 by norm_num,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num)]
  nlinarith [log_two_lt_347_div_500, log_three_lt_eleven_tenths]

lemma log_three_gt_5493_div_5000 :
    (5493 / 5000 : ℝ) < Real.log 3 := by
  have h := logAtanhPartial_le_log_of_eq
    (q := (3 : ℝ)) (x := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 9
  norm_num [logAtanhPartial] at h ⊢
  linarith

lemma dickmanRho_three_lt_one_twentieth :
    dickmanRho 3 < (1 / 20 : ℝ) := by
  have h := dickmanRho_le_refined_two_three
    (e := (3 : ℝ)) (by norm_num) (by norm_num)
  have h2 := log_two_lt_347_div_500
  have h3 := log_three_gt_5493_div_5000
  have h20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h2sq := mul_self_le_mul_self h20 h2.le
  have h2cube := mul_le_mul_of_nonneg_left h2sq h20
  norm_num at h ⊢
  nlinarith [h2sq, h2cube]

lemma dickmanRho_three_lt_493_div_10000 :
    dickmanRho 3 < (493 / 10000 : ℝ) := by
  have h := dickmanRho_le_refined_two_three
    (e := (3 : ℝ)) (by norm_num) (by norm_num)
  have h2 := log_two_lt_13863_div_20000
  have h3 := log_three_gt_109861_div_100000
  have h20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h2sq : Real.log 2 ^ 2 ≤ (13863 / 20000 : ℝ) ^ 2 :=
    pow_le_pow_left₀ h20 h2.le 2
  have h2cube : Real.log 2 ^ 3 ≤ (13863 / 20000 : ℝ) ^ 3 :=
    pow_le_pow_left₀ h20 h2.le 3
  norm_num at h ⊢
  nlinarith

/-- The delay equation and monotonicity give the elementary one-step bound
`rho(e) ≤ rho(e-1)/e`.  This is the form used in the numerical part of
Proposition 6.1. -/
lemma dickmanRho_le_previous_div
    {e : ℝ} (he1 : 1 ≤ e) :
    dickmanRho e ≤ dickmanRho (e - 1) / e := by
  have he0 : 0 < e := zero_lt_one.trans_le he1
  have hem0 : 0 ≤ e - 1 := sub_nonneg.mpr he1
  have hint : IntervalIntegrable dickmanRho volume (e - 1) e :=
    intervalIntegrable_dickmanRho_of_nonneg hem0 he0.le
  have hconst : IntervalIntegrable (fun _t : ℝ ↦ dickmanRho (e - 1))
      volume (e - 1) e := intervalIntegrable_const
  have hmono : (∫ t : ℝ in (e - 1)..e, dickmanRho t) ≤
      ∫ _t : ℝ in (e - 1)..e, dickmanRho (e - 1) := by
    apply intervalIntegral.integral_mono_on (by linarith) hint hconst
    intro t ht
    exact antitoneOn_dickmanRho_Ici_zero hem0
      (hem0.trans ht.1) ht.1
  have hdelay := dickmanRho_profile.2.2.2.2 e he1
  rw [hdelay] at hmono
  simp only [intervalIntegral.integral_const, sub_sub_cancel] at hmono
  rw [le_div_iff₀ he0]
  simpa [mul_comm] using hmono

/-- Scalar form of (4.14) for `2 ≤ e ≤ 3`. -/
lemma section61_scalar_two_three
    {e a : ℝ} (he2 : 2 ≤ e) (he3 : e ≤ 3)
    (haLower : e - 1 ≤ a) (haUpper : a ≤ e) :
    dickmanRho e ≤
      gsExpAlternatingSum (Real.log a) 3 -
        (Real.log e - Real.log a) := by
  have haPos : 0 < a := by linarith
  have hePos : 0 < e := by linarith
  have heSubPos : 0 < e - 1 := by linarith
  have hw0 : 0 ≤ Real.log (e - 1) :=
    Real.log_nonneg (by linarith)
  have hz0 : 0 ≤ Real.log a := Real.log_nonneg (by linarith)
  have hwz : Real.log (e - 1) ≤ Real.log a :=
    Real.strictMonoOn_log.monotoneOn heSubPos haPos haLower
  have hz2 : Real.log a ≤ 2 := by
    have hlog := Real.log_le_sub_one_of_pos haPos
    linarith
  have hw2 : Real.log (e - 1) ≤ 2 := hwz.trans hz2
  have hcross : Real.log a * Real.log (e - 1) ≤
      Real.log a + Real.log (e - 1) := by
    by_cases hz1 : Real.log a ≤ 1
    · nlinarith [mul_le_mul_of_nonneg_right hz1 hw0]
    · have hwle : Real.log (e - 1) ≤ Real.log a := hwz
      have hmul := mul_le_mul_of_nonneg_left hw2 hz0
      nlinarith
  have hgmono : Real.log (e - 1) ^ 2 / 2 -
        Real.log (e - 1) ^ 3 / 6 ≤
      Real.log a ^ 2 / 2 - Real.log a ^ 3 / 6 := by
    have hsqz := mul_nonneg hz0 (sub_nonneg.mpr hz2)
    have hsqw := mul_nonneg hw0 (sub_nonneg.mpr hw2)
    have hdiff := sub_nonneg.mpr hwz
    nlinarith [mul_nonneg hdiff
      (sub_nonneg.mpr (by nlinarith [hcross]))]
  have hrho := dickmanRho_le_cubic_two_three he2 he3
  norm_num [gsExpAlternatingSum, Finset.sum_range_succ]
  linarith

/-- The scalar lower model obtained from (4.15) in the range where the even
degree is two.  The product logarithm is written additively to make its
derivative transparent. -/
def gsSection61LowModel (e : ℝ) : ℝ :=
  let w := Real.log (e - 1)
  let q := Real.log e + Real.log (e - 1) - Real.log 4
  1 - Real.log e + w ^ 2 / 2 - w ^ 3 / 6 +
    q ^ 4 / 24 * (1 - Real.log e / 5)

/-- The nonconstant part of the degree-five alternating exponential
polynomial. -/
def gsTaylorFiveTail (z : ℝ) : ℝ :=
  z ^ 2 / 2 - z ^ 3 / 6 + z ^ 4 / 24 - z ^ 5 / 120

lemma hasDerivAt_gsTaylorFiveTail (z : ℝ) :
    HasDerivAt gsTaylorFiveTail
      (z - z ^ 2 / 2 + z ^ 3 / 6 - z ^ 4 / 24) z := by
  have h := (((((hasDerivAt_id z).pow 2).div_const 2).sub
    (((hasDerivAt_id z).pow 3).div_const 6)).add
      (((hasDerivAt_id z).pow 4).div_const 24)).sub
        (((hasDerivAt_id z).pow 5).div_const 120)
  change HasDerivAt
    ((((fun x : ℝ ↦ x ^ 2 / 2) - fun x : ℝ ↦ x ^ 3 / 6) +
      fun x : ℝ ↦ x ^ 4 / 24) - fun x : ℝ ↦ x ^ 5 / 120)
      (z - z ^ 2 / 2 + z ^ 3 / 6 - z ^ 4 / 24) z
  apply h.congr_deriv
  norm_num [Function.id_def]
  ring

lemma monotoneOn_gsTaylorFiveTail :
    MonotoneOn gsTaylorFiveTail (Icc (0 : ℝ) 2) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 2)
  · intro z _
    exact (hasDerivAt_gsTaylorFiveTail z).continuousAt.continuousWithinAt
  · intro z _
    exact (hasDerivAt_gsTaylorFiveTail z).differentiableAt.differentiableWithinAt
  · intro z hz
    rw [(hasDerivAt_gsTaylorFiveTail z).deriv]
    rw [show z - z ^ 2 / 2 + z ^ 3 / 6 - z ^ 4 / 24 =
        z * ((1 - z / 2) + z ^ 2 * (4 - z) / 24) by ring]
    have hzI : z ∈ Icc (0 : ℝ) 2 := by
      rw [interior_Icc] at hz
      exact ⟨hz.1.le, hz.2.le⟩
    apply mul_nonneg hzI.1
    apply add_nonneg
    · linarith [hzI.2]
    · exact div_nonneg
        (mul_nonneg (sq_nonneg z) (by linarith [hzI.2])) (by norm_num)

lemma gsExpAlternatingSum_five_lower
    {w : ℝ} (hw0 : 0 ≤ w) (hw2 : w ≤ 2) :
    Real.exp (-w) - w ^ 6 / 720 + w ^ 7 / 5040 - w ^ 8 / 40320 +
        w ^ 9 / 362880 - 2 * w ^ 10 / 3628800 ≤
      gsExpAlternatingSum w 5 := by
  have h := Complex.exp_bound' (x := ((-w : ℝ) : ℂ)) (n := 10) (by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg hw0]
    norm_num
    linarith)
  have hsum : (∑ m ∈ Finset.range 10,
      (((-w : ℝ) : ℂ) ^ m / m.factorial)) =
      ((∑ m ∈ Finset.range 10, (-w) ^ m / m.factorial : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [← Complex.ofReal_exp, hsum, ← Complex.ofReal_sub] at h
  have hreal : |Real.exp (-w) -
      ∑ m ∈ Finset.range 10, (-w) ^ m / m.factorial| ≤
      w ^ 10 / (10 : ℕ).factorial * 2 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg hw0] using h
  have hupper := (le_abs_self
    (Real.exp (-w) - ∑ m ∈ Finset.range 10,
      (-w) ^ m / m.factorial)).trans hreal
  norm_num [gsExpAlternatingSum, Finset.sum_range_succ] at hupper ⊢
  nlinarith

def gsTaylorFiveErrorLower (w : ℝ) : ℝ :=
  -w ^ 6 / 720 + w ^ 7 / 5040 - w ^ 8 / 40320 +
    w ^ 9 / 362880 - 2 * w ^ 10 / 3628800

lemma hasDerivAt_gsTaylorFiveErrorLower (w : ℝ) :
    HasDerivAt gsTaylorFiveErrorLower
      (-w ^ 5 / 120 + w ^ 6 / 720 - w ^ 7 / 5040 +
        w ^ 8 / 40320 - w ^ 9 / 181440) w := by
  have h6 := ((hasDerivAt_id w).pow 6).neg.div_const 720
  have h7 := ((hasDerivAt_id w).pow 7).div_const 5040
  have h8 := ((hasDerivAt_id w).pow 8).div_const 40320
  have h9 := ((hasDerivAt_id w).pow 9).div_const 362880
  have h10 := ((hasDerivAt_const w (2 : ℝ)).mul
    ((hasDerivAt_id w).pow 10)).div_const 3628800
  have h := (((h6.add h7).sub h8).add h9).sub h10
  change HasDerivAt
    (((((fun x : ℝ ↦ -x ^ 6 / 720) + fun x : ℝ ↦ x ^ 7 / 5040) -
      fun x : ℝ ↦ x ^ 8 / 40320) + fun x : ℝ ↦ x ^ 9 / 362880) -
        fun x : ℝ ↦ 2 * x ^ 10 / 3628800)
      (-w ^ 5 / 120 + w ^ 6 / 720 - w ^ 7 / 5040 +
        w ^ 8 / 40320 - w ^ 9 / 181440) w
  apply h.congr_deriv
  norm_num [Function.id_def]
  ring

lemma antitoneOn_gsTaylorFiveErrorLower :
    AntitoneOn gsTaylorFiveErrorLower (Icc (0 : ℝ) 2) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) 2)
  · intro w _
    exact (hasDerivAt_gsTaylorFiveErrorLower w).continuousAt.continuousWithinAt
  · intro w _
    exact (hasDerivAt_gsTaylorFiveErrorLower w).differentiableAt.differentiableWithinAt
  · intro w hw
    rw [(hasDerivAt_gsTaylorFiveErrorLower w).deriv]
    rw [show -w ^ 5 / 120 + w ^ 6 / 720 - w ^ 7 / 5040 +
          w ^ 8 / 40320 - w ^ 9 / 181440 =
        -(w ^ 5 / 120) *
          ((1 - w / 6) + w ^ 2 * (8 - w) / 336 + w ^ 4 / 1512) by
      ring]
    have hwI : w ∈ Icc (0 : ℝ) 2 := by
      rw [interior_Icc] at hw
      exact ⟨hw.1.le, hw.2.le⟩
    have hbracket : 0 ≤
        (1 - w / 6) + w ^ 2 * (8 - w) / 336 + w ^ 4 / 1512 := by
      have h1 : 0 ≤ 1 - w / 6 := by linarith [hwI.2]
      have h2 : 0 ≤ w ^ 2 * (8 - w) / 336 :=
        div_nonneg (mul_nonneg (sq_nonneg w) (by linarith [hwI.2])) (by norm_num)
      have h3 : 0 ≤ w ^ 4 / 1512 := by positivity
      linarith
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (div_nonneg (pow_nonneg hwI.1 5) (by norm_num))) hbracket

lemma log_one_add_le_cubic {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ x - x ^ 2 / 2 + x ^ 3 / 3 := by
  let f : ℝ → ℝ := fun z ↦
    z - z ^ 2 / 2 + z ^ 3 / 3 - Real.log (1 + z)
  have hfderiv : ∀ z ∈ Icc (0 : ℝ) x,
      HasDerivAt f (z ^ 3 / (1 + z)) z := by
    intro z hz
    have hden : 1 + z ≠ 0 := by linarith [hz.1]
    have hlog : HasDerivAt (fun t : ℝ ↦ Real.log (1 + t))
        (1 / (1 + z)) z := by
      have hzden : z + 1 ≠ 0 := by linarith [hz.1]
      simpa only [Function.id_def, add_comm, one_div] using
        (((hasDerivAt_id z).add_const 1).log hzden)
    have hpoly := (((hasDerivAt_id z).sub
      (((hasDerivAt_id z).pow 2).div_const 2)).add
        (((hasDerivAt_id z).pow 3).div_const 3)).sub hlog
    dsimp only [f]
    apply hpoly.congr_deriv
    norm_num [Function.id_def]
    field_simp [hden]
    ring
  have hcont : ContinuousOn f (Icc (0 : ℝ) x) := by
    intro z hz
    exact (hfderiv z hz).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (interior (Icc (0 : ℝ) x)) := by
    intro z hz
    have hzI : z ∈ Icc (0 : ℝ) x := by
      rw [interior_Icc] at hz
      exact ⟨hz.1.le, hz.2.le⟩
    exact (hfderiv z hzI).differentiableAt.differentiableWithinAt
  have hnonneg : ∀ z ∈ interior (Icc (0 : ℝ) x), 0 ≤ deriv f z := by
    intro z hz
    have hzI : z ∈ Icc (0 : ℝ) x := by
      rw [interior_Icc] at hz
      exact ⟨hz.1.le, hz.2.le⟩
    rw [(hfderiv z hzI).deriv]
    exact div_nonneg (pow_nonneg hzI.1 3) (by linarith [hzI.1])
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) x)
    hcont hdiff hnonneg
  have hvalue := hmono (by exact ⟨le_rfl, hx⟩) ⟨hx, le_rfl⟩ hx
  dsimp only [f] at hvalue
  norm_num at hvalue
  linarith

/-- The degree-five paired scalar model used for `4 ≤ e ≤ 6`. -/
def gsSection61MidModel (e : ℝ) : ℝ :=
  let w := Real.log (e - 1)
  let q := Real.log e + Real.log (e - 1) - Real.log 6
  1 - Real.log e + gsTaylorFiveTail w +
    q ^ 6 / 720 * (1 - Real.log e / 7)

def gsSection61LowModelDeriv (e : ℝ) : ℝ :=
  let w := Real.log (e - 1)
  let q := Real.log e + Real.log (e - 1) - Real.log 4
  (-1 / e + (w - w ^ 2 / 2) / (e - 1) +
    q ^ 3 / 6 * (1 / e + 1 / (e - 1)) * (1 - Real.log e / 5) -
      q ^ 4 / (120 * e))

lemma hasDerivAt_gsSection61LowModel
    {e : ℝ} (he : 1 < e) :
    HasDerivAt gsSection61LowModel (gsSection61LowModelDeriv e) e := by
  have he0 : e ≠ 0 := by linarith
  have hem0 : e - 1 ≠ 0 := by linarith
  have hE : HasDerivAt Real.log (1 / e) e := by
    simpa only [one_div] using Real.hasDerivAt_log he0
  have hW : HasDerivAt (fun x : ℝ ↦ Real.log (x - 1)) (1 / (e - 1)) e := by
    simpa only [id_eq, one_div] using
      (((hasDerivAt_id e).sub_const 1).log hem0)
  have hQ : HasDerivAt
      (fun x : ℝ ↦ Real.log x + Real.log (x - 1) - Real.log 4)
      (1 / e + 1 / (e - 1)) e := by
    convert (hE.add hW).sub_const (Real.log 4) using 1 <;> try rfl
  have hOneSub : HasDerivAt (fun x : ℝ ↦ 1 - Real.log x / 5)
      (-(1 / e) / 5) e := by
    convert (hasDerivAt_const e 1).sub (hE.div_const 5) using 1 <;>
      norm_num [Function.id_def]
    all_goals first | rfl | ring
  have hMain : HasDerivAt
      (fun x : ℝ ↦
        1 - Real.log x + Real.log (x - 1) ^ 2 / 2 -
          Real.log (x - 1) ^ 3 / 6)
      (-1 / e + (Real.log (e - 1) - Real.log (e - 1) ^ 2 / 2) /
        (e - 1)) e := by
    have hraw := (((hasDerivAt_const e 1).sub hE).add
      ((hW.pow 2).div_const 2)).sub ((hW.pow 3).div_const 6)
    convert hraw using 1 <;> norm_num [Function.id_def]
    all_goals first | rfl | (field_simp [hem0] <;> ring)
  have hBonus : HasDerivAt
      (fun x : ℝ ↦
        (Real.log x + Real.log (x - 1) - Real.log 4) ^ 4 / 24 *
          (1 - Real.log x / 5))
      ((Real.log e + Real.log (e - 1) - Real.log 4) ^ 3 / 6 *
          (1 / e + 1 / (e - 1)) * (1 - Real.log e / 5) -
        (Real.log e + Real.log (e - 1) - Real.log 4) ^ 4 /
          (120 * e)) e := by
    have hraw := ((hQ.pow 4).div_const 24).mul hOneSub
    convert hraw using 1 <;> norm_num [Function.id_def]
    all_goals first | rfl | (field_simp [he0, hem0] <;> ring)
  dsimp only [gsSection61LowModel, gsSection61LowModelDeriv]
  convert hMain.add hBonus using 1 <;> try rfl
  ring

lemma gsSection61LowModel_antitone_piece
    {lo hi Q : ℝ} (hlo : 3 ≤ lo) (hlohi : lo ≤ hi)
    (hhi : hi ≤ 5)
    (hqUpper : ∀ e ∈ Icc lo hi,
      Real.log e + Real.log (e - 1) - Real.log 4 ≤ Q)
    (hQ0 : 0 ≤ Q)
    (hcert : 1 - lo / 2 + Q ^ 3 * (2 * hi - 1) * (2 / 15) ≤ 0) :
    AntitoneOn gsSection61LowModel (Icc lo hi) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc lo hi)
  · intro e heI
    have he1 : 1 < e := by linarith [heI.1]
    exact (hasDerivAt_gsSection61LowModel he1).continuousAt.continuousWithinAt
  · intro e he
    have heI : e ∈ Icc lo hi := by
      rw [interior_Icc] at he
      exact ⟨he.1.le, he.2.le⟩
    have he1 : 1 < e := by linarith [heI.1]
    exact (hasDerivAt_gsSection61LowModel he1).differentiableAt.differentiableWithinAt
  · intro e he
    have heI : e ∈ Icc lo hi := by
      rw [interior_Icc] at he
      exact ⟨he.1.le, he.2.le⟩
    have he1 : 1 < e := by linarith [heI.1]
    have hder := (hasDerivAt_gsSection61LowModel he1).deriv
    rw [hder]
    let q : ℝ := Real.log e + Real.log (e - 1) - Real.log 4
    let w : ℝ := Real.log (e - 1)
    have he0 : 0 < e := by linarith
    have hem0 : 0 < e - 1 := by linarith
    have hq0 : 0 ≤ q := by
      have harg : (1 : ℝ) ≤ e * (e - 1) / 4 := by nlinarith [heI.1]
      have hlog0 := Real.log_nonneg harg
      have hprod : Real.log (e * (e - 1) / 4) = q := by
        dsimp only [q]
        rw [Real.log_div (mul_ne_zero he0.ne' hem0.ne') (by norm_num),
          Real.log_mul he0.ne' hem0.ne']
      rwa [hprod] at hlog0
    have hqQ : q ≤ Q := hqUpper e heI
    have hq2 : q ^ 2 ≤ Q ^ 2 := by nlinarith
    have hq3 : q ^ 3 ≤ Q ^ 3 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hqQ)
        (add_nonneg (sq_nonneg q) (add_nonneg (mul_nonneg hq0 hQ0) (sq_nonneg Q)))]
    have hlogOne : 1 ≤ Real.log e := by
      have h3pos : (0 : ℝ) < 3 := by norm_num
      have hlog := Real.strictMonoOn_log.monotoneOn h3pos he0 (hlo.trans heI.1)
      have hlog3 := log_three_gt_5493_div_5000
      linarith
    have hcoef : 0 ≤ 1 - Real.log e / 5 := by
      have hlog := Real.log_le_sub_one_of_pos he0
      nlinarith [heI.2, hhi]
    have hcoefUpper : 1 - Real.log e / 5 ≤ 4 / 5 := by linarith
    have hwSquare : w - w ^ 2 / 2 ≤ 1 / 2 := by
      nlinarith [sq_nonneg (w - 1)]
    have hpos : 0 < e * (e - 1) := mul_pos he0 hem0
    have hqBonus : q ^ 3 * (2 * e - 1) * (1 - Real.log e / 5) ≤
        Q ^ 3 * (2 * hi - 1) * (4 / 5) := by
      have htwopos : 0 ≤ 2 * e - 1 := by linarith
      have htwoupper : 2 * e - 1 ≤ 2 * hi - 1 := by linarith [heI.2]
      have hQ3 : 0 ≤ Q ^ 3 := by positivity
      have hhiTwo : 0 ≤ 2 * hi - 1 := by linarith
      calc
        q ^ 3 * (2 * e - 1) * (1 - Real.log e / 5) ≤
            Q ^ 3 * (2 * e - 1) * (1 - Real.log e / 5) := by gcongr
        _ ≤ Q ^ 3 * (2 * hi - 1) * (1 - Real.log e / 5) := by gcongr
        _ ≤ Q ^ 3 * (2 * hi - 1) * (4 / 5) := by gcongr
    have hnum : -(e - 1) + e * (w - w ^ 2 / 2) +
          q ^ 3 / 6 * (2 * e - 1) * (1 - Real.log e / 5) ≤ 0 := by
      have hmain : -(e - 1) + e * (w - w ^ 2 / 2) ≤ 1 - lo / 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hwSquare he0.le, heI.1]
      nlinarith [hcert, hqBonus]
    have hq4 : 0 ≤ q ^ 4 := by positivity
    dsimp only [gsSection61LowModelDeriv, q, w]
    rw [show -1 / e +
          (Real.log (e - 1) - Real.log (e - 1) ^ 2 / 2) / (e - 1) +
          (Real.log e + Real.log (e - 1) - Real.log 4) ^ 3 / 6 *
              (1 / e + 1 / (e - 1)) * (1 - Real.log e / 5) -
          (Real.log e + Real.log (e - 1) - Real.log 4) ^ 4 / (120 * e) =
        (-(e - 1) + e * (w - w ^ 2 / 2) +
            q ^ 3 / 6 * (2 * e - 1) * (1 - Real.log e / 5)) /
              (e * (e - 1)) - q ^ 4 / (120 * e) by
      dsimp only [q, w]
      field_simp [he0.ne', hem0.ne']
      ring]
    have hfirst :
        (-(e - 1) + e * (w - w ^ 2 / 2) +
            q ^ 3 / 6 * (2 * e - 1) * (1 - Real.log e / 5)) /
              (e * (e - 1)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hnum hpos.le
    have hlast : 0 ≤ q ^ 4 / (120 * e) := by positivity
    linarith

lemma log_thirtyfive_sixteenths_bounds :
    (7827 / 10000 : ℝ) < Real.log (35 / 16) ∧
      Real.log (35 / 16) < (79 / 100 : ℝ) := by
  have hlo := logAtanhPartial_le_log_of_eq
    (q := (35 / 16 : ℝ)) (x := (19 / 51 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 9
  have hhi := log_le_logAtanhUpper_of_eq
    (q := (35 / 16 : ℝ)) (x := (19 / 51 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 9
  constructor <;>
    norm_num [logAtanhPartial, logAtanhUpper] at hlo hhi ⊢ <;> linarith

lemma log_ninehundredninetynine_fourhundred_lt :
    Real.log (999 / 400) < (23 / 25 : ℝ) := by
  have h := log_le_logAtanhUpper_of_eq
    (q := (999 / 400 : ℝ)) (x := (599 / 1399 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 11
  norm_num [logAtanhPartial, logAtanhUpper] at h ⊢
  linarith

lemma log_onehundredthirtythree_fifty_bounds :
    (9783 / 10000 : ℝ) < Real.log (133 / 50) ∧
      Real.log (133 / 50) < (49 / 50 : ℝ) := by
  have hlo := logAtanhPartial_le_log_of_eq
    (q := (133 / 50 : ℝ)) (x := (83 / 183 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 12
  have hhi := log_le_logAtanhUpper_of_eq
    (q := (133 / 50 : ℝ)) (x := (83 / 183 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 12
  constructor <;>
    norm_num [logAtanhPartial, logAtanhUpper] at hlo hhi ⊢ <;> linarith

lemma log_five_halves_gt_4581_div_5000 :
    (4581 / 5000 : ℝ) < Real.log (5 / 2) := by
  have h := logAtanhPartial_le_log_of_eq
    (q := (5 / 2 : ℝ)) (x := (3 / 7 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 10
  norm_num [logAtanhPartial] at h ⊢
  linarith

lemma log_seven_halves_lt_1566_div_1250 :
    Real.log (7 / 2) < (1566 / 1250 : ℝ) := by
  have h := log_le_logAtanhUpper_of_eq
    (q := (7 / 2 : ℝ)) (x := (5 / 9 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 15
  norm_num [logAtanhPartial, logAtanhUpper] at h ⊢
  linarith

lemma log_fourteen_fifths_gt_1287_div_1250 :
    (1287 / 1250 : ℝ) < Real.log (14 / 5) := by
  have h := logAtanhPartial_le_log_of_eq
    (q := (14 / 5 : ℝ)) (x := (9 / 19 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 13
  norm_num [logAtanhPartial] at h ⊢
  linarith

lemma log_nineteen_fifths_lt_13351_div_10000 :
    Real.log (19 / 5) < (13351 / 10000 : ℝ) := by
  have h := log_le_logAtanhUpper_of_eq
    (q := (19 / 5 : ℝ)) (x := (7 / 12 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 18
  norm_num [logAtanhPartial, logAtanhUpper] at h ⊢
  linarith

lemma log_nine_fifths_lt_147_div_250 :
    Real.log (9 / 5) < (147 / 250 : ℝ) := by
  have h := log_le_logAtanhUpper_of_eq
    (q := (9 / 5 : ℝ)) (x := (2 / 7 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 7
  norm_num [logAtanhPartial, logAtanhUpper] at h ⊢
  linarith

lemma log_seventyseven_twenty_lt_1349_div_1000 :
    Real.log (77 / 20) < (1349 / 1000 : ℝ) := by
  have h := log_le_logAtanhUpper_of_eq
    (q := (77 / 20 : ℝ)) (x := (57 / 97 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 18
  norm_num [logAtanhPartial, logAtanhUpper] at h ⊢
  linarith

lemma log_fiftyseven_twenty_gt_1047_div_1000 :
    (1047 / 1000 : ℝ) < Real.log (57 / 20) := by
  have h := logAtanhPartial_le_log_of_eq
    (q := (57 / 20 : ℝ)) (x := (37 / 77 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 10
  norm_num [logAtanhPartial] at h ⊢
  linarith

lemma one_lt_log_fourthousandeighthundredninetynine_sixteenhundred :
    (1 : ℝ) < Real.log (4389 / 1600) := by
  have h := logAtanhPartial_le_log_of_eq
    (q := (4389 / 1600 : ℝ)) (x := (2789 / 5989 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 9
  norm_num [logAtanhPartial] at h ⊢
  linarith

lemma log_thirtynine_ten_lt_1361_div_1000 :
    Real.log (39 / 10) < (1361 / 1000 : ℝ) := by
  have h := log_le_logAtanhUpper_of_eq
    (q := (39 / 10 : ℝ)) (x := (29 / 49 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 19
  norm_num [logAtanhPartial, logAtanhUpper] at h ⊢
  linarith

lemma log_twentynine_ten_gt_1064_div_1000 :
    (1064 / 1000 : ℝ) < Real.log (29 / 10) := by
  have h := logAtanhPartial_le_log_of_eq
    (q := (29 / 10 : ℝ)) (x := (19 / 39 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 10
  norm_num [logAtanhPartial] at h ⊢
  linarith

lemma log_onethousandonehundredthirtyone_fourhundred_gt_103_div_100 :
    (103 / 100 : ℝ) < Real.log (1131 / 400) := by
  have h := logAtanhPartial_le_log_of_eq
    (q := (1131 / 400 : ℝ)) (x := (731 / 1531 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 10
  norm_num [logAtanhPartial] at h ⊢
  linarith

lemma log_seventynine_twenty_lt_1374_div_1000 :
    Real.log (79 / 20) < (1374 / 1000 : ℝ) := by
  have h := log_le_logAtanhUpper_of_eq
    (q := (79 / 20 : ℝ)) (x := (59 / 99 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 20
  norm_num [logAtanhPartial, logAtanhUpper] at h ⊢
  linarith

lemma log_fiftynine_twenty_gt_1081_div_1000 :
    (1081 / 1000 : ℝ) < Real.log (59 / 20) := by
  have h := logAtanhPartial_le_log_of_eq
    (q := (59 / 20 : ℝ)) (x := (39 / 79 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 10
  norm_num [logAtanhPartial] at h ⊢
  linarith

lemma log_fourthousandsixhundredsixtyone_sixteenhundred_gt_1069_div_1000 :
    (1069 / 1000 : ℝ) < Real.log (4661 / 1600) := by
  have h := logAtanhPartial_le_log_of_eq
    (q := (4661 / 1600 : ℝ)) (x := (3061 / 6261 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 11
  norm_num [logAtanhPartial] at h ⊢
  linarith

lemma log_four_lt_347_div_250 :
    Real.log 4 < (347 / 250 : ℝ) := by
  rw [show (4 : ℝ) = 2 * 2 by norm_num,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num)]
  nlinarith [log_two_lt_347_div_500]

lemma log_two_gt_sixtynine_hundredths :
    (69 / 100 : ℝ) < Real.log 2 := by
  have h := logAtanhPartial_le_log_of_eq
    (q := (2 : ℝ)) (x := (1 / 3 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 5
  norm_num [logAtanhPartial] at h ⊢
  linarith

lemma log_nine_halves_lt_151_hundredths :
    Real.log (9 / 2) < (151 / 100 : ℝ) := by
  have h := log_le_logAtanhUpper_of_eq
    (q := (9 / 2 : ℝ)) (x := (7 / 11 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 25
  norm_num [logAtanhPartial, logAtanhUpper] at h ⊢
  linarith

lemma log_twentyone_eighths_gt_twentyfour_twentyfifths :
    (24 / 25 : ℝ) < Real.log (21 / 8) := by
  have h := logAtanhPartial_le_log_of_eq
    (q := (21 / 8 : ℝ)) (x := (13 / 29 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 8
  norm_num [logAtanhPartial] at h ⊢
  linarith

lemma log_five_lt_161_hundredths :
    Real.log 5 < (161 / 100 : ℝ) := by
  have h := log_le_logAtanhUpper_of_eq
    (q := (5 : ℝ)) (x := (2 / 3 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 30
  norm_num [logAtanhPartial, logAtanhUpper] at h ⊢
  linarith

lemma log_seventeen_fourths_lt_twentynine_twentieths :
    Real.log (17 / 4) < (29 / 20 : ℝ) := by
  have h := log_le_logAtanhUpper_of_eq
    (q := (17 / 4 : ℝ)) (x := (13 / 21 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 22
  norm_num [logAtanhPartial, logAtanhUpper] at h ⊢
  linarith

lemma log_ten_thirds_gt_six_fifths :
    (6 / 5 : ℝ) < Real.log (10 / 3) := by
  have h := logAtanhPartial_le_log_of_eq
    (q := (10 / 3 : ℝ)) (x := (7 / 13 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 10
  norm_num [logAtanhPartial] at h ⊢
  linarith

lemma log_twentyone_fourths_lt_eightythree_fiftieths :
    Real.log (21 / 4) < (83 / 50 : ℝ) := by
  have h := log_le_logAtanhUpper_of_eq
    (q := (21 / 4 : ℝ)) (x := (17 / 25 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 30
  norm_num [logAtanhPartial, logAtanhUpper] at h ⊢
  linarith

lemma log_onehundrednineteen_thirtyseconds_gt_131_hundredths :
    (131 / 100 : ℝ) < Real.log (119 / 32) := by
  have h := logAtanhPartial_le_log_of_eq
    (q := (119 / 32 : ℝ)) (x := (87 / 151 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 12
  norm_num [logAtanhPartial] at h ⊢
  linarith

lemma log_eleven_halves_lt_171_hundredths :
    Real.log (11 / 2) < (171 / 100 : ℝ) := by
  have h := log_le_logAtanhUpper_of_eq
    (q := (11 / 2 : ℝ)) (x := (9 / 13 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 32
  norm_num [logAtanhPartial, logAtanhUpper] at h ⊢
  linarith

lemma log_nineteen_fourths_lt_thirtynine_twentyfifths :
    Real.log (19 / 4) < (39 / 25 : ℝ) := by
  have h := log_le_logAtanhUpper_of_eq
    (q := (19 / 4 : ℝ)) (x := (15 / 23 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 27
  norm_num [logAtanhPartial, logAtanhUpper] at h ⊢
  linarith

lemma log_thirtythree_eighths_gt_1417_thousandths :
    (1417 / 1000 : ℝ) < Real.log (33 / 8) := by
  have h := logAtanhPartial_le_log_of_eq
    (q := (33 / 8 : ℝ)) (x := (25 / 41 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 16
  norm_num [logAtanhPartial] at h ⊢
  linarith

lemma log_twentythree_fourths_lt_seven_fourths :
    Real.log (23 / 4) < (7 / 4 : ℝ) := by
  have h := log_le_logAtanhUpper_of_eq
    (q := (23 / 4 : ℝ)) (x := (19 / 27 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 35
  norm_num [logAtanhPartial, logAtanhUpper] at h ⊢
  linarith

lemma log_fourhundredthirtyseven_ninetysixths_gt_303_halves_hundredths :
    (303 / 200 : ℝ) < Real.log (437 / 96) := by
  have h := logAtanhPartial_le_log_of_eq
    (q := (437 / 96 : ℝ)) (x := (341 / 533 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 20
  norm_num [logAtanhPartial] at h ⊢
  linarith

lemma dickmanRho_seven_halves_lt_one_twentyfifth :
    dickmanRho (7 / 2) < (1 / 25 : ℝ) := by
  have hprev := dickmanRho_le_refined_two_three
    (e := (5 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hlogMain := log_five_halves_gt_4581_div_5000
  have hlogAux := log_three_halves_bounds.2
  have haux0 : 0 ≤ Real.log (3 / 2) := Real.log_nonneg (by norm_num)
  have haux2 : Real.log (3 / 2) ^ 2 ≤
      (40547 / 100000 : ℝ) ^ 2 :=
    pow_le_pow_left₀ haux0 hlogAux.le 2
  have haux3 : Real.log (3 / 2) ^ 3 ≤
      (40547 / 100000 : ℝ) ^ 3 :=
    pow_le_pow_left₀ haux0 hlogAux.le 3
  have hprev' : dickmanRho (5 / 2) < (131 / 1000 : ℝ) := by
    norm_num at hprev ⊢
    nlinarith
  have hstep := dickmanRho_le_previous_div
    (e := (7 / 2 : ℝ)) (by norm_num)
  norm_num at hstep ⊢
  nlinarith

lemma dickmanRho_seven_halves_lt_three_eightieth :
    dickmanRho (7 / 2) < (3 / 80 : ℝ) := by
  have hprev := dickmanRho_le_refined_two_three
    (e := (5 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hlogMain := log_five_halves_gt_4581_div_5000
  have hlogAux := log_three_halves_bounds.2
  have haux0 : 0 ≤ Real.log (3 / 2) := Real.log_nonneg (by norm_num)
  have haux2 : Real.log (3 / 2) ^ 2 ≤
      (40547 / 100000 : ℝ) ^ 2 :=
    pow_le_pow_left₀ haux0 hlogAux.le 2
  have haux3 : Real.log (3 / 2) ^ 3 ≤
      (40547 / 100000 : ℝ) ^ 3 :=
    pow_le_pow_left₀ haux0 hlogAux.le 3
  have hprev' : dickmanRho (5 / 2) < (131 / 1000 : ℝ) := by
    norm_num at hprev ⊢
    nlinarith
  have hstep := dickmanRho_le_previous_div
    (e := (7 / 2 : ℝ)) (by norm_num)
  norm_num at hstep ⊢
  nlinarith

lemma dickmanRho_nineteen_fifths_lt_one_fiftieth :
    dickmanRho (19 / 5) < (1 / 50 : ℝ) := by
  have hprev := dickmanRho_le_refined_two_three
    (e := (14 / 5 : ℝ)) (by norm_num) (by norm_num)
  have hlogMain := log_fourteen_fifths_gt_1287_div_1250
  have hlogAux := log_nine_fifths_lt_147_div_250
  have haux0 : 0 ≤ Real.log (9 / 5) := Real.log_nonneg (by norm_num)
  have haux2 : Real.log (9 / 5) ^ 2 ≤ (147 / 250 : ℝ) ^ 2 :=
    pow_le_pow_left₀ haux0 hlogAux.le 2
  have haux3 : Real.log (9 / 5) ^ 3 ≤ (147 / 250 : ℝ) ^ 3 :=
    pow_le_pow_left₀ haux0 hlogAux.le 3
  have hprev' : dickmanRho (14 / 5) < (3 / 40 : ℝ) := by
    norm_num at hprev ⊢
    nlinarith
  have hstep := dickmanRho_le_previous_div
    (e := (19 / 5 : ℝ)) (by norm_num)
  norm_num at hstep ⊢
  nlinarith

lemma integral_dickmanRho_le_const_of_antitone
    {a b c : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b)
    (hrho : dickmanRho a ≤ c) :
    (∫ t : ℝ in a..b, dickmanRho t) ≤ (b - a) * c := by
  have hint : IntervalIntegrable dickmanRho volume a b :=
    intervalIntegrable_dickmanRho_of_nonneg ha0 (ha0.trans hab)
  have hconst : IntervalIntegrable (fun _t : ℝ ↦ c) volume a b :=
    intervalIntegrable_const
  have h := intervalIntegral.integral_mono_on hab hint hconst
    (fun t ht ↦
      (antitoneOn_dickmanRho_Ici_zero ha0 (ha0.trans ht.1) ht.1).trans hrho)
  simpa using h

lemma dickmanRho_four_lt_one_hundredth :
    dickmanRho 4 < (1 / 100 : ℝ) := by
  have hA : (∫ t : ℝ in (3 : ℝ)..(7 / 2), dickmanRho t) ≤
      ((7 / 2 : ℝ) - 3) * (493 / 10000 : ℝ) :=
    integral_dickmanRho_le_const_of_antitone (by norm_num) (by norm_num)
      dickmanRho_three_lt_493_div_10000.le
  have hB : (∫ t : ℝ in (7 / 2 : ℝ)..(19 / 5), dickmanRho t) ≤
      ((19 / 5 : ℝ) - 7 / 2) * (3 / 80 : ℝ) :=
    integral_dickmanRho_le_const_of_antitone (by norm_num) (by norm_num)
      dickmanRho_seven_halves_lt_three_eightieth.le
  have hC : (∫ t : ℝ in (19 / 5 : ℝ)..4, dickmanRho t) ≤
      ((4 : ℝ) - 19 / 5) * (1 / 50 : ℝ) :=
    integral_dickmanRho_le_const_of_antitone (by norm_num) (by norm_num)
      dickmanRho_nineteen_fifths_lt_one_fiftieth.le
  have hintA : IntervalIntegrable dickmanRho volume (3 : ℝ) (7 / 2) :=
    intervalIntegrable_dickmanRho_of_nonneg (by norm_num) (by norm_num)
  have hintB : IntervalIntegrable dickmanRho volume (7 / 2 : ℝ) (19 / 5) :=
    intervalIntegrable_dickmanRho_of_nonneg (by norm_num) (by norm_num)
  have hintC : IntervalIntegrable dickmanRho volume (19 / 5 : ℝ) 4 :=
    intervalIntegrable_dickmanRho_of_nonneg (by norm_num) (by norm_num)
  have hsplitAB := intervalIntegral.integral_add_adjacent_intervals hintA hintB
  have hintAB : IntervalIntegrable dickmanRho volume (3 : ℝ) (19 / 5) :=
    intervalIntegrable_dickmanRho_of_nonneg (by norm_num) (by norm_num)
  have hsplitABC := intervalIntegral.integral_add_adjacent_intervals hintAB hintC
  have htotal : (∫ t : ℝ in (3 : ℝ)..4, dickmanRho t) =
      (∫ t : ℝ in (3 : ℝ)..(7 / 2), dickmanRho t) +
        (∫ t : ℝ in (7 / 2 : ℝ)..(19 / 5), dickmanRho t) +
          (∫ t : ℝ in (19 / 5 : ℝ)..4, dickmanRho t) := by
    calc
      _ = (∫ t : ℝ in (3 : ℝ)..(19 / 5), dickmanRho t) +
          ∫ t : ℝ in (19 / 5 : ℝ)..4, dickmanRho t := hsplitABC.symm
      _ = _ := by rw [← hsplitAB]
  have hdelay := dickmanRho_profile.2.2.2.2 (4 : ℝ) (by norm_num)
  norm_num at hdelay htotal ⊢
  nlinarith

lemma gsSection61LowModel_antitone_three_seven_halves :
    AntitoneOn gsSection61LowModel (Icc (3 : ℝ) (7 / 2)) := by
  apply gsSection61LowModel_antitone_piece
      (Q := (79 / 100 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  · intro e he
    have he0 : 0 < e := by linarith [he.1]
    have hem0 : 0 < e - 1 := by linarith [he.1]
    have harg : e * (e - 1) / 4 ≤ 35 / 16 := by nlinarith [he.2]
    have harg0 : 0 < e * (e - 1) / 4 := by positivity
    have hlog := Real.strictMonoOn_log.monotoneOn harg0 (by norm_num) harg
    have hprod : Real.log (e * (e - 1) / 4) =
        Real.log e + Real.log (e - 1) - Real.log 4 := by
      rw [Real.log_div (mul_ne_zero he0.ne' hem0.ne') (by norm_num),
        Real.log_mul he0.ne' hem0.ne']
    rw [hprod] at hlog
    exact hlog.trans log_thirtyfive_sixteenths_bounds.2.le
  · norm_num
  · norm_num

lemma gsSection61LowModel_antitone_seven_halves_thirtyseven_tenths :
    AntitoneOn gsSection61LowModel (Icc (7 / 2 : ℝ) (37 / 10)) := by
  apply gsSection61LowModel_antitone_piece
      (Q := (23 / 25 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  · intro e he
    have he0 : 0 < e := by linarith [he.1]
    have hem0 : 0 < e - 1 := by linarith [he.1]
    have harg : e * (e - 1) / 4 ≤ 999 / 400 := by nlinarith [he.2]
    have harg0 : 0 < e * (e - 1) / 4 := by positivity
    have hlog := Real.strictMonoOn_log.monotoneOn harg0 (by norm_num) harg
    have hprod : Real.log (e * (e - 1) / 4) =
        Real.log e + Real.log (e - 1) - Real.log 4 := by
      rw [Real.log_div (mul_ne_zero he0.ne' hem0.ne') (by norm_num),
        Real.log_mul he0.ne' hem0.ne']
    rw [hprod] at hlog
    exact hlog.trans log_ninehundredninetynine_fourhundred_lt.le
  · norm_num
  · norm_num

lemma gsSection61LowModel_antitone_thirtyseven_tenths_nineteen_fifths :
    AntitoneOn gsSection61LowModel (Icc (37 / 10 : ℝ) (19 / 5)) := by
  apply gsSection61LowModel_antitone_piece
      (Q := (49 / 50 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  · intro e he
    have he0 : 0 < e := by linarith [he.1]
    have hem0 : 0 < e - 1 := by linarith [he.1]
    have harg : e * (e - 1) / 4 ≤ 133 / 50 := by nlinarith [he.2]
    have harg0 : 0 < e * (e - 1) / 4 := by positivity
    have hlog := Real.strictMonoOn_log.monotoneOn harg0 (by norm_num) harg
    have hprod : Real.log (e * (e - 1) / 4) =
        Real.log e + Real.log (e - 1) - Real.log 4 := by
      rw [Real.log_div (mul_ne_zero he0.ne' hem0.ne') (by norm_num),
        Real.log_mul he0.ne' hem0.ne']
    rw [hprod] at hlog
    exact hlog.trans log_onehundredthirtythree_fifty_bounds.2.le
  · norm_num
  · norm_num

lemma gsSection61LowModel_seven_halves_gt_one_twentieth :
    (1 / 20 : ℝ) < gsSection61LowModel (7 / 2) := by
  let w : ℝ := Real.log (5 / 2)
  let q : ℝ := Real.log (35 / 16)
  have hw0 : 0 ≤ w := Real.log_nonneg (by norm_num)
  have hwlo : (4581 / 5000 : ℝ) ≤ w :=
    log_five_halves_gt_4581_div_5000.le
  have hwUpper : w ≤ 3 / 2 := by
    dsimp only [w]
    exact (Real.log_le_sub_one_of_pos (by norm_num)).trans_eq (by norm_num)
  have hq0 : 0 ≤ q := Real.log_nonneg (by norm_num)
  have hqlo : (7827 / 10000 : ℝ) ≤ q :=
    log_thirtyfive_sixteenths_bounds.1.le
  have hE := log_seven_halves_lt_1566_div_1250.le
  have hg : (4581 / 5000 : ℝ) ^ 2 / 2 -
        (4581 / 5000 : ℝ) ^ 3 / 6 ≤ w ^ 2 / 2 - w ^ 3 / 6 := by
    have hdiff : 0 ≤ w - (4581 / 5000 : ℝ) := sub_nonneg.mpr hwlo
    have hbracket : 0 ≤
        3 * (w + (4581 / 5000 : ℝ)) -
          (w ^ 2 + w * (4581 / 5000 : ℝ) +
            (4581 / 5000 : ℝ) ^ 2) := by
      nlinarith [mul_nonneg hw0 (sub_nonneg.mpr hwUpper),
        mul_nonneg (by norm_num : (0 : ℝ) ≤ 4581 / 5000)
          (sub_nonneg.mpr hwUpper),
        mul_nonneg (sub_nonneg.mpr hwUpper)
          (by norm_num : (0 : ℝ) ≤ 4581 / 5000)]
    nlinarith [mul_nonneg hdiff hbracket]
  have hq2 : (7827 / 10000 : ℝ) ^ 2 ≤ q ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self (by norm_num) hqlo
  have hq4 : (7827 / 10000 : ℝ) ^ 4 ≤ q ^ 4 := by
    nlinarith [mul_self_le_mul_self (sq_nonneg (7827 / 10000 : ℝ)) hq2]
  have hcoef : 0 ≤ 1 - Real.log (7 / 2) / 5 := by nlinarith
  have hcoefLower : 1 - (1566 / 1250 : ℝ) / 5 ≤
      1 - Real.log (7 / 2) / 5 := by linarith
  have hbonus := mul_le_mul hq4 hcoefLower
    (by norm_num : 0 ≤ 1 - (1566 / 1250 : ℝ) / 5)
    (by positivity : 0 ≤ q ^ 4)
  have hqEq : Real.log (7 / 2) + Real.log (5 / 2) - Real.log 4 = q := by
    dsimp only [q]
    rw [← Real.log_mul (by norm_num : (7 / 2 : ℝ) ≠ 0) (by norm_num)]
    rw [show (7 / 2 : ℝ) * (5 / 2) = 35 / 4 by norm_num]
    rw [← Real.log_div (by norm_num : (35 / 4 : ℝ) ≠ 0) (by norm_num)]
    congr 1 <;> norm_num
  dsimp only [gsSection61LowModel]
  rw [show (7 / 2 : ℝ) - 1 = 5 / 2 by norm_num, hqEq]
  dsimp only [w] at hg
  nlinarith [hg, hbonus]

lemma gsSection61LowModel_nineteen_fifths_gt_one_twentyfifth :
    (1 / 25 : ℝ) < gsSection61LowModel (19 / 5) := by
  let w : ℝ := Real.log (14 / 5)
  let q : ℝ := Real.log (133 / 50)
  have hw0 : 0 ≤ w := Real.log_nonneg (by norm_num)
  have hwlo : (1287 / 1250 : ℝ) ≤ w :=
    log_fourteen_fifths_gt_1287_div_1250.le
  have hwUpper : w ≤ 9 / 5 := by
    dsimp only [w]
    exact (Real.log_le_sub_one_of_pos (by norm_num)).trans_eq (by norm_num)
  have hq0 : 0 ≤ q := Real.log_nonneg (by norm_num)
  have hqlo : (9783 / 10000 : ℝ) ≤ q :=
    log_onehundredthirtythree_fifty_bounds.1.le
  have hE := log_nineteen_fifths_lt_13351_div_10000.le
  have hg : (1287 / 1250 : ℝ) ^ 2 / 2 -
        (1287 / 1250 : ℝ) ^ 3 / 6 ≤ w ^ 2 / 2 - w ^ 3 / 6 := by
    have hdiff : 0 ≤ w - (1287 / 1250 : ℝ) := sub_nonneg.mpr hwlo
    have hbracket : 0 ≤
        3 * (w + (1287 / 1250 : ℝ)) -
          (w ^ 2 + w * (1287 / 1250 : ℝ) +
            (1287 / 1250 : ℝ) ^ 2) := by
      nlinarith [mul_nonneg hw0 (sub_nonneg.mpr hwUpper),
        mul_nonneg (by norm_num : (0 : ℝ) ≤ 1287 / 1250)
          (sub_nonneg.mpr hwUpper),
        mul_nonneg (sub_nonneg.mpr hwUpper)
          (by norm_num : (0 : ℝ) ≤ 1287 / 1250)]
    nlinarith [mul_nonneg hdiff hbracket]
  have hq2 : (9783 / 10000 : ℝ) ^ 2 ≤ q ^ 2 := by nlinarith
  have hq4 : (9783 / 10000 : ℝ) ^ 4 ≤ q ^ 4 := by nlinarith
  have hcoef : 0 ≤ 1 - Real.log (19 / 5) / 5 := by nlinarith
  have hcoefLower : 1 - (13351 / 10000 : ℝ) / 5 ≤
      1 - Real.log (19 / 5) / 5 := by linarith
  have hbonus := mul_le_mul hq4 hcoefLower
    (by norm_num : 0 ≤ 1 - (13351 / 10000 : ℝ) / 5)
    (by positivity : 0 ≤ q ^ 4)
  have hqEq : Real.log (19 / 5) + Real.log (14 / 5) - Real.log 4 = q := by
    dsimp only [q]
    rw [← Real.log_mul (by norm_num : (19 / 5 : ℝ) ≠ 0) (by norm_num)]
    rw [show (19 / 5 : ℝ) * (14 / 5) = 266 / 25 by norm_num]
    rw [← Real.log_div (by norm_num : (266 / 25 : ℝ) ≠ 0) (by norm_num)]
    congr 1 <;> norm_num
  dsimp only [gsSection61LowModel]
  rw [show (19 / 5 : ℝ) - 1 = 14 / 5 by norm_num, hqEq]
  dsimp only [w] at hg
  nlinarith [hg, hbonus]

/-- The degree-three paired Bonferroni expression dominates the explicit
low model throughout `3 ≤ e ≤ 4`. -/
lemma gsSection61LowModel_le_paired
    {e a m : ℝ} (he3 : 3 ≤ e) (he4 : e ≤ 4)
    (haLower : e - 1 ≤ a) (haUpper : a ≤ e)
    (hmLower : Real.log e + Real.log (e - 1) - Real.log 4 ≤ m) :
    gsSection61LowModel e ≤
      gsExpAlternatingSum (Real.log a) 3 +
          m ^ 4 / 24 * (1 - Real.log a / 5) -
        (Real.log e - Real.log a) := by
  let w : ℝ := Real.log (e - 1)
  let z : ℝ := Real.log a
  let q : ℝ := Real.log e + Real.log (e - 1) - Real.log 4
  have he0 : 0 < e := by linarith
  have hem0 : 0 < e - 1 := by linarith
  have ha0 : 0 < a := hem0.trans_le haLower
  have hw0 : 0 ≤ w := by
    dsimp only [w]
    exact Real.log_nonneg (by linarith)
  have hz0 : 0 ≤ z := by
    dsimp only [z]
    exact Real.log_nonneg (by linarith)
  have hwz : w ≤ z := by
    dsimp only [w, z]
    exact Real.strictMonoOn_log.monotoneOn hem0 ha0 haLower
  have hze : z ≤ Real.log e := by
    dsimp only [z]
    exact Real.strictMonoOn_log.monotoneOn ha0 he0 haUpper
  have hlogE4 : Real.log e ≤ Real.log 4 :=
    Real.strictMonoOn_log.monotoneOn he0 (by norm_num) he4
  have hz2 : z ≤ 2 := hze.trans (hlogE4.trans log_four_lt_two.le)
  have hw2 : w ≤ 2 := hwz.trans hz2
  have hcross : z * w ≤ z + w := by
    by_cases hz1 : z ≤ 1
    · nlinarith [mul_le_mul_of_nonneg_right hz1 hw0]
    · have hmul := mul_le_mul_of_nonneg_left hw2 hz0
      nlinarith
  have hmain : w ^ 2 / 2 - w ^ 3 / 6 ≤
      z ^ 2 / 2 - z ^ 3 / 6 := by
    have hdiff : 0 ≤ z - w := sub_nonneg.mpr hwz
    have hzsq : z ^ 2 ≤ 2 * z := by
      nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hz2)]
    have hwsq : w ^ 2 ≤ 2 * w := by
      nlinarith [mul_nonneg hw0 (sub_nonneg.mpr hw2)]
    have hbracket : 0 ≤ 3 * (z + w) - (z ^ 2 + z * w + w ^ 2) := by
      linarith
    nlinarith [mul_nonneg hdiff
      hbracket]
  have hqEq : q = Real.log (e * (e - 1) / 4) := by
    dsimp only [q]
    rw [Real.log_div (mul_ne_zero he0.ne' hem0.ne') (by norm_num),
      Real.log_mul he0.ne' hem0.ne']
  have harg : 1 ≤ e * (e - 1) / 4 := by nlinarith
  have hq0 : 0 ≤ q := by
    rw [hqEq]
    exact Real.log_nonneg harg
  have hm0 : 0 ≤ m := hq0.trans hmLower
  have hpow : q ^ 4 ≤ m ^ 4 := pow_le_pow_left₀ hq0 hmLower 4
  have hcoefE : 0 ≤ 1 - Real.log e / 5 := by
    nlinarith [hlogE4.trans log_four_lt_two.le]
  have hcoef : 1 - Real.log e / 5 ≤ 1 - z / 5 := by
    linarith
  have hbonus : q ^ 4 / 24 * (1 - Real.log e / 5) ≤
      m ^ 4 / 24 * (1 - z / 5) := by
    calc
      q ^ 4 / 24 * (1 - Real.log e / 5) ≤
          m ^ 4 / 24 * (1 - Real.log e / 5) := by
            gcongr
      _ ≤ m ^ 4 / 24 * (1 - z / 5) := by
            exact mul_le_mul_of_nonneg_left hcoef (by positivity)
  dsimp only [gsSection61LowModel]
  norm_num [gsExpAlternatingSum, Finset.sum_range_succ]
  dsimp only [w, z, q] at hmain hbonus ⊢
  nlinarith

/-- The degree-five paired Bonferroni expression dominates the middle
model throughout `4 ≤ e ≤ 6`. -/
lemma gsSection61MidModel_le_paired
    {e a m : ℝ} (he4 : 4 ≤ e) (he6 : e ≤ 6)
    (haLower : e - 1 ≤ a) (haUpper : a ≤ e)
    (hmLower : Real.log e + Real.log (e - 1) - Real.log 6 ≤ m) :
    gsSection61MidModel e ≤
      gsExpAlternatingSum (Real.log a) 5 +
          m ^ 6 / 720 * (1 - Real.log a / 7) -
        (Real.log e - Real.log a) := by
  let w : ℝ := Real.log (e - 1)
  let z : ℝ := Real.log a
  let q : ℝ := Real.log e + Real.log (e - 1) - Real.log 6
  have he0 : 0 < e := by linarith
  have hem0 : 0 < e - 1 := by linarith
  have ha0 : 0 < a := hem0.trans_le haLower
  have hw0 : 0 ≤ w := by
    dsimp only [w]
    exact Real.log_nonneg (by linarith)
  have hz0 : 0 ≤ z := by
    dsimp only [z]
    exact Real.log_nonneg (by linarith)
  have hwz : w ≤ z := by
    dsimp only [w, z]
    exact Real.strictMonoOn_log.monotoneOn hem0 ha0 haLower
  have hze : z ≤ Real.log e := by
    dsimp only [z]
    exact Real.strictMonoOn_log.monotoneOn ha0 he0 haUpper
  have hlogE6 : Real.log e ≤ Real.log 6 :=
    Real.strictMonoOn_log.monotoneOn he0 (by norm_num) he6
  have hz2 : z ≤ 2 := hze.trans (hlogE6.trans log_six_lt_two.le)
  have hw2 : w ≤ 2 := hwz.trans hz2
  have hmain : gsTaylorFiveTail w ≤ gsTaylorFiveTail z :=
    monotoneOn_gsTaylorFiveTail ⟨hw0, hw2⟩ ⟨hz0, hz2⟩ hwz
  have hqEq : q = Real.log (e * (e - 1) / 6) := by
    dsimp only [q]
    rw [Real.log_div (mul_ne_zero he0.ne' hem0.ne') (by norm_num),
      Real.log_mul he0.ne' hem0.ne']
  have harg : 1 ≤ e * (e - 1) / 6 := by nlinarith
  have hq0 : 0 ≤ q := by
    rw [hqEq]
    exact Real.log_nonneg harg
  have hm0 : 0 ≤ m := hq0.trans hmLower
  have hpow : q ^ 6 ≤ m ^ 6 := pow_le_pow_left₀ hq0 hmLower 6
  have hcoefE : 0 ≤ 1 - Real.log e / 7 := by
    nlinarith [hlogE6.trans log_six_lt_two.le]
  have hcoef : 1 - Real.log e / 7 ≤ 1 - z / 7 := by linarith
  have hbonus : q ^ 6 / 720 * (1 - Real.log e / 7) ≤
      m ^ 6 / 720 * (1 - z / 7) := by
    calc
      q ^ 6 / 720 * (1 - Real.log e / 7) ≤
          m ^ 6 / 720 * (1 - Real.log e / 7) := by
            gcongr
      _ ≤ m ^ 6 / 720 * (1 - z / 7) := by
            exact mul_le_mul_of_nonneg_left hcoef (by positivity)
  dsimp only [gsSection61MidModel]
  norm_num [gsExpAlternatingSum, Finset.sum_range_succ, gsTaylorFiveTail]
  simp only [gsTaylorFiveTail] at hmain
  dsimp only [w, z, q] at hmain hbonus ⊢
  nlinarith

/-- Rational-envelope lower bound for the middle model.  The parameters
`X,W,Q,E` are respectively lower/upper/lower/upper bounds for
`1/(e-1)`, `log(e-1)`, `log(e(e-1)/6)`, and `log e`. -/
lemma gsSection61MidModel_lower_of_bounds
    {e X W Q E : ℝ} (he4 : 4 ≤ e) (he6 : e ≤ 6)
    (hX0 : 0 ≤ X) (hX : X ≤ 1 / (e - 1))
    (hW : Real.log (e - 1) ≤ W) (hW2 : W ≤ 2)
    (hQ0 : 0 ≤ Q)
    (hQ : Q ≤ Real.log e + Real.log (e - 1) - Real.log 6)
    (hE : Real.log e ≤ E) (hE7 : E ≤ 7) :
    X ^ 2 / 2 - X ^ 3 / 3 + gsTaylorFiveErrorLower W +
        Q ^ 6 / 720 * (1 - E / 7) ≤ gsSection61MidModel e := by
  let w : ℝ := Real.log (e - 1)
  let x : ℝ := 1 / (e - 1)
  let q : ℝ := Real.log e + Real.log (e - 1) - Real.log 6
  have he0 : 0 < e := by linarith
  have hem0 : 0 < e - 1 := by linarith
  have hw0 : 0 ≤ w := by
    dsimp only [w]
    exact Real.log_nonneg (by linarith)
  have hlogE6 : Real.log e ≤ Real.log 6 :=
    Real.strictMonoOn_log.monotoneOn he0 (by norm_num) he6
  have hwle : w ≤ Real.log e := by
    dsimp only [w]
    exact Real.strictMonoOn_log.monotoneOn hem0 he0 (by linarith)
  have hw2 : w ≤ 2 := hwle.trans (hlogE6.trans log_six_lt_two.le)
  have hx0 : 0 ≤ x := by dsimp only [x]; positivity
  have hx1 : x ≤ 1 := by
    dsimp only [x]
    rw [div_le_one hem0]
    linarith
  have hX1 : X ≤ 1 := hX.trans hx1
  have hcross : 2 * x * X ≤ x + X := by
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hX1),
      mul_nonneg hX0 (sub_nonneg.mpr hx1)]
  have hk : X ^ 2 / 2 - X ^ 3 / 3 ≤ x ^ 2 / 2 - x ^ 3 / 3 := by
    have hdiff : 0 ≤ x - X := sub_nonneg.mpr hX
    have hxsq : 2 * x ^ 2 ≤ 2 * x := by
      nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]
    have hXsq : 2 * X ^ 2 ≤ 2 * X := by
      nlinarith [mul_nonneg hX0 (sub_nonneg.mpr hX1)]
    have hbracket : 0 ≤
        3 * (x + X) - 2 * (x ^ 2 + x * X + X ^ 2) := by
      linarith
    nlinarith [mul_nonneg hdiff hbracket]
  have hW0 : 0 ≤ W := hw0.trans hW
  have herr : gsTaylorFiveErrorLower W ≤
      gsTaylorFiveErrorLower w :=
    antitoneOn_gsTaylorFiveErrorLower ⟨hw0, hw2⟩ ⟨hW0, hW2⟩ hW
  have hP := gsExpAlternatingSum_five_lower hw0 hw2
  have hP' : Real.exp (-w) + gsTaylorFiveErrorLower w ≤
      gsExpAlternatingSum w 5 := by
    dsimp only [gsTaylorFiveErrorLower]
    linarith
  have hexp : Real.exp (-w) = x := by
    dsimp only [w, x]
    rw [Real.exp_neg, Real.exp_log hem0]
    simp only [one_div]
  have hdelta : Real.log e - w = Real.log (1 + x) := by
    have hratio : e / (e - 1) = 1 + x := by
      dsimp only [x]
      field_simp [hem0.ne']
      ring
    dsimp only [w]
    rw [← Real.log_div he0.ne' hem0.ne', hratio]
  have hlog := log_one_add_le_cubic hx0
  have hbase : x ^ 2 / 2 - x ^ 3 / 3 +
        gsTaylorFiveErrorLower w ≤
      gsExpAlternatingSum w 5 - (Real.log e - w) := by
    rw [hexp] at hP'
    rw [hdelta]
    linarith
  have hqEq : q = Real.log (e * (e - 1) / 6) := by
    dsimp only [q]
    rw [Real.log_div (mul_ne_zero he0.ne' hem0.ne') (by norm_num),
      Real.log_mul he0.ne' hem0.ne']
  have harg : 1 ≤ e * (e - 1) / 6 := by nlinarith
  have hq0 : 0 ≤ q := by
    rw [hqEq]
    exact Real.log_nonneg harg
  have hpow : Q ^ 6 ≤ q ^ 6 := pow_le_pow_left₀ hQ0 hQ 6
  have hcoefLower : 0 ≤ 1 - E / 7 := by linarith
  have hcoef : 1 - E / 7 ≤ 1 - Real.log e / 7 := by linarith
  have hbonus : Q ^ 6 / 720 * (1 - E / 7) ≤
      q ^ 6 / 720 * (1 - Real.log e / 7) := by
    calc
      Q ^ 6 / 720 * (1 - E / 7) ≤
          q ^ 6 / 720 * (1 - E / 7) := by
            gcongr
      _ ≤ q ^ 6 / 720 * (1 - Real.log e / 7) := by
            exact mul_le_mul_of_nonneg_left hcoef (by positivity)
  dsimp only [gsSection61MidModel]
  norm_num [gsExpAlternatingSum, Finset.sum_range_succ, gsTaylorFiveTail]
    at hbase
  simp only [gsTaylorFiveTail]
  dsimp only [w, x, q] at hk herr hbase hbonus ⊢
  linarith

lemma one_hundredth_lt_gsSection61MidModel_four_six
    {e : ℝ} (he4 : 4 ≤ e) (he6 : e ≤ 6) :
    (1 / 100 : ℝ) < gsSection61MidModel e := by
  have he0 : 0 < e := by linarith
  have hem0 : 0 < e - 1 := by linarith
  have hprodEq : Real.log (e * (e - 1) / 6) =
      Real.log e + Real.log (e - 1) - Real.log 6 := by
    rw [Real.log_div (mul_ne_zero he0.ne' hem0.ne') (by norm_num),
      Real.log_mul he0.ne' hem0.ne']
  by_cases h1 : e ≤ 9 / 2
  · have hX : (2 / 7 : ℝ) ≤ 1 / (e - 1) := by
      rw [le_div_iff₀ hem0]
      nlinarith
    have hWlog := Real.strictMonoOn_log.monotoneOn hem0
      (by norm_num : (0 : ℝ) < 7 / 2) (by linarith : e - 1 ≤ 7 / 2)
    have hW : Real.log (e - 1) ≤ (63 / 50 : ℝ) :=
      hWlog.trans (by linarith [log_seven_halves_lt_1566_div_1250])
    have harg : (2 : ℝ) ≤ e * (e - 1) / 6 := by nlinarith
    have hQlog := Real.strictMonoOn_log.monotoneOn
      (by norm_num : (0 : ℝ) < 2)
      (show (0 : ℝ) < e * (e - 1) / 6 by positivity) harg
    rw [hprodEq] at hQlog
    have hQ : (69 / 100 : ℝ) ≤
        Real.log e + Real.log (e - 1) - Real.log 6 :=
      log_two_gt_sixtynine_hundredths.le.trans hQlog
    have hE := (Real.strictMonoOn_log.monotoneOn he0
      (by norm_num : (0 : ℝ) < 9 / 2) h1).trans
        log_nine_halves_lt_151_hundredths.le
    have hmodel := gsSection61MidModel_lower_of_bounds
      (e := e) (X := (2 / 7 : ℝ)) (W := (63 / 50 : ℝ))
      (Q := (69 / 100 : ℝ)) (E := (151 / 100 : ℝ))
      he4 he6 (by norm_num) hX hW (by norm_num) (by norm_num) hQ hE
      (by norm_num)
    norm_num [gsTaylorFiveErrorLower] at hmodel ⊢
    linarith
  · have hlo : 9 / 2 ≤ e := le_of_not_ge h1
    by_cases h2 : e ≤ 5
    · have hX : (1 / 4 : ℝ) ≤ 1 / (e - 1) := by
        rw [le_div_iff₀ hem0]
        nlinarith
      have hWlog := Real.strictMonoOn_log.monotoneOn hem0
        (by norm_num : (0 : ℝ) < 4) (by linarith : e - 1 ≤ 4)
      have hW : Real.log (e - 1) ≤ (139 / 100 : ℝ) :=
        hWlog.trans (by linarith [log_four_lt_347_div_250])
      have harg : (21 / 8 : ℝ) ≤ e * (e - 1) / 6 := by nlinarith
      have hQlog := Real.strictMonoOn_log.monotoneOn
        (by norm_num : (0 : ℝ) < 21 / 8)
        (show (0 : ℝ) < e * (e - 1) / 6 by positivity) harg
      rw [hprodEq] at hQlog
      have hQ : (24 / 25 : ℝ) ≤
          Real.log e + Real.log (e - 1) - Real.log 6 :=
        log_twentyone_eighths_gt_twentyfour_twentyfifths.le.trans hQlog
      have hE := (Real.strictMonoOn_log.monotoneOn he0
        (by norm_num : (0 : ℝ) < 5) h2).trans log_five_lt_161_hundredths.le
      have hmodel := gsSection61MidModel_lower_of_bounds
        (e := e) (X := (1 / 4 : ℝ)) (W := (139 / 100 : ℝ))
        (Q := (24 / 25 : ℝ)) (E := (161 / 100 : ℝ))
        he4 he6 (by norm_num) hX hW (by norm_num) (by norm_num) hQ hE
        (by norm_num)
      norm_num [gsTaylorFiveErrorLower] at hmodel ⊢
      linarith
    · have hlo2 : 5 ≤ e := le_of_not_ge h2
      by_cases h3 : e ≤ 21 / 4
      · have hX : (4 / 17 : ℝ) ≤ 1 / (e - 1) := by
          rw [le_div_iff₀ hem0]
          nlinarith
        have hWlog := Real.strictMonoOn_log.monotoneOn hem0
          (by norm_num : (0 : ℝ) < 17 / 4)
          (by linarith : e - 1 ≤ 17 / 4)
        have hW := hWlog.trans log_seventeen_fourths_lt_twentynine_twentieths.le
        have harg : (10 / 3 : ℝ) ≤ e * (e - 1) / 6 := by nlinarith
        have hQlog := Real.strictMonoOn_log.monotoneOn
          (by norm_num : (0 : ℝ) < 10 / 3)
          (show (0 : ℝ) < e * (e - 1) / 6 by positivity) harg
        rw [hprodEq] at hQlog
        have hQ : (6 / 5 : ℝ) ≤
            Real.log e + Real.log (e - 1) - Real.log 6 :=
          log_ten_thirds_gt_six_fifths.le.trans hQlog
        have hE := (Real.strictMonoOn_log.monotoneOn he0
          (by norm_num : (0 : ℝ) < 21 / 4) h3).trans
            log_twentyone_fourths_lt_eightythree_fiftieths.le
        have hmodel := gsSection61MidModel_lower_of_bounds
          (e := e) (X := (4 / 17 : ℝ)) (W := (29 / 20 : ℝ))
          (Q := (6 / 5 : ℝ)) (E := (83 / 50 : ℝ))
          he4 he6 (by norm_num) hX hW (by norm_num) (by norm_num) hQ hE
          (by norm_num)
        norm_num [gsTaylorFiveErrorLower] at hmodel ⊢
        linarith
      · have hlo3 : 21 / 4 ≤ e := le_of_not_ge h3
        by_cases h4' : e ≤ 11 / 2
        · have hX : (2 / 9 : ℝ) ≤ 1 / (e - 1) := by
            rw [le_div_iff₀ hem0]
            nlinarith
          have hWlog := Real.strictMonoOn_log.monotoneOn hem0
            (by norm_num : (0 : ℝ) < 9 / 2)
            (by linarith : e - 1 ≤ 9 / 2)
          have hW := hWlog.trans log_nine_halves_lt_151_hundredths.le
          have harg : (119 / 32 : ℝ) ≤ e * (e - 1) / 6 := by nlinarith
          have hQlog := Real.strictMonoOn_log.monotoneOn
            (by norm_num : (0 : ℝ) < 119 / 32)
            (show (0 : ℝ) < e * (e - 1) / 6 by positivity) harg
          rw [hprodEq] at hQlog
          have hQ : (131 / 100 : ℝ) ≤
              Real.log e + Real.log (e - 1) - Real.log 6 :=
            log_onehundrednineteen_thirtyseconds_gt_131_hundredths.le.trans hQlog
          have hE := (Real.strictMonoOn_log.monotoneOn he0
            (by norm_num : (0 : ℝ) < 11 / 2) h4').trans
              log_eleven_halves_lt_171_hundredths.le
          have hmodel := gsSection61MidModel_lower_of_bounds
            (e := e) (X := (2 / 9 : ℝ)) (W := (151 / 100 : ℝ))
            (Q := (131 / 100 : ℝ)) (E := (171 / 100 : ℝ))
            he4 he6 (by norm_num) hX hW (by norm_num) (by norm_num) hQ hE
            (by norm_num)
          norm_num [gsTaylorFiveErrorLower] at hmodel ⊢
          linarith
        · have hlo4 : 11 / 2 ≤ e := le_of_not_ge h4'
          by_cases h5 : e ≤ 23 / 4
          · have hX : (4 / 19 : ℝ) ≤ 1 / (e - 1) := by
              rw [le_div_iff₀ hem0]
              nlinarith
            have hWlog := Real.strictMonoOn_log.monotoneOn hem0
              (by norm_num : (0 : ℝ) < 19 / 4)
              (by linarith : e - 1 ≤ 19 / 4)
            have hW := hWlog.trans
              log_nineteen_fourths_lt_thirtynine_twentyfifths.le
            have harg : (33 / 8 : ℝ) ≤ e * (e - 1) / 6 := by nlinarith
            have hQlog := Real.strictMonoOn_log.monotoneOn
              (by norm_num : (0 : ℝ) < 33 / 8)
              (show (0 : ℝ) < e * (e - 1) / 6 by positivity) harg
            rw [hprodEq] at hQlog
            have hQ : (1417 / 1000 : ℝ) ≤
                Real.log e + Real.log (e - 1) - Real.log 6 :=
              log_thirtythree_eighths_gt_1417_thousandths.le.trans hQlog
            have hE := (Real.strictMonoOn_log.monotoneOn he0
              (by norm_num : (0 : ℝ) < 23 / 4) h5).trans
                log_twentythree_fourths_lt_seven_fourths.le
            have hmodel := gsSection61MidModel_lower_of_bounds
              (e := e) (X := (4 / 19 : ℝ)) (W := (39 / 25 : ℝ))
              (Q := (1417 / 1000 : ℝ)) (E := (7 / 4 : ℝ))
              he4 he6 (by norm_num) hX hW (by norm_num) (by norm_num) hQ hE
              (by norm_num)
            norm_num [gsTaylorFiveErrorLower] at hmodel ⊢
            linarith

          · have hlo5 : 23 / 4 ≤ e := le_of_not_ge h5
            have hX : (1 / 5 : ℝ) ≤ 1 / (e - 1) := by
              rw [le_div_iff₀ hem0]
              nlinarith
            have hWlog := Real.strictMonoOn_log.monotoneOn hem0
              (by norm_num : (0 : ℝ) < 5) (by linarith : e - 1 ≤ 5)
            have hW := hWlog.trans log_five_lt_161_hundredths.le
            have harg : (437 / 96 : ℝ) ≤ e * (e - 1) / 6 := by nlinarith
            have hQlog := Real.strictMonoOn_log.monotoneOn
              (by norm_num : (0 : ℝ) < 437 / 96)
              (show (0 : ℝ) < e * (e - 1) / 6 by positivity) harg
            rw [hprodEq] at hQlog
            have hQ : (303 / 200 : ℝ) ≤
                Real.log e + Real.log (e - 1) - Real.log 6 :=
              log_fourhundredthirtyseven_ninetysixths_gt_303_halves_hundredths.le.trans
                hQlog
            have hE := (Real.strictMonoOn_log.monotoneOn he0
              (by norm_num : (0 : ℝ) < 6) he6).trans log_six_lt_nine_fifths.le
            have hmodel := gsSection61MidModel_lower_of_bounds
              (e := e) (X := (1 / 5 : ℝ)) (W := (161 / 100 : ℝ))
              (Q := (303 / 200 : ℝ)) (E := (9 / 5 : ℝ))
              he4 he6 (by norm_num) hX hW (by norm_num) (by norm_num) hQ hE
              (by norm_num)
            norm_num [gsTaylorFiveErrorLower] at hmodel ⊢
            linarith

lemma dickmanRho_lt_gsSection61MidModel_four_six
    {e : ℝ} (he4 : 4 ≤ e) (he6 : e ≤ 6) :
    dickmanRho e < gsSection61MidModel e := by
  have hrho := antitoneOn_dickmanRho_Ici_zero
    (by norm_num : (0 : ℝ) ≤ 4) (by linarith : (0 : ℝ) ≤ e) he4
  have hmodel := one_hundredth_lt_gsSection61MidModel_four_six he4 he6
  linarith [dickmanRho_four_lt_one_hundredth]

/-- Scalar form of the degree-five paired estimate for `4 ≤ e ≤ 6`. -/
lemma section61_scalar_four_six
    {e a m : ℝ} (he4 : 4 ≤ e) (he6 : e ≤ 6)
    (haLower : e - 1 ≤ a) (haUpper : a ≤ e)
    (hmLower : Real.log e + Real.log (e - 1) - Real.log 6 ≤ m) :
    dickmanRho e ≤
      gsExpAlternatingSum (Real.log a) 5 +
          m ^ 6 / 720 * (1 - Real.log a / 7) -
        (Real.log e - Real.log a) := by
  exact (dickmanRho_lt_gsSection61MidModel_four_six he4 he6).le.trans
    (gsSection61MidModel_le_paired he4 he6 haLower haUpper hmLower)

/-- A reusable rational certificate for a lower bound on the explicit
low model.  It replaces each logarithm by a one-sided rational bound. -/
lemma gsSection61LowModel_lower_of_log_bounds
    {e W Q E : ℝ} (he3 : 3 ≤ e) (he4 : e ≤ 4)
    (hW0 : 0 ≤ W) (hW : W ≤ Real.log (e - 1))
    (hQ0 : 0 ≤ Q)
    (hQ : Q ≤ Real.log e + Real.log (e - 1) - Real.log 4)
    (hE : Real.log e ≤ E) (hE5 : E ≤ 5) :
    1 - E + W ^ 2 / 2 - W ^ 3 / 6 +
        Q ^ 4 / 24 * (1 - E / 5) ≤ gsSection61LowModel e := by
  let w : ℝ := Real.log (e - 1)
  let q : ℝ := Real.log e + Real.log (e - 1) - Real.log 4
  have he0 : 0 < e := by linarith
  have hem0 : 0 < e - 1 := by linarith
  have hw0 : 0 ≤ w := by
    dsimp only [w]
    exact Real.log_nonneg (by linarith)
  have hwe : w ≤ Real.log e := by
    dsimp only [w]
    exact Real.strictMonoOn_log.monotoneOn hem0 he0 (by linarith)
  have hlogE4 : Real.log e ≤ Real.log 4 :=
    Real.strictMonoOn_log.monotoneOn he0 (by norm_num) he4
  have hw2 : w ≤ 2 := hwe.trans (hlogE4.trans log_four_lt_two.le)
  have hW2 : W ≤ 2 := hW.trans hw2
  have hcross : w * W ≤ w + W := by
    by_cases hw1 : w ≤ 1
    · nlinarith [mul_le_mul_of_nonneg_right hw1 hW0]
    · have hmul := mul_le_mul_of_nonneg_left hW2 hw0
      nlinarith
  have hmain : W ^ 2 / 2 - W ^ 3 / 6 ≤
      w ^ 2 / 2 - w ^ 3 / 6 := by
    have hdiff : 0 ≤ w - W := by
      dsimp only [w]
      linarith
    have hwsq : w ^ 2 ≤ 2 * w := by
      nlinarith [mul_nonneg hw0 (sub_nonneg.mpr hw2)]
    have hWsq : W ^ 2 ≤ 2 * W := by
      nlinarith [mul_nonneg hW0 (sub_nonneg.mpr hW2)]
    have hbracket : 0 ≤
        3 * (w + W) - (w ^ 2 + w * W + W ^ 2) := by
      linarith
    nlinarith [mul_nonneg hdiff hbracket]
  have hqEq : q = Real.log (e * (e - 1) / 4) := by
    dsimp only [q]
    rw [Real.log_div (mul_ne_zero he0.ne' hem0.ne') (by norm_num),
      Real.log_mul he0.ne' hem0.ne']
  have harg : 1 ≤ e * (e - 1) / 4 := by nlinarith
  have hq0 : 0 ≤ q := by
    rw [hqEq]
    exact Real.log_nonneg harg
  have hpow : Q ^ 4 ≤ q ^ 4 := pow_le_pow_left₀ hQ0 hQ 4
  have hcoefLower : 0 ≤ 1 - E / 5 := by linarith
  have hcoef : 1 - E / 5 ≤ 1 - Real.log e / 5 := by linarith
  have hbonus : Q ^ 4 / 24 * (1 - E / 5) ≤
      q ^ 4 / 24 * (1 - Real.log e / 5) := by
    calc
      Q ^ 4 / 24 * (1 - E / 5) ≤
          q ^ 4 / 24 * (1 - E / 5) := by
            gcongr
      _ ≤ q ^ 4 / 24 * (1 - Real.log e / 5) := by
            exact mul_le_mul_of_nonneg_left hcoef (by positivity)
  dsimp only [gsSection61LowModel]
  dsimp only [w, q] at hmain hbonus ⊢
  linarith

lemma one_fortieth_lt_gsSection61LowModel_nineteen_fifths_four
    {e : ℝ} (heLower : 19 / 5 ≤ e) (heUpper : e ≤ 4) :
    (1 / 40 : ℝ) < gsSection61LowModel e := by
  have he0 : 0 < e := by linarith
  have hem0 : 0 < e - 1 := by linarith
  have hprodEq : Real.log (e * (e - 1) / 4) =
      Real.log e + Real.log (e - 1) - Real.log 4 := by
    rw [Real.log_div (mul_ne_zero he0.ne' hem0.ne') (by norm_num),
      Real.log_mul he0.ne' hem0.ne']
  by_cases hfirst : e ≤ 77 / 20
  · have hE : Real.log e ≤ (1349 / 1000 : ℝ) :=
      (Real.strictMonoOn_log.monotoneOn he0 (by norm_num) hfirst).trans
        log_seventyseven_twenty_lt_1349_div_1000.le
    have hWarg : (14 / 5 : ℝ) ≤ e - 1 := by linarith
    have hW : (1287 / 1250 : ℝ) ≤ Real.log (e - 1) :=
      log_fourteen_fifths_gt_1287_div_1250.le.trans
        (Real.strictMonoOn_log.monotoneOn (by norm_num) hem0 hWarg)
    have harg : (133 / 50 : ℝ) ≤ e * (e - 1) / 4 := by
      nlinarith
    have hQlog := Real.strictMonoOn_log.monotoneOn
      (by norm_num : (0 : ℝ) < 133 / 50)
      (show (0 : ℝ) < e * (e - 1) / 4 by positivity) harg
    rw [hprodEq] at hQlog
    have hQ : (9783 / 10000 : ℝ) ≤
        Real.log e + Real.log (e - 1) - Real.log 4 :=
      log_onehundredthirtythree_fifty_bounds.1.le.trans hQlog
    have hmodel := gsSection61LowModel_lower_of_log_bounds
      (e := e) (W := (1287 / 1250 : ℝ))
      (Q := (9783 / 10000 : ℝ)) (E := (1349 / 1000 : ℝ))
      (by linarith) heUpper (by norm_num) hW (by norm_num) hQ hE (by norm_num)
    norm_num at hmodel ⊢
    linarith
  · have heSecondLower : 77 / 20 ≤ e := le_of_not_ge hfirst
    by_cases hsecond : e ≤ 39 / 10
    · have hE : Real.log e ≤ (1361 / 1000 : ℝ) :=
        (Real.strictMonoOn_log.monotoneOn he0 (by norm_num) hsecond).trans
          log_thirtynine_ten_lt_1361_div_1000.le
      have hWarg : (57 / 20 : ℝ) ≤ e - 1 := by linarith
      have hW : (1047 / 1000 : ℝ) ≤ Real.log (e - 1) :=
        log_fiftyseven_twenty_gt_1047_div_1000.le.trans
          (Real.strictMonoOn_log.monotoneOn (by norm_num) hem0 hWarg)
      have harg : (4389 / 1600 : ℝ) ≤ e * (e - 1) / 4 := by
        nlinarith
      have hQlog := Real.strictMonoOn_log.monotoneOn
        (by norm_num : (0 : ℝ) < 4389 / 1600)
        (show (0 : ℝ) < e * (e - 1) / 4 by positivity) harg
      rw [hprodEq] at hQlog
      have hQ : (1 : ℝ) ≤
          Real.log e + Real.log (e - 1) - Real.log 4 :=
        one_lt_log_fourthousandeighthundredninetynine_sixteenhundred.le.trans
          hQlog
      have hmodel := gsSection61LowModel_lower_of_log_bounds
        (e := e) (W := (1047 / 1000 : ℝ))
        (Q := (1 : ℝ)) (E := (1361 / 1000 : ℝ))
        (by linarith) heUpper (by norm_num) hW (by norm_num) hQ hE
        (by norm_num)
      norm_num at hmodel ⊢
      linarith
    · have heThirdLower : 39 / 10 ≤ e := le_of_not_ge hsecond
      by_cases hthird : e ≤ 79 / 20
      · have hE : Real.log e ≤ (1374 / 1000 : ℝ) :=
          (Real.strictMonoOn_log.monotoneOn he0 (by norm_num) hthird).trans
            log_seventynine_twenty_lt_1374_div_1000.le
        have hWarg : (29 / 10 : ℝ) ≤ e - 1 := by linarith
        have hW : (1064 / 1000 : ℝ) ≤ Real.log (e - 1) :=
          log_twentynine_ten_gt_1064_div_1000.le.trans
            (Real.strictMonoOn_log.monotoneOn (by norm_num) hem0 hWarg)
        have harg : (1131 / 400 : ℝ) ≤ e * (e - 1) / 4 := by
          nlinarith
        have hQlog := Real.strictMonoOn_log.monotoneOn
          (by norm_num : (0 : ℝ) < 1131 / 400)
          (show (0 : ℝ) < e * (e - 1) / 4 by positivity) harg
        rw [hprodEq] at hQlog
        have hQ : (103 / 100 : ℝ) ≤
            Real.log e + Real.log (e - 1) - Real.log 4 :=
          log_onethousandonehundredthirtyone_fourhundred_gt_103_div_100.le.trans
            hQlog
        have hmodel := gsSection61LowModel_lower_of_log_bounds
          (e := e) (W := (1064 / 1000 : ℝ))
          (Q := (103 / 100 : ℝ)) (E := (1374 / 1000 : ℝ))
          (by linarith) heUpper (by norm_num) hW (by norm_num) hQ hE
          (by norm_num)
        norm_num at hmodel ⊢
        linarith
      · have heFourthLower : 79 / 20 ≤ e := le_of_not_ge hthird
        have hE : Real.log e ≤ (347 / 250 : ℝ) :=
          (Real.strictMonoOn_log.monotoneOn he0 (by norm_num) heUpper).trans
            log_four_lt_347_div_250.le
        have hWarg : (59 / 20 : ℝ) ≤ e - 1 := by linarith
        have hW : (1081 / 1000 : ℝ) ≤ Real.log (e - 1) :=
          log_fiftynine_twenty_gt_1081_div_1000.le.trans
            (Real.strictMonoOn_log.monotoneOn (by norm_num) hem0 hWarg)
        have harg : (4661 / 1600 : ℝ) ≤ e * (e - 1) / 4 := by
          nlinarith
        have hQlog := Real.strictMonoOn_log.monotoneOn
          (by norm_num : (0 : ℝ) < 4661 / 1600)
          (show (0 : ℝ) < e * (e - 1) / 4 by positivity) harg
        rw [hprodEq] at hQlog
        have hQ : (1069 / 1000 : ℝ) ≤
            Real.log e + Real.log (e - 1) - Real.log 4 :=
          log_fourthousandsixhundredsixtyone_sixteenhundred_gt_1069_div_1000.le.trans
            hQlog
        have hmodel := gsSection61LowModel_lower_of_log_bounds
          (e := e) (W := (1081 / 1000 : ℝ))
          (Q := (1069 / 1000 : ℝ)) (E := (347 / 250 : ℝ))
          (by linarith) heUpper (by norm_num) hW (by norm_num) hQ hE
          (by norm_num)
        norm_num at hmodel ⊢
        linarith

lemma dickmanRho_lt_gsSection61LowModel_three_nineteen_fifths
    {e : ℝ} (he3 : 3 ≤ e) (heUpper : e ≤ 19 / 5) :
    dickmanRho e < gsSection61LowModel e := by
  by_cases heFirst : e ≤ 7 / 2
  · have hmodel := gsSection61LowModel_antitone_three_seven_halves
      (show e ∈ Icc (3 : ℝ) (7 / 2) from ⟨he3, heFirst⟩)
      (show (7 / 2 : ℝ) ∈ Icc (3 : ℝ) (7 / 2) by norm_num)
      heFirst
    have hrho := antitoneOn_dickmanRho_Ici_zero
      (by norm_num : (0 : ℝ) ≤ 3)
      (by linarith : (0 : ℝ) ≤ e)
      he3
    linarith [dickmanRho_three_lt_one_twentieth,
      gsSection61LowModel_seven_halves_gt_one_twentieth]
  · have heLower : 7 / 2 ≤ e := le_of_not_ge heFirst
    have hmodel : gsSection61LowModel (19 / 5) ≤
        gsSection61LowModel e := by
      by_cases heMiddle : e ≤ 37 / 10
      · have hleft :=
          gsSection61LowModel_antitone_seven_halves_thirtyseven_tenths
            (show e ∈ Icc (7 / 2 : ℝ) (37 / 10) from
              ⟨heLower, heMiddle⟩)
            (show (37 / 10 : ℝ) ∈ Icc (7 / 2 : ℝ) (37 / 10) by
              norm_num)
            heMiddle
        have hright :=
          gsSection61LowModel_antitone_thirtyseven_tenths_nineteen_fifths
            (show (37 / 10 : ℝ) ∈ Icc (37 / 10 : ℝ) (19 / 5) by
              norm_num)
            (show (19 / 5 : ℝ) ∈ Icc (37 / 10 : ℝ) (19 / 5) by
              norm_num)
            (by norm_num)
        exact hright.trans hleft
      · have heLast : 37 / 10 ≤ e := le_of_not_ge heMiddle
        exact
          gsSection61LowModel_antitone_thirtyseven_tenths_nineteen_fifths
            (show e ∈ Icc (37 / 10 : ℝ) (19 / 5) from
              ⟨heLast, heUpper⟩)
            (show (19 / 5 : ℝ) ∈ Icc (37 / 10 : ℝ) (19 / 5) by
              norm_num)
            heUpper
    have hrho := antitoneOn_dickmanRho_Ici_zero
      (by norm_num : (0 : ℝ) ≤ 7 / 2)
      (by linarith : (0 : ℝ) ≤ e)
      heLower
    linarith [dickmanRho_seven_halves_lt_one_twentyfifth,
      gsSection61LowModel_nineteen_fifths_gt_one_twentyfifth]

lemma dickmanRho_lt_gsSection61LowModel_three_four
    {e : ℝ} (he3 : 3 ≤ e) (he4 : e ≤ 4) :
    dickmanRho e < gsSection61LowModel e := by
  by_cases he : e ≤ 19 / 5
  · exact dickmanRho_lt_gsSection61LowModel_three_nineteen_fifths he3 he
  · have heLower : 19 / 5 ≤ e := le_of_not_ge he
    have hrho := antitoneOn_dickmanRho_Ici_zero
      (by norm_num : (0 : ℝ) ≤ 19 / 5)
      (by linarith : (0 : ℝ) ≤ e)
      heLower
    have hmodel := one_fortieth_lt_gsSection61LowModel_nineteen_fifths_four
      heLower he4
    linarith [dickmanRho_nineteen_fifths_lt_one_fiftieth]

/-- Scalar form of the paired estimate for `3 ≤ e ≤ 4`. -/
lemma section61_scalar_three_four
    {e a m : ℝ} (he3 : 3 ≤ e) (he4 : e ≤ 4)
    (haLower : e - 1 ≤ a) (haUpper : a ≤ e)
    (hmLower : Real.log e + Real.log (e - 1) - Real.log 4 ≤ m) :
    dickmanRho e ≤
      gsExpAlternatingSum (Real.log a) 3 +
          m ^ 4 / 24 * (1 - Real.log a / 5) -
        (Real.log e - Real.log a) := by
  exact (dickmanRho_lt_gsSection61LowModel_three_four he3 he4).le.trans
    (gsSection61LowModel_le_paired he3 he4 haLower haUpper hmLower)

/-- Proposition 6.1 in the complete low-scale range `E(u) ≤ 4`. -/
theorem gs_proposition61_of_scale_le_four
    {chi sigma : ℝ → ℝ} (hchi : IsGSKernel chi)
    (hsigma : IsGSSolution chi sigma)
    {u : ℝ} (hu : 1 ≤ u) (hE2 : 2 < gsScale chi u)
    (hlarge : gsScale chi u - 1 <
      gsScale chi (u / gsScale chi u))
    (hE4 : gsScale chi u ≤ 4) :
    dickmanRho (gsScale chi u) ≤ sigma u := by
  let e : ℝ := gsScale chi u
  let u0 : ℝ := u / e
  let a : ℝ := gsScale chi u0
  have he0 : 0 < e := by
    dsimp only [e]
    exact gsScale_pos chi u
  have he1 : 1 ≤ e := by linarith
  have heu : e * u0 = u := by
    dsimp only [u0]
    field_simp [he0.ne']
  have heLeU : e ≤ u := by
    dsimp only [e]
    exact gsScale_le_self hchi hu
  have hu0 : 1 ≤ u0 := by
    dsimp only [u0]
    rw [le_div_iff₀ he0]
    simpa using heLeU
  have hu00 : 0 ≤ u0 := zero_le_one.trans hu0
  have hu0u : u0 ≤ u := by
    rw [← heu]
    nlinarith [mul_nonneg (sub_nonneg.mpr he1) hu00]
  have ha0 : 0 < a := by
    dsimp only [a]
    exact gsScale_pos chi u0
  have haUpper : a ≤ e := by
    dsimp only [a, e]
    exact gsScale_mono hchi hu0 hu hu0u
  have haLeU0 : a ≤ u0 := by
    dsimp only [a]
    exact gsScale_le_self hchi hu0
  have haLower : e - 1 ≤ a := by
    dsimp only [e, a, u0] at hlarge ⊢
    exact hlarge.le
  have hlogE : Real.log e = gsLogScale chi u := by
    dsimp only [e, gsScale]
    rw [Real.log_exp]
  have hlogA : Real.log a = gsLogScale chi u0 := by
    dsimp only [a, gsScale]
    rw [Real.log_exp]
  have hfit : (((2 * 1 : ℕ) : ℝ) * u0) ≤ u := by
    norm_num
    rw [← heu]
    nlinarith
  by_cases he3 : e ≤ 3
  · have hscalar := section61_scalar_two_three
      (e := e) (a := a) hE2.le he3 haLower haUpper
    have hperturb := gs_fill_exp_perturb_lower hchi hsigma hu0 hu0u hu 1 hfit
    rw [← hlogA, ← hlogE] at hperturb
    exact hscalar.trans hperturb
  · have he3' : 3 ≤ e := le_of_not_ge he3
    have he4 : e ≤ 4 := by
      dsimp only [e]
      exact hE4
    let y : ℝ := u / 4
    have hu0Lower : 2 ≤ u0 := by linarith
    have heuLower : (6 : ℝ) ≤ e * u0 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr he3')
        (sub_nonneg.mpr hu0Lower)]
    have hy : 1 ≤ y := by
      dsimp only [y]
      rw [← heu]
      nlinarith
    have hyfit : (((2 * 1 + 2 : ℕ) : ℝ) * y) ≤ u := by
      dsimp only [y]
      norm_num
      ring_nf
      exact le_rfl
    have hyu0 : y ≤ u0 := by
      dsimp only [y]
      rw [← heu]
      nlinarith [mul_nonneg (sub_nonneg.mpr he4) hu00]
    have hz : gsLogScale chi u0 ≤ (((2 * 1 + 3 : ℕ) : ℝ)) := by
      rw [← hlogA]
      have hlog := Real.strictMonoOn_log.monotoneOn ha0 he0 haUpper
      have hlogE2 : Real.log e ≤ 2 := by
        have hlogE4 : Real.log e ≤ Real.log 4 :=
          Real.strictMonoOn_log.monotoneOn he0 (by norm_num) he4
        exact hlogE4.trans log_four_lt_two.le
      norm_num
      linarith
    have hmoment := gsMoment_one_ge_log_scale_ratio hchi hy hyu0
    rw [gsMoment_one chi hy] at hmoment
    have hyEq : y = e * u0 / 4 := by
      dsimp only [y]
      rw [← heu]
    have hratio : a * y / u0 = a * e / 4 := by
      rw [hyEq]
      field_simp [(zero_lt_one.trans_le hu0).ne']
    rw [hratio] at hmoment
    rw [← gsLogScale_gsFillAbove_of_le chi hy hyu0] at hmoment
    have hlogProd : Real.log (a * e / 4) =
        Real.log e + Real.log a - Real.log 4 := by
      rw [Real.log_div (mul_ne_zero ha0.ne' he0.ne') (by norm_num),
        Real.log_mul ha0.ne' he0.ne']
      ring
    rw [hlogProd] at hmoment
    have hlogLower : Real.log (e - 1) ≤ Real.log a :=
      Real.strictMonoOn_log.monotoneOn
        (show (0 : ℝ) < e - 1 by linarith) ha0 haLower
    have hmLower : Real.log e + Real.log (e - 1) - Real.log 4 ≤
        gsLogScale (gsFillAbove chi u0) y := by
      linarith
    have hscalar := section61_scalar_three_four
      he3' he4 haLower haUpper hmLower
    have hperturb := gs_fill_paired_logScale_lower hchi hsigma hu0 hu0u hu
      hy 1 hfit hyfit hz
    rw [← hlogA, ← hlogE] at hperturb
    norm_num at hperturb
    apply hscalar.trans
    linarith

/-- Proposition 6.1 throughout the range `E(u) ≤ 6`. -/
theorem gs_proposition61_of_scale_le_six
    {chi sigma : ℝ → ℝ} (hchi : IsGSKernel chi)
    (hsigma : IsGSSolution chi sigma)
    {u : ℝ} (hu : 1 ≤ u) (hE2 : 2 < gsScale chi u)
    (hlarge : gsScale chi u - 1 <
      gsScale chi (u / gsScale chi u))
    (hE6 : gsScale chi u ≤ 6) :
    dickmanRho (gsScale chi u) ≤ sigma u := by
  by_cases hE4 : gsScale chi u ≤ 4
  · exact gs_proposition61_of_scale_le_four hchi hsigma hu hE2 hlarge hE4
  · let e : ℝ := gsScale chi u
    let u0 : ℝ := u / e
    let a : ℝ := gsScale chi u0
    have he0 : 0 < e := by
      dsimp only [e]
      exact gsScale_pos chi u
    have he4 : 4 ≤ e := by
      dsimp only [e]
      exact le_of_not_ge hE4
    have he6 : e ≤ 6 := by
      dsimp only [e]
      exact hE6
    have heu : e * u0 = u := by
      dsimp only [u0]
      field_simp [he0.ne']
    have heLeU : e ≤ u := by
      dsimp only [e]
      exact gsScale_le_self hchi hu
    have hu0 : 1 ≤ u0 := by
      dsimp only [u0]
      rw [le_div_iff₀ he0]
      simpa using heLeU
    have hu00 : 0 ≤ u0 := zero_le_one.trans hu0
    have hu0u : u0 ≤ u := by
      rw [← heu]
      nlinarith [mul_nonneg (sub_nonneg.mpr (by linarith : 1 ≤ e)) hu00]
    have ha0 : 0 < a := by
      dsimp only [a]
      exact gsScale_pos chi u0
    have haUpper : a ≤ e := by
      dsimp only [a, e]
      exact gsScale_mono hchi hu0 hu hu0u
    have haLeU0 : a ≤ u0 := by
      dsimp only [a]
      exact gsScale_le_self hchi hu0
    have haLower : e - 1 ≤ a := by
      dsimp only [e, a, u0] at hlarge ⊢
      exact hlarge.le
    have hlogE : Real.log e = gsLogScale chi u := by
      dsimp only [e, gsScale]
      rw [Real.log_exp]
    have hlogA : Real.log a = gsLogScale chi u0 := by
      dsimp only [a, gsScale]
      rw [Real.log_exp]
    have hfit : (((2 * 2 : ℕ) : ℝ) * u0) ≤ u := by
      norm_num
      rw [← heu]
      nlinarith [mul_nonneg (sub_nonneg.mpr he4) hu00]
    let y : ℝ := u / 6
    have hu0Lower : 3 ≤ u0 := by linarith
    have heuLower : (12 : ℝ) ≤ e * u0 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr he4)
        (sub_nonneg.mpr hu0Lower)]
    have hy : 1 ≤ y := by
      dsimp only [y]
      rw [← heu]
      nlinarith
    have hyfit : (((2 * 2 + 2 : ℕ) : ℝ) * y) ≤ u := by
      dsimp only [y]
      norm_num
      ring_nf
      exact le_rfl
    have hyu0 : y ≤ u0 := by
      dsimp only [y]
      rw [← heu]
      nlinarith [mul_nonneg (sub_nonneg.mpr he6) hu00]
    have hz : gsLogScale chi u0 ≤ (((2 * 2 + 3 : ℕ) : ℝ)) := by
      rw [← hlogA]
      have hlog := Real.strictMonoOn_log.monotoneOn ha0 he0 haUpper
      have hlogE2 : Real.log e ≤ 2 := by
        have hlogE6 : Real.log e ≤ Real.log 6 :=
          Real.strictMonoOn_log.monotoneOn he0 (by norm_num) he6
        exact hlogE6.trans log_six_lt_two.le
      norm_num
      linarith
    have hmoment := gsMoment_one_ge_log_scale_ratio hchi hy hyu0
    rw [gsMoment_one chi hy] at hmoment
    have hyEq : y = e * u0 / 6 := by
      dsimp only [y]
      rw [← heu]
    have hratio : a * y / u0 = a * e / 6 := by
      rw [hyEq]
      field_simp [(zero_lt_one.trans_le hu0).ne']
    rw [hratio] at hmoment
    rw [← gsLogScale_gsFillAbove_of_le chi hy hyu0] at hmoment
    have hlogProd : Real.log (a * e / 6) =
        Real.log e + Real.log a - Real.log 6 := by
      rw [Real.log_div (mul_ne_zero ha0.ne' he0.ne') (by norm_num),
        Real.log_mul ha0.ne' he0.ne']
      ring
    rw [hlogProd] at hmoment
    have hlogLower : Real.log (e - 1) ≤ Real.log a :=
      Real.strictMonoOn_log.monotoneOn
        (show (0 : ℝ) < e - 1 by linarith) ha0 haLower
    have hmLower : Real.log e + Real.log (e - 1) - Real.log 6 ≤
        gsLogScale (gsFillAbove chi u0) y := by
      linarith
    have hscalar := section61_scalar_four_six
      he4 he6 haLower haUpper hmLower
    have hperturb := gs_fill_paired_logScale_lower hchi hsigma hu0 hu0u hu
      hy 2 hfit hyfit hz
    rw [← hlogA, ← hlogE] at hperturb
    norm_num at hperturb
    apply hscalar.trans
    linarith

lemma exp_neg_sub_odd_sum_le_alt
    {z : ℝ} (hz : 0 ≤ z) (r : ℕ)
    (hzUpper : z ≤ (2 * r + 3 : ℕ)) :
    Real.exp (-z) - gsExpAlternatingSum z (2 * r + 1) ≤
      z ^ (2 * r + 2) / (2 * r + 2).factorial := by
  let N : ℕ := 2 * r + 2
  let f : ℕ → ℝ := fun k => z ^ (k + N) / (k + N).factorial
  have hfull : HasSum (fun k : ℕ => (-z) ^ k / k.factorial) (Real.exp (-z)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (-z)
  have htail : HasSum (fun k : ℕ => (-z) ^ (k + N) / (k + N).factorial)
      (Real.exp (-z) - ∑ j ∈ Finset.range N, (-z) ^ j / j.factorial) := by
    apply (hasSum_nat_add_iff (f := fun j : ℕ =>
      (-z) ^ j / j.factorial) N).2
    simpa only [sub_add_cancel] using hfull
  have hanti : Antitone f := by
    apply antitone_nat_of_succ_le
    intro k
    have hden : (0 : ℝ) < (k + N + 1 : ℕ) := by positivity
    have hzden : z ≤ (k + N + 1 : ℕ) := by
      have hNat : 2 * r + 3 ≤ k + N + 1 := by
        dsimp only [N]
        omega
      exact hzUpper.trans (by exact_mod_cast hNat)
    have hratio : z / (k + N + 1 : ℕ) ≤ (1 : ℝ) :=
      (div_le_one hden).2 hzden
    have hbase : 0 ≤ z ^ (k + N) / (k + N).factorial := by positivity
    dsimp only [f]
    rw [show k + 1 + N = (k + N) + 1 by omega,
      pow_succ', Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    calc
      z * z ^ (k + N) /
          ((((k + N : ℕ) : ℝ) + 1) *
            (((k + N).factorial : ℕ) : ℝ)) =
          (z ^ (k + N) / (k + N).factorial) *
            (z / (k + N + 1 : ℕ)) := by
              simp only [Nat.cast_add, Nat.cast_one]
              field_simp
      _ ≤ (z ^ (k + N) / (k + N).factorial) * 1 := by
        apply mul_le_mul_of_nonneg_left _ hbase
        simpa [Nat.cast_add, Nat.cast_one] using hratio
      _ = z ^ (k + N) / (k + N).factorial := by ring
  have hfl : Filter.Tendsto
      (fun n => ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * f k)
      Filter.atTop
      (nhds (Real.exp (-z) - ∑ j ∈ Finset.range N,
        (-z) ^ j / j.factorial)) := by
    apply HasSum.tendsto_sum_nat
    convert htail using 1
    funext k
    dsimp only [f, N]
    have heven : (-1 : ℝ) ^ (2 * r + 2) = 1 := by
      rw [show 2 * r + 2 = 2 * (r + 1) by omega, pow_mul]
      norm_num
    rw [show (-z) ^ (k + (2 * r + 2)) =
        (-1 : ℝ) ^ (k + (2 * r + 2)) * z ^ (k + (2 * r + 2)) by
      rw [neg_pow]]
    rw [show (-1 : ℝ) ^ (k + (2 * r + 2)) =
        (-1 : ℝ) ^ k * (-1 : ℝ) ^ (2 * r + 2) by rw [pow_add], heven]
    ring
  have hbound := hanti.tendsto_le_alternating_series hfl 0
  simp only [mul_zero, zero_add, Finset.sum_range_one, pow_zero, one_mul] at hbound
  dsimp only [f] at hbound
  have hsum : (∑ j ∈ Finset.range N, (-z) ^ j / j.factorial) =
      gsExpAlternatingSum z (2 * r + 1) := by
    dsimp only [N]
    unfold gsExpAlternatingSum
    apply Finset.sum_congr (by congr 1 <;> omega)
    intro j hj
    rw [neg_pow]
  rw [hsum] at hbound
  simpa [N, add_comm] using hbound

def testLogSqrtGap (x : ℝ) : ℝ :=
  3 / 4 * Real.sqrt x - Real.log x

lemma hasDerivAt_logSqrtGap {x : ℝ} (hx : 0 < x) :
    HasDerivAt testLogSqrtGap
      (3 / 4 * (1 / (2 * Real.sqrt x)) - 1 / x) x := by
  exact ((Real.hasDerivAt_sqrt hx.ne').const_mul (3 / 4)).sub
    (by simpa only [one_div] using Real.hasDerivAt_log hx.ne')

lemma logSqrtGap_monotone : MonotoneOn testLogSqrtGap (Set.Ici (10 : ℝ)) := by
  apply monotoneOn_of_deriv_nonneg
    (convex_Ici (10 : ℝ) : Convex ℝ (Set.Ici (10 : ℝ)))
  · intro x hx
    have hxle : (10 : ℝ) ≤ x := hx
    exact (hasDerivAt_logSqrtGap (by linarith)).continuousAt.continuousWithinAt
  · intro x hx
    have hxle : (10 : ℝ) ≤ x := (interior_subset hx : x ∈ Set.Ici (10 : ℝ))
    exact (hasDerivAt_logSqrtGap (by linarith)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx10 : (10 : ℝ) < x := hx
    have hx0 : 0 < x := by linarith
    have hspos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
    have hs31 : (31 / 10 : ℝ) < Real.sqrt x := by
      rw [Real.lt_sqrt (by norm_num)]
      nlinarith
    have hcross : (8 : ℝ) * Real.sqrt x ≤ 3 * x := by
      nlinarith [Real.sq_sqrt hx0.le]
    have hfrac : 1 / x ≤ (3 : ℝ) / (8 * Real.sqrt x) := by
      rw [div_le_div_iff₀ hx0 (by positivity)]
      simpa using hcross
    have hder := (hasDerivAt_logSqrtGap hx0).deriv
    rw [hder]
    have heq : (3 / 4 : ℝ) * (1 / (2 * Real.sqrt x)) =
        3 / (8 * Real.sqrt x) := by field_simp; ring
    rw [heq]
    linarith

lemma log_le_three_fourths_sqrt {x : ℝ} (hx : 10 ≤ x) :
    Real.log x ≤ 3 / 4 * Real.sqrt x := by
  have hsqrt10 : (31 / 10 : ℝ) < Real.sqrt 10 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hlog10 : Real.log 10 < (2303 / 1000 : ℝ) := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have hbase : 0 ≤ testLogSqrtGap 10 := by
    dsimp only [testLogSqrtGap]
    nlinarith
  have hmono := logSqrtGap_monotone
    (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  dsimp only [testLogSqrtGap] at hmono
  linarith

def testFactorialMajorant (r : ℕ) : ℝ :=
  (3 / 4 : ℝ) ^ (2 * r + 2) * (2 * r + 2 : ℕ) ^ (r + 1) /
    (2 * r).factorial

lemma factorialMajorant_succ_le {r : ℕ} (hr : 4 ≤ r) :
    testFactorialMajorant (r + 1) ≤ testFactorialMajorant r := by
  let R : ℝ := (9 / 16 : ℝ) *
    ((2 * r + 4 : ℕ) : ℝ) ^ (r + 2) /
      (((2 * r + 2 : ℕ) : ℝ) ^ (r + 1) *
        ((2 * r + 2 : ℕ) : ℝ) * ((2 * r + 1 : ℕ) : ℝ))
  have hpow : (1 + ((r + 1 : ℕ) : ℝ)⁻¹) ^ (r + 1) ≤ 3 :=
    (Real.one_add_inv_pow_le_exp (n := r + 1)).trans Real.exp_one_lt_three.le
  have hbaseEq : (1 + ((r + 1 : ℕ) : ℝ)⁻¹) *
      ((2 * r + 2 : ℕ) : ℝ) = ((2 * r + 4 : ℕ) : ℝ) := by
    norm_num [Nat.cast_add, Nat.cast_mul]
    field_simp
    ring
  have hpower : ((2 * r + 4 : ℕ) : ℝ) ^ (r + 1) ≤
      3 * ((2 * r + 2 : ℕ) : ℝ) ^ (r + 1) := by
    have hscale := mul_le_mul_of_nonneg_right hpow
      (show 0 ≤ ((2 * r + 2 : ℕ) : ℝ) ^ (r + 1) by positivity)
    rw [← mul_pow, hbaseEq] at hscale
    exact hscale
  have hden : (0 : ℝ) <
      (((2 * r + 2 : ℕ) : ℝ) ^ (r + 1) *
        ((2 * r + 2 : ℕ) : ℝ) * ((2 * r + 1 : ℕ) : ℝ)) := by positivity
  have hR0 : 0 ≤ R := by positivity
  have hR1 : R ≤ 1 := by
    dsimp only [R]
    rw [div_le_one hden]
    have hscalar : (9 / 16 : ℝ) * 3 * ((2 * r + 4 : ℕ) : ℝ) ≤
        ((2 * r + 2 : ℕ) : ℝ) * ((2 * r + 1 : ℕ) : ℝ) := by
      have hrReal : (4 : ℝ) ≤ r := by exact_mod_cast hr
      norm_num [Nat.cast_add, Nat.cast_mul] at ⊢
      nlinarith
    calc
      (9 / 16 : ℝ) * ((2 * r + 4 : ℕ) : ℝ) ^ (r + 2) =
          (9 / 16 : ℝ) * ((2 * r + 4 : ℕ) : ℝ) ^ (r + 1) *
            ((2 * r + 4 : ℕ) : ℝ) := by rw [pow_succ]
              <;> ring
      _ ≤ (9 / 16 : ℝ) *
          (3 * ((2 * r + 2 : ℕ) : ℝ) ^ (r + 1)) *
            ((2 * r + 4 : ℕ) : ℝ) := by gcongr
      _ ≤ ((2 * r + 2 : ℕ) : ℝ) ^ (r + 1) *
          (((2 * r + 2 : ℕ) : ℝ) * ((2 * r + 1 : ℕ) : ℝ)) := by
            have hnonneg : 0 ≤ ((2 * r + 2 : ℕ) : ℝ) ^ (r + 1) := by positivity
            have hmul := mul_le_mul_of_nonneg_left hscalar hnonneg
            nlinarith
      _ = ((2 * r + 2 : ℕ) : ℝ) ^ (r + 1) *
          ((2 * r + 2 : ℕ) : ℝ) * ((2 * r + 1 : ℕ) : ℝ) := by ring
  have hEq : testFactorialMajorant (r + 1) =
      testFactorialMajorant r * R := by
    dsimp only [testFactorialMajorant, R]
    rw [show 2 * (r + 1) + 2 = (2 * r + 2) + 2 by omega,
      show r + 1 + 1 = (r + 1) + 1 by omega,
      show 2 * (r + 1) = (2 * r) + 2 by omega,
      pow_add, pow_succ,
      Nat.factorial_succ, Nat.factorial_succ]
    norm_num [Nat.cast_add, Nat.cast_mul]
    field_simp
    ring
  rw [hEq]
  apply mul_le_of_le_one_right
  · dsimp only [testFactorialMajorant]
    positivity
  · exact hR1

lemma factorialMajorant_le_base {r : ℕ} (hr : 4 ≤ r) :
    testFactorialMajorant r ≤ testFactorialMajorant 4 := by
  induction r, hr using Nat.le_induction with
  | base => exact le_rfl
  | succ r hr ih => exact (factorialMajorant_succ_le hr).trans ih

lemma log_power_div_factorial_le
    {r : ℕ} (hr : 3 ≤ r) :
    Real.log ((2 * r + 2 : ℕ) : ℝ) ^ (2 * r + 2) /
        (2 * r).factorial ≤ (243 / 500 : ℝ) := by
  rcases hr.eq_or_lt with rfl | hr4
  · have hlog8 : Real.log 8 ≤ (41589 / 20000 : ℝ) := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      linarith [log_two_lt_13863_div_20000]
    have hlog0 : 0 ≤ Real.log (8 : ℝ) := Real.log_nonneg (by norm_num)
    have hp := pow_le_pow_left₀ hlog0 hlog8 (2 * 3 + 2)
    have hp8 : Real.log (8 : ℝ) ^ 8 ≤ (41589 / 20000 : ℝ) ^ 8 := by
      convert hp using 1 <;> norm_num
    have hpdiv : Real.log (8 : ℝ) ^ 8 / 720 ≤
        (41589 / 20000 : ℝ) ^ 8 / 720 := by
      exact div_le_div_of_nonneg_right hp8 (by norm_num)
    norm_num
    exact hpdiv.trans (by norm_num)
  · have hr4' : 4 ≤ r := by omega
    let x : ℝ := (2 * r + 2 : ℕ)
    have hx10 : 10 ≤ x := by
      have hNat : 10 ≤ 2 * r + 2 := by omega
      dsimp only [x]
      exact_mod_cast hNat
    have hlog := log_le_three_fourths_sqrt hx10
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have hp := pow_le_pow_left₀ hlog0 hlog (2 * r + 2)
    have hsqrtpow : Real.sqrt x ^ (2 * r + 2) = x ^ (r + 1) := by
      rw [show 2 * r + 2 = 2 * (r + 1) by omega, pow_mul,
        Real.sq_sqrt (by positivity)]
    have hmaj : Real.log x ^ (2 * r + 2) / (2 * r).factorial ≤
        testFactorialMajorant r := by
      dsimp only [testFactorialMajorant]
      rw [mul_pow, hsqrtpow] at hp
      exact div_le_div_of_nonneg_right hp (by positivity)
    calc
      Real.log ((2 * r + 2 : ℕ) : ℝ) ^ (2 * r + 2) /
          (2 * r).factorial = Real.log x ^ (2 * r + 2) /
            (2 * r).factorial := by rfl
      _ ≤ testFactorialMajorant r := hmaj
      _ ≤ testFactorialMajorant 4 := factorialMajorant_le_base hr4'
      _ ≤ (243 / 500 : ℝ) := by norm_num [testFactorialMajorant]

lemma one_div_add_log_mono
    {b a : ℝ} (hb1 : 1 ≤ b) (hba : b ≤ a) :
    1 / b + Real.log b ≤ 1 / a + Real.log a := by
  have hb0 : 0 < b := zero_lt_one.trans_le hb1
  have ha0 : 0 < a := hb0.trans_le hba
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos ha0 hb0)
  have hlogEq : Real.log (a / b) = Real.log a - Real.log b := by
    rw [Real.log_div ha0.ne' hb0.ne']
  have hinvEq : (a / b)⁻¹ = b / a := by field_simp
  rw [hlogEq, hinvEq] at hlog
  have hrecip : 1 / b - 1 / a ≤ 1 - b / a := by
    have hleft : 1 / b - 1 / a = (a - b) / (a * b) := by
      field_simp [ha0.ne', hb0.ne']
    have hright : 1 - b / a = (a - b) / a := by
      field_simp [ha0.ne']
    rw [hleft, hright, div_le_div_iff₀ (mul_pos ha0 hb0) ha0]
    nlinarith [mul_nonneg (sub_nonneg.mpr hba) (sub_nonneg.mpr hb1)]
  linarith

lemma endpoint_loss
    {e : ℝ} (he6 : 6 ≤ e) :
    1 / (e - 1) + Real.log (e - 1) - Real.log e ≥
      1 / (2 * e * (e - 1)) := by
  let x : ℝ := 1 / (e - 1)
  have hem0 : 0 < e - 1 := by linarith
  have he0 : 0 < e := by linarith
  have hx0 : 0 ≤ x := by dsimp only [x]; positivity
  have hx5 : x ≤ 1 / 5 := by
    dsimp only [x]
    rw [div_le_div_iff₀ hem0 (by norm_num)]
    nlinarith
  have hlog := log_one_add_le_cubic hx0
  have hpoly : x ^ 2 / (2 * (1 + x)) ≤ x ^ 2 / 2 - x ^ 3 / 3 := by
    have hden : 0 < 2 * (1 + x) := by positivity
    rw [div_le_iff₀ hden]
    have hfac : 0 ≤ x ^ 3 * (1 - 2 * x) :=
      mul_nonneg (by positivity) (by linarith)
    nlinarith
  have hlogEq : Real.log e - Real.log (e - 1) = Real.log (1 + x) := by
    rw [← Real.log_div he0.ne' hem0.ne']
    congr 1
    dsimp only [x]
    field_simp [hem0.ne']
    ring
  have hratEq : 1 / (2 * e * (e - 1)) = x ^ 2 / (2 * (1 + x)) := by
    dsimp only [x]
    field_simp [he0.ne', hem0.ne']
    ring
  rw [← hlogEq] at hlog
  rw [← hratEq] at hpoly
  dsimp only [x] at hlog hpoly
  nlinarith

lemma loss_lower
    {e a : ℝ} (he6 : 6 ≤ e) (haLower : e - 1 ≤ a) :
    1 / a - (Real.log e - Real.log a) ≥
      1 / (2 * e * (e - 1)) := by
  have hmono := one_div_add_log_mono (b := e - 1) (a := a)
    (by linarith) haLower
  have hend := endpoint_loss he6
  linarith

lemma dickmanRho_quarter_step
    {a c0 c1 c2 c3 : ℝ} (ha0 : 0 ≤ a)
    (h0 : dickmanRho a ≤ c0)
    (h1 : dickmanRho (a + 1 / 4) ≤ c1)
    (h2 : dickmanRho (a + 1 / 2) ≤ c2)
    (h3 : dickmanRho (a + 3 / 4) ≤ c3) :
    4 * (a + 1) * dickmanRho (a + 1) ≤ c0 + c1 + c2 + c3 := by
  have hA := integral_dickmanRho_le_const_of_antitone ha0
    (show a ≤ a + 1 / 4 by norm_num) h0
  have hB := integral_dickmanRho_le_const_of_antitone
    (show 0 ≤ a + 1 / 4 by linarith)
    (show a + 1 / 4 ≤ a + 1 / 2 by norm_num) h1
  have hC := integral_dickmanRho_le_const_of_antitone
    (show 0 ≤ a + 1 / 2 by linarith)
    (show a + 1 / 2 ≤ a + 3 / 4 by norm_num) h2
  have hD := integral_dickmanRho_le_const_of_antitone
    (show 0 ≤ a + 3 / 4 by linarith)
    (show a + 3 / 4 ≤ a + 1 by norm_num) h3
  have hIntA : IntervalIntegrable dickmanRho volume a (a + 1 / 4) :=
    intervalIntegrable_dickmanRho_of_nonneg ha0 (by linarith)
  have hIntB : IntervalIntegrable dickmanRho volume (a + 1 / 4) (a + 1 / 2) :=
    intervalIntegrable_dickmanRho_of_nonneg (by linarith) (by linarith)
  have hIntC : IntervalIntegrable dickmanRho volume (a + 1 / 2) (a + 3 / 4) :=
    intervalIntegrable_dickmanRho_of_nonneg (by linarith) (by linarith)
  have hIntD : IntervalIntegrable dickmanRho volume (a + 3 / 4) (a + 1) :=
    intervalIntegrable_dickmanRho_of_nonneg (by linarith) (by linarith)
  have hIntAB : IntervalIntegrable dickmanRho volume a (a + 1 / 2) :=
    intervalIntegrable_dickmanRho_of_nonneg ha0 (by linarith)
  have hIntABC : IntervalIntegrable dickmanRho volume a (a + 3 / 4) :=
    intervalIntegrable_dickmanRho_of_nonneg ha0 (by linarith)
  have hsplitAB := intervalIntegral.integral_add_adjacent_intervals hIntA hIntB
  have hsplitABC := intervalIntegral.integral_add_adjacent_intervals hIntAB hIntC
  have hsplitABCD := intervalIntegral.integral_add_adjacent_intervals hIntABC hIntD
  have htotal : (∫ t : ℝ in a..(a + 1), dickmanRho t) =
      (∫ t : ℝ in a..(a + 1 / 4), dickmanRho t) +
      (∫ t : ℝ in (a + 1 / 4)..(a + 1 / 2), dickmanRho t) +
      (∫ t : ℝ in (a + 1 / 2)..(a + 3 / 4), dickmanRho t) +
      (∫ t : ℝ in (a + 3 / 4)..(a + 1), dickmanRho t) := by
    calc
      _ = (∫ t : ℝ in a..(a + 3 / 4), dickmanRho t) +
          ∫ t : ℝ in (a + 3 / 4)..(a + 1), dickmanRho t := hsplitABCD.symm
      _ = ((∫ t : ℝ in a..(a + 1 / 2), dickmanRho t) +
          ∫ t : ℝ in (a + 1 / 2)..(a + 3 / 4), dickmanRho t) +
          ∫ t : ℝ in (a + 3 / 4)..(a + 1), dickmanRho t := by rw [hsplitABC]
      _ = _ := by rw [hsplitAB]
  have hdelay := dickmanRho_profile.2.2.2.2 (a + 1) (by linarith)
  rw [show a + 1 - 1 = a by ring] at hdelay
  rw [htotal] at hdelay
  norm_num at hA hB hC hD
  nlinarith

lemma log_nine_fourths_gt :
    (8109 / 10000 : ℝ) < Real.log (9 / 4) := by
  have h := logAtanhPartial_le_log_of_eq
    (q := (9 / 4 : ℝ)) (x := (5 / 13 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 8
  norm_num [logAtanhPartial] at h ⊢
  linarith

lemma log_five_fourths_lt :
    Real.log (5 / 4) < (2232 / 10000 : ℝ) := by
  have h := log_le_logAtanhUpper_of_eq
    (q := (5 / 4 : ℝ)) (x := (1 / 9 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 5
  norm_num [logAtanhPartial, logAtanhUpper] at h ⊢
  linarith

lemma log_eleven_fourths_gt :
    (2529 / 2500 : ℝ) < Real.log (11 / 4) := by
  have h := logAtanhPartial_le_log_of_eq
    (q := (11 / 4 : ℝ)) (x := (7 / 15 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 10
  norm_num [logAtanhPartial] at h ⊢
  linarith

lemma log_seven_fourths_lt :
    Real.log (7 / 4) < (5597 / 10000 : ℝ) := by
  have h := log_le_logAtanhUpper_of_eq
    (q := (7 / 4 : ℝ)) (x := (3 / 11 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 7
  norm_num [logAtanhPartial, logAtanhUpper] at h ⊢
  linarith

lemma dickmanRho_nine_fourths_lt :
    dickmanRho (9 / 4) < (203 / 1000 : ℝ) := by
  have h := dickmanRho_le_refined_two_three
    (e := (9 / 4 : ℝ)) (by norm_num) (by norm_num)
  have hw0 : 0 ≤ Real.log (5 / 4) := Real.log_nonneg (by norm_num)
  have hw2 := pow_le_pow_left₀ hw0 log_five_fourths_lt.le 2
  have hw3 := pow_le_pow_left₀ hw0 log_five_fourths_lt.le 3
  norm_num at h ⊢
  nlinarith [log_nine_fourths_gt, hw2, hw3]

lemma dickmanRho_five_halves_lt :
    dickmanRho (5 / 2) < (131 / 1000 : ℝ) := by
  have h := dickmanRho_le_refined_two_three
    (e := (5 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hw0 : 0 ≤ Real.log (3 / 2) := Real.log_nonneg (by norm_num)
  have hw2 := pow_le_pow_left₀ hw0 log_three_halves_bounds.2.le 2
  have hw3 := pow_le_pow_left₀ hw0 log_three_halves_bounds.2.le 3
  norm_num at h ⊢
  nlinarith [log_five_halves_gt_4581_div_5000, hw2, hw3]

lemma dickmanRho_eleven_fourths_lt :
    dickmanRho (11 / 4) < (82 / 1000 : ℝ) := by
  have h := dickmanRho_le_refined_two_three
    (e := (11 / 4 : ℝ)) (by norm_num) (by norm_num)
  have hw0 : 0 ≤ Real.log (7 / 4) := Real.log_nonneg (by norm_num)
  have hw2 := pow_le_pow_left₀ hw0 log_seven_fourths_lt.le 2
  have hw3 := pow_le_pow_left₀ hw0 log_seven_fourths_lt.le 3
  norm_num at h ⊢
  nlinarith [log_eleven_fourths_gt, hw2, hw3]

lemma dickmanRho_thirteen_fourths_lt :
    dickmanRho (13 / 4) < (9 / 250 : ℝ) := by
  have h := dickmanRho_quarter_step
    (a := (9 / 4 : ℝ))
    (c0 := (203 / 1000 : ℝ)) (c1 := (131 / 1000 : ℝ))
    (c2 := (82 / 1000 : ℝ)) (c3 := (493 / 10000 : ℝ))
    (by norm_num) dickmanRho_nine_fourths_lt.le
    (by norm_num; exact dickmanRho_five_halves_lt.le)
    (by norm_num; linarith [dickmanRho_eleven_fourths_lt])
    (by norm_num; exact dickmanRho_three_lt_493_div_10000.le)
  norm_num at h ⊢
  nlinarith

lemma dickmanRho_seven_halves_lt :
    dickmanRho (7 / 2) < (107 / 5000 : ℝ) := by
  have h := dickmanRho_quarter_step
    (a := (5 / 2 : ℝ))
    (c0 := (131 / 1000 : ℝ)) (c1 := (82 / 1000 : ℝ))
    (c2 := (493 / 10000 : ℝ)) (c3 := (9 / 250 : ℝ))
    (by norm_num) dickmanRho_five_halves_lt.le
    (by norm_num; linarith [dickmanRho_eleven_fourths_lt])
    (by norm_num; exact dickmanRho_three_lt_493_div_10000.le)
    (by norm_num; exact dickmanRho_thirteen_fourths_lt.le)
  norm_num at h ⊢
  nlinarith

lemma dickmanRho_fifteen_fourths_lt :
    dickmanRho (15 / 4) < (63 / 5000 : ℝ) := by
  have h := dickmanRho_quarter_step
    (a := (11 / 4 : ℝ))
    (c0 := (82 / 1000 : ℝ)) (c1 := (493 / 10000 : ℝ))
    (c2 := (9 / 250 : ℝ)) (c3 := (107 / 5000 : ℝ))
    (by norm_num) dickmanRho_eleven_fourths_lt.le
    (by norm_num; exact dickmanRho_three_lt_493_div_10000.le)
    (by norm_num; exact dickmanRho_thirteen_fourths_lt.le)
    (by norm_num; exact dickmanRho_seven_halves_lt.le)
  norm_num at h ⊢
  nlinarith

lemma dickmanRho_four_lt_three_fourhundredths :
    dickmanRho 4 < (3 / 400 : ℝ) := by
  have h := dickmanRho_quarter_step
    (a := (3 : ℝ))
    (c0 := (493 / 10000 : ℝ)) (c1 := (9 / 250 : ℝ))
    (c2 := (107 / 5000 : ℝ)) (c3 := (63 / 5000 : ℝ))
    (by norm_num) dickmanRho_three_lt_493_div_10000.le
    (by norm_num; exact dickmanRho_thirteen_fourths_lt.le)
    (by norm_num; exact dickmanRho_seven_halves_lt.le)
    (by norm_num; exact dickmanRho_fifteen_fourths_lt.le)
  norm_num at h ⊢
  nlinarith

lemma dickmanRho_six_lt_one_fourthousandth :
    dickmanRho 6 < (1 / 4000 : ℝ) := by
  have h5 := dickmanRho_le_previous_div (e := (5 : ℝ)) (by norm_num)
  have h6 := dickmanRho_le_previous_div (e := (6 : ℝ)) (by norm_num)
  norm_num at h5 h6 ⊢
  nlinarith [dickmanRho_four_lt_three_fourhundredths]

lemma scaled_dickmanRho_nat_lt
    (n : ℕ) (hn : 6 ≤ n) :
    (((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) * dickmanRho n <
      (7 / 500 : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base =>
      norm_num
      nlinarith [dickmanRho_six_lt_one_fourthousandth]
  | succ n hn ih =>
      have hn0 : (0 : ℝ) ≤ n := by positivity
      have hn1 : (0 : ℝ) < n + 1 := by positivity
      have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
      have hstep := dickmanRho_le_previous_div
        (e := ((n + 1 : ℕ) : ℝ)) (by exact_mod_cast (show 1 ≤ n + 1 by omega))
      have hstep' : ((n + 1 : ℕ) : ℝ) * dickmanRho (n + 1) ≤
          dickmanRho n := by
        have hh := (le_div_iff₀ hn1).mp (by
          simpa [Nat.cast_add, Nat.cast_one] using hstep)
        simpa [Nat.cast_add, Nat.cast_one, mul_comm] using hh
      have hrho : 0 ≤ dickmanRho (n + 1) :=
        dickmanRho_nonneg (by positivity)
      have hcoef : (((n + 3 : ℕ) : ℝ) : ℝ) ≤
          (((n + 1 : ℕ) : ℝ) : ℝ) ^ 2 := by
        norm_num [Nat.cast_add, Nat.cast_one]
        nlinarith
      have hfactor : 0 ≤ (((n + 2 : ℕ) : ℝ) : ℝ) * dickmanRho (n + 1) :=
        mul_nonneg (by positivity) hrho
      have hmul := mul_le_mul_of_nonneg_right hcoef hfactor
      have hfront : 0 ≤ (((n + 2 : ℕ) : ℝ) : ℝ) * ((n + 1 : ℕ) : ℝ) :=
        mul_nonneg (by positivity) (by positivity)
      have hmul' := mul_le_mul_of_nonneg_left hstep' hfront
      norm_num [Nat.cast_add, Nat.cast_one] at ih ⊢
      calc
        (n + 1 + 2) * (n + 1 + 1) * dickmanRho (n + 1) =
            (n + 3) * ((n + 2) * dickmanRho (n + 1)) := by ring
        _ ≤ (n + 1) ^ 2 * ((n + 2) * dickmanRho (n + 1)) := by
          simpa [Nat.cast_add, Nat.cast_one] using hmul
        _ = ((n + 2) * (n + 1)) * ((n + 1) * dickmanRho (n + 1)) := by ring
        _ ≤ ((n + 2) * (n + 1)) * dickmanRho n := by
          simpa [Nat.cast_add, Nat.cast_one] using hmul'
        _ < 7 / 500 := ih

lemma section61_scalar_large
    {r : ℕ} {e a : ℝ} (hr : 3 ≤ r)
    (heLower : ((2 * r : ℕ) : ℝ) ≤ e)
    (heUpper : e ≤ ((2 * r + 2 : ℕ) : ℝ))
    (haLower : e - 1 ≤ a) (haUpper : a ≤ e) :
    dickmanRho e ≤
      gsExpAlternatingSum (Real.log a) (2 * r + 1) -
        (Real.log e - Real.log a) := by
  let D : ℝ := ((2 * r + 2 : ℕ) : ℝ) * ((2 * r + 1 : ℕ) : ℝ)
  have he6 : 6 ≤ e := by
    have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
    norm_num [Nat.cast_mul] at heLower
    linarith
  have he0 : 0 < e := by linarith
  have ha0 : 0 < a := by linarith
  have ha1 : 1 ≤ a := by linarith
  have hz0 : 0 ≤ Real.log a := Real.log_nonneg ha1
  have hN0 : (0 : ℝ) < ((2 * r + 2 : ℕ) : ℝ) := by positivity
  have hD0 : 0 < D := by dsimp only [D]; positivity
  have haN : a ≤ ((2 * r + 2 : ℕ) : ℝ) := haUpper.trans heUpper
  have hzLog : Real.log a ≤ Real.log ((2 * r + 2 : ℕ) : ℝ) :=
    Real.strictMonoOn_log.monotoneOn ha0 hN0 haN
  have hzUpper : Real.log a ≤ ((2 * r + 3 : ℕ) : ℝ) := by
    have hlogA := Real.log_le_sub_one_of_pos ha0
    have hNr : ((2 * r + 2 : ℕ) : ℝ) ≤ ((2 * r + 3 : ℕ) : ℝ) := by
      exact_mod_cast (show 2 * r + 2 ≤ 2 * r + 3 by omega)
    linarith
  have hTaylor := exp_neg_sub_odd_sum_le_alt hz0 r hzUpper
  have hexp : Real.exp (-Real.log a) = 1 / a := by
    rw [Real.exp_neg, Real.exp_log ha0]
    simp only [one_div]
  rw [hexp] at hTaylor
  have hp := pow_le_pow_left₀ hz0 hzLog (2 * r + 2)
  have hpowerFactorial :
      Real.log a ^ (2 * r + 2) / (2 * r).factorial ≤
        (243 / 500 : ℝ) := by
    exact (div_le_div_of_nonneg_right hp (by positivity)).trans
      (log_power_div_factorial_le hr)
  have hfac : (((2 * r + 2).factorial : ℕ) : ℝ) =
      D * (((2 * r).factorial : ℕ) : ℝ) := by
    rw [show 2 * r + 2 = (2 * r + 1) + 1 by omega,
      Nat.factorial_succ,
      show 2 * r + 1 = (2 * r) + 1 by omega,
      Nat.factorial_succ]
    norm_num [D, Nat.cast_add, Nat.cast_mul]
    ring
  have hrem :
      Real.log a ^ (2 * r + 2) / (2 * r + 2).factorial ≤
        (243 / 500 : ℝ) / D := by
    rw [hfac]
    have hfact0 : (0 : ℝ) < ((2 * r).factorial : ℕ) := by positivity
    calc
      Real.log a ^ (2 * r + 2) /
          (D * (((2 * r).factorial : ℕ) : ℝ)) =
          (Real.log a ^ (2 * r + 2) / (2 * r).factorial) / D := by
            field_simp [hD0.ne', hfact0.ne']
      _ ≤ (243 / 500 : ℝ) / D :=
        div_le_div_of_nonneg_right hpowerFactorial hD0.le
  have hloss := loss_lower he6 haLower
  have hprod : e * (e - 1) ≤ D := by
    dsimp only [D]
    have heOneUpper : e - 1 ≤ ((2 * r + 1 : ℕ) : ℝ) := by
      have hcast : (((2 * r + 2 : ℕ) : ℝ) - 1) =
          ((2 * r + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      linarith
    exact mul_le_mul heUpper heOneUpper (by linarith) (by positivity)
  have hbase : (1 / 2 : ℝ) / D ≤ 1 / (2 * e * (e - 1)) := by
    have hem0 : 0 < e - 1 := by linarith
    have hden0 : 0 < 2 * e * (e - 1) :=
      mul_pos (mul_pos (by norm_num) he0) hem0
    have hden : 2 * e * (e - 1) ≤ 2 * D := by nlinarith
    have hone := one_div_le_one_div_of_le hden0 hden
    calc
      (1 / 2 : ℝ) / D = 1 / (2 * D) := by
        field_simp [hD0.ne']
      _ ≤ 1 / (2 * e * (e - 1)) := hone
  have hrhoNat := scaled_dickmanRho_nat_lt (2 * r) (by omega)
  have hrhoDiv : dickmanRho ((2 * r : ℕ) : ℝ) < (7 / 500 : ℝ) / D := by
    rw [lt_div_iff₀ hD0]
    simpa [D, Nat.cast_add, Nat.cast_mul, mul_comm] using hrhoNat
  have hrhoMono : dickmanRho e ≤ dickmanRho ((2 * r : ℕ) : ℝ) :=
    antitoneOn_dickmanRho_Ici_zero
      (show (0 : ℝ) ≤ ((2 * r : ℕ) : ℝ) by positivity)
      (show (0 : ℝ) ≤ e by linarith) heLower
  apply le_of_lt
  calc
    dickmanRho e ≤ dickmanRho ((2 * r : ℕ) : ℝ) := hrhoMono
    _ < (7 / 500 : ℝ) / D := hrhoDiv
    _ = (1 / 2 : ℝ) / D - (243 / 500 : ℝ) / D := by ring
    _ ≤ (1 / a - (Real.log e - Real.log a)) -
          Real.log a ^ (2 * r + 2) / (2 * r + 2).factorial := by
      linarith
    _ ≤ gsExpAlternatingSum (Real.log a) (2 * r + 1) -
          (Real.log e - Real.log a) := by
      linarith

theorem gs_proposition61_of_scale_ge_six
    {chi sigma : ℝ → ℝ} (hchi : IsGSKernel chi)
    (hsigma : IsGSSolution chi sigma)
    {u : ℝ} (hu : 1 ≤ u)
    (hlarge : gsScale chi u - 1 <
      gsScale chi (u / gsScale chi u))
    (hE6 : 6 ≤ gsScale chi u) :
    dickmanRho (gsScale chi u) ≤ sigma u := by
  let e : ℝ := gsScale chi u
  let u0 : ℝ := u / e
  let a : ℝ := gsScale chi u0
  let r : ℕ := ⌊e / 2⌋₊
  have he0 : 0 < e := by
    dsimp only [e]
    exact gsScale_pos chi u
  have he6 : 6 ≤ e := by exact hE6
  have heu : e * u0 = u := by
    dsimp only [u0]
    field_simp [he0.ne']
  have heLeU : e ≤ u := by
    dsimp only [e]
    exact gsScale_le_self hchi hu
  have hu0 : 1 ≤ u0 := by
    dsimp only [u0]
    rw [le_div_iff₀ he0]
    simpa using heLeU
  have hu00 : 0 ≤ u0 := zero_le_one.trans hu0
  have hu0u : u0 ≤ u := by
    rw [← heu]
    nlinarith [mul_nonneg (sub_nonneg.mpr (by linarith : 1 ≤ e)) hu00]
  have ha0 : 0 < a := by
    dsimp only [a]
    exact gsScale_pos chi u0
  have haUpper : a ≤ e := by
    dsimp only [a, e]
    exact gsScale_mono hchi hu0 hu hu0u
  have haLower : e - 1 ≤ a := by
    dsimp only [e, a, u0] at hlarge ⊢
    exact hlarge.le
  have hr : 3 ≤ r := by
    dsimp only [r]
    apply Nat.le_floor
    norm_num
    linarith
  have heLower : ((2 * r : ℕ) : ℝ) ≤ e := by
    have hf : ((r : ℕ) : ℝ) ≤ e / 2 := by
      dsimp only [r]
      exact Nat.floor_le (show (0 : ℝ) ≤ e / 2 by positivity)
    push_cast at hf ⊢
    nlinarith
  have heUpper : e ≤ ((2 * r + 2 : ℕ) : ℝ) := by
    have hf : e / 2 < ((r : ℕ) : ℝ) + 1 := by
      dsimp only [r]
      exact Nat.lt_floor_add_one (e / 2)
    push_cast at hf ⊢
    linarith
  have hfit : ((2 * r : ℕ) : ℝ) * u0 ≤ u := by
    rw [← heu]
    nlinarith [mul_nonneg (sub_nonneg.mpr heLower) hu00]
  have hlogE : Real.log e = gsLogScale chi u := by
    dsimp only [e, gsScale]
    rw [Real.log_exp]
  have hlogA : Real.log a = gsLogScale chi u0 := by
    dsimp only [a, gsScale]
    rw [Real.log_exp]
  have hscalar := section61_scalar_large hr heLower heUpper haLower haUpper
  have hperturb := gs_fill_exp_perturb_lower hchi hsigma hu0 hu0u hu r hfit
  rw [← hlogA, ← hlogE] at hperturb
  exact hscalar.trans hperturb

theorem gs_proposition61_estimate
    {chi sigma : ℝ → ℝ} (hchi : IsGSKernel chi)
    (hsigma : IsGSSolution chi sigma) :
    ∀ u : ℝ, 1 ≤ u → 2 < gsScale chi u →
      gsScale chi u - 1 < gsScale chi (u / gsScale chi u) →
      dickmanRho (gsScale chi u) ≤ sigma u := by
  intro u hu hE2 hlarge
  by_cases hE6 : gsScale chi u ≤ 6
  · exact gs_proposition61_of_scale_le_six hchi hsigma hu hE2 hlarge hE6
  · exact gs_proposition61_of_scale_ge_six hchi hsigma hu hlarge
      (le_of_not_ge hE6)


end

end Erdos783
