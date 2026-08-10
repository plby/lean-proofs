import Arxiv.Arxiv2407_19026.TangentKernelBounds

/-!
# Semantic bounds for the backward coordinate comparisons

These estimates replace the executable affine-cover checks on the backward
intervals with Taylor bounds and exact polynomial certificates.
-/

namespace Arxiv2407_19026

noncomputable section

def backwardExpTaylor5 (z : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 6, (-z) ^ i / Nat.factorial i

def backwardExpError6 (z : ℝ) : ℝ :=
  z ^ 6 * 7 / (Nat.factorial 6 * 6)

def backwardExpLower5 (z : ℝ) : ℝ :=
  backwardExpTaylor5 z - backwardExpError6 z

def backwardQLower (β z : ℝ) : ℝ :=
  -mediumCorrectionPolynomial β z *
      KernelBounds.expNegTaylor9 z -
    (1 / 4) * KernelBounds.expNegError10 z

def backwardExpQLower (β z : ℝ) : ℝ :=
  let r := backwardQLower β z + 3 / 10
  (KernelBounds.expNegTaylor9 (3 / 10) -
      KernelBounds.expNegError10 (3 / 10)) *
    (1 + r + r ^ 2 / 2 + r ^ 3 / 6 + r ^ 4 / 24)

def backwardBlueRawLower (β z : ℝ) : ℝ :=
  z / (1 + z) * backwardExpQLower β z

def backwardLogUpperBelowFive (x : ℝ) : ℝ :=
  let y := 1 - x
  (-(y + y ^ 2 / 2 + y ^ 3 / 3 + y ^ 4 / 4 + y ^ 5 / 5))

def backwardLogUpperBelowSeven (x : ℝ) : ℝ :=
  let y := 1 - x
  (-(y + y ^ 2 / 2 + y ^ 3 / 3 + y ^ 4 / 4 +
    y ^ 5 / 5 + y ^ 6 / 6 + y ^ 7 / 7))

def backwardLogTangentUpper (center x : ℝ) : ℝ :=
  backwardLogUpperBelowSeven center + x / center - 1

def backwardLogLowerBelowThree (x : ℝ) : ℝ :=
  let y := (1 - x) / (1 + x)
  (-2) * (y + y ^ 3 / 3 + y ^ 5 / 5 +
    y ^ 7 / (1 - y ^ 2))

def backwardLogLowerThreeClosed (x : ℝ) : ℝ :=
  (x - 1) *
    (15 * x ^ 6 + 2 * x ^ 5 + 417 * x ^ 4 +
      92 * x ^ 3 + 417 * x ^ 2 + 2 * x + 15) /
    (30 * x * (x + 1) ^ 5)

def backwardLogLowerBelowFour (x : ℝ) : ℝ :=
  let y := (1 - x) / (1 + x)
  (-2) * (y + y ^ 3 / 3 + y ^ 5 / 5 + y ^ 7 / 7 +
    y ^ 9 / (1 - y ^ 2))

def backwardLogLowerFourClosed (x : ℝ) : ℝ :=
  (x - 1) *
    (105 * x ^ 8 - 136 * x ^ 7 + 5212 * x ^ 6 +
      1096 * x ^ 5 + 14326 * x ^ 4 + 1096 * x ^ 3 +
      5212 * x ^ 2 - 136 * x + 105) /
    (210 * x * (x + 1) ^ 7)

def backwardLogLowerScaledThree (x : ℝ) : ℝ :=
  backwardLogLowerBelowThree (2 * x) -
    693147181 / 1000000000

lemma backward_log_lower_below_three_closed {x : ℝ}
    (hx0 : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    backwardLogLowerBelowThree x =
      backwardLogLowerThreeClosed x := by
  have hx1' : 1 + x ≠ 0 := by
    simpa [add_comm] using hx1
  unfold backwardLogLowerBelowThree
  dsimp only
  rw [show
    1 - ((1 - x) / (1 + x)) ^ 2 =
      4 * x / (1 + x) ^ 2 by
    field_simp [hx1']
    ring]
  unfold backwardLogLowerThreeClosed
  field_simp [hx0, hx1']
  ring

lemma backward_log_lower_below_four_closed {x : ℝ}
    (hx0 : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    backwardLogLowerBelowFour x =
      backwardLogLowerFourClosed x := by
  have hx1' : 1 + x ≠ 0 := by
    simpa [add_comm] using hx1
  unfold backwardLogLowerBelowFour
  dsimp only
  rw [show
    1 - ((1 - x) / (1 + x)) ^ 2 =
      4 * x / (1 + x) ^ 2 by
    field_simp [hx1']
    ring]
  unfold backwardLogLowerFourClosed
  field_simp [hx0, hx1']
  ring

def backwardBLogLower (β t : ℝ) : ℝ :=
  backwardLogLowerBelowThree t -
    tangentCoordLogUpper (1 + t) -
    mediumCorrectionPolynomial β t * backwardExpTaylor5 t -
    (1 / 4) * backwardExpError6 t

def backwardBLogLowerFour (β t : ℝ) : ℝ :=
  backwardLogLowerBelowFour t -
    tangentCoordLogUpper (1 + t) -
    mediumCorrectionPolynomial β t * backwardExpTaylor5 t -
    (1 / 4) * backwardExpError6 t

def backwardBLogLowerScaledThree (β t : ℝ) : ℝ :=
  backwardLogLowerScaledThree t -
    tangentCoordLogUpper (1 + t) -
    mediumCorrectionPolynomial β t * backwardExpTaylor5 t -
    (1 / 4) * backwardExpError6 t

def backwardMuLower (z : ℝ) : ℝ :=
  z * backwardExpLower5 z

def backwardMuLowerNine (z : ℝ) : ℝ :=
  z * (KernelBounds.expNegTaylor9 z -
    KernelBounds.expNegError10 z)

def backwardXLogUpper (B z : ℝ) : ℝ :=
  let M := backwardMuLower z
  backwardLogUpperBelowFive (1 - B) * (1 - M)⁻¹ +
    backwardLogUpperBelowFive (1 - M)

def backwardXLogUpperSevenNine (B z : ℝ) : ℝ :=
  let M := backwardMuLowerNine z
  backwardLogUpperBelowSeven (1 - B) * (1 - M)⁻¹ +
    backwardLogUpperBelowSeven (1 - M)

def backwardXLogTangentUpper
    (pCenter omCenter B z : ℝ) : ℝ :=
  let M := backwardMuLowerNine z
  backwardLogTangentUpper pCenter (1 - B) * (1 - M)⁻¹ +
    backwardLogTangentUpper omCenter (1 - M)

lemma backward_exp_approx5 {z : ℝ} (hz : z ∈ Set.Icc 0 1) :
    |Real.exp (-z) - backwardExpTaylor5 z| ≤
      backwardExpError6 z := by
  have h := Real.exp_bound (x := -z) (n := 6) (by
    rw [abs_neg, abs_of_nonneg hz.1]
    exact hz.2) (by norm_num)
  norm_num [backwardExpTaylor5, backwardExpError6,
    Finset.sum_range_succ, Nat.factorial, abs_neg,
    abs_of_nonneg hz.1] at h ⊢
  convert h using 1
  all_goals ring_nf

lemma backward_exp_lower5_nonneg {z : ℝ}
    (hz : z ∈ Set.Icc 0 1) :
    0 ≤ backwardExpLower5 z := by
  have hz2 : 0 ≤ z ^ 2 := sq_nonneg z
  have hz4 : 0 ≤ z ^ 4 := pow_nonneg hz.1 4
  have h23 : 0 ≤ z ^ 2 * (1 / 2 - z / 6) :=
    mul_nonneg hz2 (by nlinarith [hz.2])
  have h45 : 0 ≤ z ^ 4 * (1 / 24 - z / 120) :=
    mul_nonneg hz4 (by nlinarith [hz.2])
  have h6 : z ^ 6 ≤ z ^ 4 := by
    have hz2le : z ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hz.2)]
    nlinarith [mul_nonneg hz4
      (sub_nonneg.mpr hz2le)]
  norm_num [backwardExpLower5, backwardExpTaylor5,
    backwardExpError6, Finset.sum_range_succ,
    Nat.factorial]
  nlinarith [sub_nonneg.mpr hz.2]

lemma backward_log_upper_below_five {x : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) :
    Real.log x ≤ backwardLogUpperBelowFive x := by
  let y : ℝ := 1 - x
  have hy0 : 0 ≤ y := sub_nonneg.mpr hx1
  have hy1 : y < 1 := by dsimp [y]; linarith
  have hyabs : |y| < 1 := by
    simpa [abs_of_nonneg hy0] using hy1
  have hseries := Real.hasSum_pow_div_log_of_abs_lt_one hyabs
  have hpartial :=
    hseries.summable.sum_le_tsum (Finset.range 5) (by
      intro i hi
      positivity)
  rw [hseries.tsum_eq] at hpartial
  have harg : 1 - y = x := by dsimp [y]; ring
  rw [harg] at hpartial
  norm_num [Finset.sum_range_succ,
    backwardLogUpperBelowFive, y] at hpartial ⊢
  linarith

lemma backward_log_upper_below_seven {x : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) :
    Real.log x ≤ backwardLogUpperBelowSeven x := by
  let y : ℝ := 1 - x
  have hy0 : 0 ≤ y := sub_nonneg.mpr hx1
  have hy1 : y < 1 := by dsimp [y]; linarith
  have hyabs : |y| < 1 := by
    simpa [abs_of_nonneg hy0] using hy1
  have hseries := Real.hasSum_pow_div_log_of_abs_lt_one hyabs
  have hpartial :=
    hseries.summable.sum_le_tsum (Finset.range 7) (by
      intro i hi
      positivity)
  rw [hseries.tsum_eq] at hpartial
  have harg : 1 - y = x := by dsimp [y]; ring
  rw [harg] at hpartial
  norm_num [Finset.sum_range_succ,
    backwardLogUpperBelowSeven, y] at hpartial ⊢
  linarith

lemma backward_log_tangent_upper {center x : ℝ}
    (hc : center ∈ Set.Ioc (0 : ℝ) 1) (hx : 0 < x) :
    Real.log x ≤ backwardLogTangentUpper center x := by
  have hlogCenter :=
    backward_log_upper_below_seven hc.1 hc.2
  have hquot :=
    Real.log_le_sub_one_of_pos (div_pos hx hc.1)
  have hlogDiv :
      Real.log (x / center) =
        Real.log x - Real.log center :=
    Real.log_div hx.ne' hc.1.ne'
  rw [hlogDiv] at hquot
  unfold backwardLogTangentUpper
  linarith

lemma tangent_coord_log_upper_backward {x : ℝ}
    (hx : x ∈ Set.Icc (1 : ℝ) 2) :
    Real.log x ≤ tangentCoordLogUpper x := by
  let s : ℝ := (2 - x) / 2
  have hs0 : 0 ≤ s := by dsimp [s]; linarith [hx.2]
  have hs1 : s < 1 := by dsimp [s]; linarith [hx.1]
  have hsabs : |s| < 1 := by
    simpa [abs_of_nonneg hs0] using hs1
  have hseries := Real.hasSum_pow_div_log_of_abs_lt_one hsabs
  have hpartial :=
    hseries.summable.sum_le_tsum (Finset.range 6) (by
      intro i hi
      positivity)
  rw [hseries.tsum_eq] at hpartial
  have hratio : 1 - s = x / 2 := by
    dsimp [s]
    ring
  rw [hratio] at hpartial
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
  have hlog :
      Real.log x = Real.log 2 + Real.log (x / 2) := by
    calc
      Real.log x = Real.log (2 * (x / 2)) := by
        congr 1
        ring
      _ = Real.log 2 + Real.log (x / 2) :=
        Real.log_mul (by norm_num) (by positivity)
  have hlogTwo :
      Real.log 2 ≤ (693147181 / 1000000000 : ℝ) :=
    (le_of_lt Real.log_two_lt_d9).trans (by norm_num)
  rw [hlog]
  norm_num [Finset.sum_range_succ, tangentCoordLogUpper, s]
    at hpartial ⊢
  linarith

lemma backward_log_lower_below_three {x : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) :
    backwardLogLowerBelowThree x ≤ Real.log x := by
  let y : ℝ := (1 - x) / (1 + x)
  have hxplus : 0 < 1 + x := by linarith
  have hy0 : 0 ≤ y := div_nonneg (sub_nonneg.mpr hx1) hxplus.le
  have hy1 : y < 1 := by
    rw [div_lt_one hxplus]
    linarith
  have h := Real.log_div_le_sum_range_add hy0 hy1 3
  have hratio : (1 + y) / (1 - y) = x⁻¹ := by
    dsimp [y]
    field_simp [hx.ne', hxplus.ne']
    ring
  rw [hratio, Real.log_inv] at h
  norm_num [Finset.sum_range_succ,
    backwardLogLowerBelowThree, y] at h ⊢
  linarith

lemma backward_log_lower_below_four {x : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) :
    backwardLogLowerBelowFour x ≤ Real.log x := by
  let y : ℝ := (1 - x) / (1 + x)
  have hxplus : 0 < 1 + x := by linarith
  have hy0 : 0 ≤ y := div_nonneg (sub_nonneg.mpr hx1) hxplus.le
  have hy1 : y < 1 := by
    rw [div_lt_one hxplus]
    linarith
  have h := Real.log_div_le_sum_range_add hy0 hy1 4
  have hratio : (1 + y) / (1 - y) = x⁻¹ := by
    dsimp [y]
    field_simp [hx.ne', hxplus.ne']
    ring
  rw [hratio, Real.log_inv] at h
  norm_num [Finset.sum_range_succ,
    backwardLogLowerBelowFour, y] at h ⊢
  linarith

lemma backward_log_lower_scaled_three {x : ℝ}
    (hx : 0 < x) (hxhalf : x ≤ 1 / 2) :
    backwardLogLowerScaledThree x ≤ Real.log x := by
  have htwo : 0 < 2 * x := by positivity
  have hseries :=
    backward_log_lower_below_three htwo (by linarith)
  have hlogTwo :
      Real.log 2 ≤ (693147181 / 1000000000 : ℝ) :=
    (le_of_lt Real.log_two_lt_d9).trans (by norm_num)
  have hlog :
      Real.log (2 * x) = Real.log 2 + Real.log x :=
    Real.log_mul (by norm_num) hx.ne'
  rw [hlog] at hseries
  unfold backwardLogLowerScaledThree
  linarith

lemma backward_exp_lower_nine_nonneg {z : ℝ}
    (hz : z ∈ Set.Icc 0 1) :
    0 ≤ KernelBounds.expNegTaylor9 z -
      KernelBounds.expNegError10 z := by
  have h01 : 0 ≤ 1 - z := sub_nonneg.mpr hz.2
  have h23 : 0 ≤ z ^ 2 * (1 / 2 - z / 6) :=
    mul_nonneg (sq_nonneg z) (by nlinarith [hz.2])
  have h45 : 0 ≤ z ^ 4 * (1 / 24 - z / 120) :=
    mul_nonneg (pow_nonneg hz.1 4) (by nlinarith [hz.2])
  have h67 : 0 ≤ z ^ 6 * (1 / 720 - z / 5040) :=
    mul_nonneg (pow_nonneg hz.1 6) (by nlinarith [hz.2])
  have h89 :
      0 ≤ z ^ 8 *
        (1 / 40320 - z / 362880 -
          11 * z ^ 2 / 36288000) := by
    apply mul_nonneg (pow_nonneg hz.1 8)
    nlinarith [sq_nonneg z,
      mul_nonneg hz.1 (sub_nonneg.mpr hz.2)]
  norm_num [KernelBounds.expNegTaylor9,
    KernelBounds.expNegError10, Finset.sum_range_succ,
    Nat.factorial]
  nlinarith

lemma medium_correction_abs_le_quarter {β z : ℝ}
    (hβ : β ∈ Set.Icc 0 (2 / 25))
    (hz : z ∈ Set.Icc 0 1) :
    |mediumCorrectionPolynomial β z| ≤ 1 / 4 := by
  have hlow :
      -(1 / 4) ≤ mediumCorrectionPolynomial β z := by
    rw [← sub_nonneg]
    rw [sub_neg_eq_add]
    rw [show
      mediumCorrectionPolynomial β z + 1 / 4 =
        z * (1 / 4 + 2 * β + (6 / 25 - β) * z -
          2 / 25 * z ^ 2) by
      dsimp [mediumCorrectionPolynomial]
      ring]
    apply mul_nonneg hz.1
    nlinarith [hβ.1, hβ.2, hz.1, hz.2, sq_nonneg z]
  have hu :
      mediumCorrectionPolynomial β z ≤ β + 4 / 25 := by
    rw [← sub_nonneg]
    rw [show
      β + 4 / 25 - mediumCorrectionPolynomial β z =
        (1 - z) *
          ((41 + 16 * z - 8 * z ^ 2 +
              100 * β * (1 - z)) / 100) by
      dsimp [mediumCorrectionPolynomial]
      ring]
    apply mul_nonneg (sub_nonneg.mpr hz.2)
    have hz2 : z ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hz.2)]
    have hβterm : 0 ≤ 100 * β * (1 - z) :=
      mul_nonneg (mul_nonneg (by norm_num) hβ.1)
        (sub_nonneg.mpr hz.2)
    nlinarith
  rw [abs_le]
  constructor
  · exact hlow
  · nlinarith [hβ.2]

lemma backward_q_lower_le {β z : ℝ}
    (hβ : β ∈ Set.Icc 0 (2 / 25))
    (hz : z ∈ Set.Icc 0 1) :
    backwardQLower β z ≤
      -mediumCorrectionPolynomial β z * Real.exp (-z) := by
  have happrox := backward_exp_approx5 hz
  have happrox9 := KernelBounds.exp_neg_approx hz
  have hP := medium_correction_abs_le_quarter hβ hz
  have herror : 0 ≤ KernelBounds.expNegError10 z := by
    dsimp [KernelBounds.expNegError10]
    positivity
  have hproduct :
      mediumCorrectionPolynomial β z *
          (Real.exp (-z) - KernelBounds.expNegTaylor9 z) ≤
        (1 / 4) * KernelBounds.expNegError10 z := by
    calc
      _ ≤
          |mediumCorrectionPolynomial β z *
            (Real.exp (-z) -
              KernelBounds.expNegTaylor9 z)| :=
        le_abs_self _
      _ =
          |mediumCorrectionPolynomial β z| *
            |Real.exp (-z) -
              KernelBounds.expNegTaylor9 z| := abs_mul _ _
      _ ≤ (1 / 4) * KernelBounds.expNegError10 z :=
        mul_le_mul hP happrox9 (abs_nonneg _)
          (by norm_num)
  dsimp [backwardQLower]
  linarith

lemma backward_q_lower_ge {β z : ℝ}
    (hβ : β ∈ Set.Icc 0 (2 / 25))
    (hz : z ∈ Set.Icc 0 1) :
    -(3 / 10) ≤ backwardQLower β z := by
  have hP := medium_correction_abs_le_quarter hβ hz
  have happrox := KernelBounds.exp_neg_approx hz
  have hexp : Real.exp (-z) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith [hz.1])
  have he0 : 0 ≤ KernelBounds.expNegError10 z := by
    dsimp [KernelBounds.expNegError10]
    positivity
  have hzpow : z ^ 10 ≤ 1 := pow_le_one₀ hz.1 hz.2
  have he1 :
      KernelBounds.expNegError10 z ≤ 1 / 1000000 := by
    dsimp [KernelBounds.expNegError10]
    norm_num [Nat.factorial]
    nlinarith
  have hT :
      |KernelBounds.expNegTaylor9 z| ≤ 1 + 1 / 1000000 := by
    calc
      _ ≤ |Real.exp (-z)| +
          |Real.exp (-z) -
            KernelBounds.expNegTaylor9 z| := by
        have htri := abs_add_le (Real.exp (-z))
          (KernelBounds.expNegTaylor9 z - Real.exp (-z))
        rw [show
          Real.exp (-z) +
              (KernelBounds.expNegTaylor9 z - Real.exp (-z)) =
            KernelBounds.expNegTaylor9 z by ring,
          abs_sub_comm] at htri
        exact htri
      _ ≤ 1 + 1 / 1000000 := by
        have habsexp : |Real.exp (-z)| ≤ 1 := by
          rw [abs_of_pos (Real.exp_pos _)]
          exact hexp
        linarith
  have hproduct :
      |mediumCorrectionPolynomial β z *
          KernelBounds.expNegTaylor9 z| ≤
        (1 / 4) * (1 + 1 / 1000000) := by
    rw [abs_mul]
    exact mul_le_mul hP hT (abs_nonneg _)
      (by norm_num)
  have hlower :
      -(1 / 4) * (1 + 1 / 1000000) ≤
        -(mediumCorrectionPolynomial β z *
          KernelBounds.expNegTaylor9 z) := by
    have hneg := neg_abs_le
      (-(mediumCorrectionPolynomial β z *
        KernelBounds.expNegTaylor9 z))
    rw [abs_neg] at hneg
    calc
      -(1 / 4) * (1 + 1 / 1000000) =
          -((1 / 4) * (1 + 1 / 1000000)) := by ring
      _ ≤
          -|mediumCorrectionPolynomial β z *
            KernelBounds.expNegTaylor9 z| :=
        neg_le_neg hproduct
      _ ≤
          -(mediumCorrectionPolynomial β z *
            KernelBounds.expNegTaylor9 z) := hneg
  dsimp [backwardQLower]
  nlinarith

lemma backward_exp_q_lower_le {β z : ℝ}
    (hβ : β ∈ Set.Icc 0 (2 / 25))
    (hz : z ∈ Set.Icc 0 1) :
    backwardExpQLower β z ≤
      Real.exp (backwardQLower β z) := by
  let r := backwardQLower β z + 3 / 10
  have hr : 0 ≤ r := by
    dsimp [r]
    linarith [backward_q_lower_ge hβ hz]
  have hseries := Real.sum_le_exp_of_nonneg hr 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at hseries
  have hpointApprox := KernelBounds.exp_neg_approx
    (z := (3 / 10 : ℝ)) (by norm_num)
  have hpoint :
      KernelBounds.expNegTaylor9 (3 / 10) -
          KernelBounds.expNegError10 (3 / 10) ≤
        Real.exp (-(3 / 10 : ℝ)) := by
    linarith [abs_le.mp hpointApprox]
  have hpoint0 :
      0 ≤ KernelBounds.expNegTaylor9 (3 / 10) -
        KernelBounds.expNegError10 (3 / 10) := by
    norm_num [KernelBounds.expNegTaylor9,
      KernelBounds.expNegError10, Finset.sum_range_succ,
      Nat.factorial]
  have hpoly0 :
      0 ≤ 1 + r + r ^ 2 / 2 + r ^ 3 / 6 + r ^ 4 / 24 := by
    positivity
  calc
    backwardExpQLower β z =
        (KernelBounds.expNegTaylor9 (3 / 10) -
            KernelBounds.expNegError10 (3 / 10)) *
          (1 + r + r ^ 2 / 2 + r ^ 3 / 6 + r ^ 4 / 24) := by
      rfl
    _ ≤ Real.exp (-(3 / 10 : ℝ)) *
          (1 + r + r ^ 2 / 2 + r ^ 3 / 6 + r ^ 4 / 24) :=
      mul_le_mul_of_nonneg_right hpoint hpoly0
    _ ≤ Real.exp (-(3 / 10 : ℝ)) * Real.exp r :=
      mul_le_mul_of_nonneg_left hseries (Real.exp_pos _).le
    _ = Real.exp (backwardQLower β z) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [r]
      ring

lemma backward_blue_raw_lower_le {β z : ℝ}
    (hβ : β ∈ Set.Icc 0 (2 / 25))
    (hz : z ∈ Set.Icc 0 1) :
    backwardBlueRawLower β z ≤ tangentBlue β z := by
  have hq := backward_q_lower_le hβ hz
  have hexpQ :
      Real.exp (backwardQLower β z) ≤
        Real.exp
          (-mediumCorrectionPolynomial β z *
            Real.exp (-z)) :=
    Real.exp_le_exp.mpr hq
  have hraw := (backward_exp_q_lower_le hβ hz).trans hexpQ
  have hzplus : 0 < 1 + z := by linarith [hz.1]
  have hfactor : 0 ≤ z / (1 + z) :=
    div_nonneg hz.1 hzplus.le
  unfold tangentBlue backwardBlueRawLower
  rw [show
      -Real.log (1 + z) - tangentCorrectionSlope β z =
        -Real.log (1 + z) +
          (-mediumCorrectionPolynomial β z *
            Real.exp (-z)) by
      unfold tangentCorrectionSlope mediumCorrectionPolynomial
      ring,
    Real.exp_add, Real.exp_neg, Real.exp_log hzplus]
  have hmul := mul_le_mul_of_nonneg_left hraw hfactor
  simpa [div_eq_mul_inv, mul_assoc] using hmul

lemma backward_blog_lower_le {β t : ℝ}
    (hβ : β ∈ Set.Icc 0 (2 / 25))
    (ht : t ∈ Set.Icc 0 1) (ht0 : 0 < t) :
    backwardBLogLower β t ≤ tangentBLog β t := by
  have hlogLower := backward_log_lower_below_three ht0 ht.2
  have hlogUpper := tangent_coord_log_upper_backward
    (show 1 + t ∈ Set.Icc (1 : ℝ) 2 by
      constructor <;> linarith [ht.1, ht.2])
  have happrox := backward_exp_approx5 ht
  have hP := medium_correction_abs_le_quarter hβ ht
  have herror : 0 ≤ backwardExpError6 t := by
    dsimp [backwardExpError6]
    positivity
  have hproduct :
      mediumCorrectionPolynomial β t *
          (Real.exp (-t) - backwardExpTaylor5 t) ≤
        (1 / 4) * backwardExpError6 t := by
    calc
      _ ≤
          |mediumCorrectionPolynomial β t *
            (Real.exp (-t) - backwardExpTaylor5 t)| :=
        le_abs_self _
      _ =
          |mediumCorrectionPolynomial β t| *
            |Real.exp (-t) - backwardExpTaylor5 t| := abs_mul _ _
      _ ≤ (1 / 4) * backwardExpError6 t :=
        mul_le_mul hP happrox (abs_nonneg _) (by norm_num)
  unfold tangentBLog
  rw [show
    tangentCorrectionSlope β t =
      mediumCorrectionPolynomial β t * Real.exp (-t) by rfl]
  dsimp [backwardBLogLower]
  linarith

lemma backward_blog_lower_four_le {β t : ℝ}
    (hβ : β ∈ Set.Icc 0 (2 / 25))
    (ht : t ∈ Set.Icc 0 1) (ht0 : 0 < t) :
    backwardBLogLowerFour β t ≤ tangentBLog β t := by
  have hlogLower := backward_log_lower_below_four ht0 ht.2
  have hlogUpper := tangent_coord_log_upper_backward
    (show 1 + t ∈ Set.Icc (1 : ℝ) 2 by
      constructor <;> linarith [ht.1, ht.2])
  have happrox := backward_exp_approx5 ht
  have hP := medium_correction_abs_le_quarter hβ ht
  have herror : 0 ≤ backwardExpError6 t := by
    dsimp [backwardExpError6]
    positivity
  have hproduct :
      mediumCorrectionPolynomial β t *
          (Real.exp (-t) - backwardExpTaylor5 t) ≤
        (1 / 4) * backwardExpError6 t := by
    calc
      _ ≤
          |mediumCorrectionPolynomial β t *
            (Real.exp (-t) - backwardExpTaylor5 t)| :=
        le_abs_self _
      _ =
          |mediumCorrectionPolynomial β t| *
            |Real.exp (-t) - backwardExpTaylor5 t| := abs_mul _ _
      _ ≤ (1 / 4) * backwardExpError6 t :=
        mul_le_mul hP happrox (abs_nonneg _) (by norm_num)
  unfold tangentBLog
  rw [show
    tangentCorrectionSlope β t =
      mediumCorrectionPolynomial β t * Real.exp (-t) by rfl]
  dsimp [backwardBLogLowerFour]
  linarith

lemma backward_blog_lower_scaled_three_le {β t : ℝ}
    (hβ : β ∈ Set.Icc 0 (2 / 25))
    (ht : t ∈ Set.Icc 0 (1 / 2)) (ht0 : 0 < t) :
    backwardBLogLowerScaledThree β t ≤ tangentBLog β t := by
  have hlogLower :=
    backward_log_lower_scaled_three ht0 ht.2
  have hlogUpper := tangent_coord_log_upper_backward
    (show 1 + t ∈ Set.Icc (1 : ℝ) 2 by
      constructor <;> linarith [ht.1, ht.2])
  have happrox :=
    backward_exp_approx5
      (show t ∈ Set.Icc (0 : ℝ) 1 by
        exact ⟨ht.1, ht.2.trans (by norm_num)⟩)
  have hP := medium_correction_abs_le_quarter hβ
    (show t ∈ Set.Icc (0 : ℝ) 1 by
      exact ⟨ht.1, ht.2.trans (by norm_num)⟩)
  have herror : 0 ≤ backwardExpError6 t := by
    dsimp [backwardExpError6]
    positivity
  have hproduct :
      mediumCorrectionPolynomial β t *
          (Real.exp (-t) - backwardExpTaylor5 t) ≤
        (1 / 4) * backwardExpError6 t := by
    calc
      _ ≤
          |mediumCorrectionPolynomial β t *
            (Real.exp (-t) - backwardExpTaylor5 t)| :=
        le_abs_self _
      _ =
          |mediumCorrectionPolynomial β t| *
            |Real.exp (-t) - backwardExpTaylor5 t| := abs_mul _ _
      _ ≤ (1 / 4) * backwardExpError6 t :=
        mul_le_mul hP happrox (abs_nonneg _) (by norm_num)
  unfold tangentBLog
  rw [show
    tangentCorrectionSlope β t =
      mediumCorrectionPolynomial β t * Real.exp (-t) by rfl]
  dsimp [backwardBLogLowerScaledThree]
  linarith

lemma tangent_xlog_le_backward_seven_nine {β B z : ℝ}
    (hβ : 0 ≤ β) (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hB0 : 0 ≤ B) (hB : B ≤ tangentBlue β z)
    (hB1 : B < 1) :
    tangentXLog β z ≤ backwardXLogUpperSevenNine B z := by
  have happrox := KernelBounds.exp_neg_approx hz
  have hM :
      backwardMuLowerNine z ≤ optimizationM z := by
    unfold backwardMuLowerNine optimizationM
    exact mul_le_mul_of_nonneg_left
      (by linarith [abs_le.mp happrox]) hz.1
  have hM0 : 0 ≤ backwardMuLowerNine z := by
    unfold backwardMuLowerNine
    exact mul_nonneg hz.1 (backward_exp_lower_nine_nonneg hz)
  have hM1 : backwardMuLowerNine z < 1 :=
    hM.trans_lt (optimizationM_lt_one_of_Icc hz.1 hz.2)
  let p : ℝ := 1 - tangentBlue β z
  let om : ℝ := 1 - optimizationM z
  let pB : ℝ := 1 - B
  let omM : ℝ := 1 - backwardMuLowerNine z
  have hp : 0 < p :=
    sub_pos.mpr (tangentBlue_lt_one hβ hz.1 hz.2)
  have hom : 0 < om :=
    sub_pos.mpr (optimizationM_lt_one_of_Icc hz.1 hz.2)
  have hpB : 0 < pB := by dsimp [pB]; linarith
  have homM : 0 < omM := by dsimp [omM]; linarith
  have hp_le : p ≤ pB := by dsimp [p, pB]; linarith
  have hom_le : om ≤ omM := by dsimp [om, omM]; linarith
  have hlogp :
      Real.log p ≤ backwardLogUpperBelowSeven pB := by
    exact (Real.strictMonoOn_log.monotoneOn hp hpB hp_le).trans
      (backward_log_upper_below_seven hpB (by
        dsimp [pB]
        linarith))
  have hlogom :
      Real.log om ≤ backwardLogUpperBelowSeven omM := by
    exact (Real.strictMonoOn_log.monotoneOn hom homM hom_le).trans
      (backward_log_upper_below_seven homM (by
        dsimp [omM]
        linarith))
  have hubp : backwardLogUpperBelowSeven pB ≤ 0 := by
    have hy0 : 0 ≤ 1 - pB := by
      simpa [pB] using hB0
    dsimp [backwardLogUpperBelowSeven]
    exact neg_nonpos.mpr (by positivity)
  have hinv : omM⁻¹ ≤ om⁻¹ :=
    (inv_le_inv₀ homM hom).mpr hom_le
  have hfirst :
      Real.log p * om⁻¹ ≤
        backwardLogUpperBelowSeven pB * omM⁻¹ := by
    calc
      Real.log p * om⁻¹ ≤
          backwardLogUpperBelowSeven pB * om⁻¹ :=
        mul_le_mul_of_nonneg_right hlogp (inv_nonneg.mpr hom.le)
      _ ≤ backwardLogUpperBelowSeven pB * omM⁻¹ :=
        mul_le_mul_of_nonpos_left hinv hubp
  unfold tangentXLog backwardXLogUpperSevenNine
  dsimp only
  rw [Real.exp_neg, Real.exp_log hom]
  dsimp [p, om, pB, omM] at hfirst hlogom ⊢
  linarith

lemma tangent_xlog_le_backward_tangent_nine
    {β pCenter omCenter B z : ℝ}
    (hβ : 0 ≤ β) (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hpCenter : pCenter ∈ Set.Ioc (0 : ℝ) 1)
    (homCenter : omCenter ∈ Set.Ioc (0 : ℝ) 1)
    (hB0 : 0 ≤ B) (hB : B ≤ tangentBlue β z)
    (hB1 : B < 1) :
    tangentXLog β z ≤
      backwardXLogTangentUpper pCenter omCenter B z := by
  have happrox := KernelBounds.exp_neg_approx hz
  have hM :
      backwardMuLowerNine z ≤ optimizationM z := by
    unfold backwardMuLowerNine optimizationM
    exact mul_le_mul_of_nonneg_left
      (by linarith [abs_le.mp happrox]) hz.1
  have hM0 : 0 ≤ backwardMuLowerNine z := by
    unfold backwardMuLowerNine
    exact mul_nonneg hz.1 (backward_exp_lower_nine_nonneg hz)
  have hM1 : backwardMuLowerNine z < 1 :=
    hM.trans_lt (optimizationM_lt_one_of_Icc hz.1 hz.2)
  let p : ℝ := 1 - tangentBlue β z
  let om : ℝ := 1 - optimizationM z
  let pB : ℝ := 1 - B
  let omM : ℝ := 1 - backwardMuLowerNine z
  have hp : 0 < p :=
    sub_pos.mpr (tangentBlue_lt_one hβ hz.1 hz.2)
  have hom : 0 < om :=
    sub_pos.mpr (optimizationM_lt_one_of_Icc hz.1 hz.2)
  have hpB : 0 < pB := by dsimp [pB]; linarith
  have homM : 0 < omM := by dsimp [omM]; linarith
  have hp_le : p ≤ pB := by dsimp [p, pB]; linarith
  have hom_le : om ≤ omM := by dsimp [om, omM]; linarith
  have hlogp :
      Real.log p ≤
        backwardLogTangentUpper pCenter pB :=
    (Real.strictMonoOn_log.monotoneOn hp hpB hp_le).trans
      (backward_log_tangent_upper hpCenter hpB)
  have hlogom :
      Real.log om ≤
        backwardLogTangentUpper omCenter omM :=
    (Real.strictMonoOn_log.monotoneOn hom homM hom_le).trans
      (backward_log_tangent_upper homCenter homM)
  have hinv : omM⁻¹ ≤ om⁻¹ :=
    (inv_le_inv₀ homM hom).mpr hom_le
  have hblue0 : 0 ≤ tangentBlue β z := by
    unfold tangentBlue
    exact mul_nonneg hz.1 (Real.exp_pos _).le
  have hp1 : p ≤ 1 := by
    dsimp [p]
    linarith
  have hlogp0 : Real.log p ≤ 0 :=
    Real.log_nonpos hp.le hp1
  have hfirst :
      Real.log p * om⁻¹ ≤
        backwardLogTangentUpper pCenter pB * omM⁻¹ := by
    calc
      Real.log p * om⁻¹ ≤ Real.log p * omM⁻¹ :=
        mul_le_mul_of_nonpos_left hinv hlogp0
      _ ≤ backwardLogTangentUpper pCenter pB * omM⁻¹ :=
        mul_le_mul_of_nonneg_right hlogp (inv_nonneg.mpr homM.le)
  unfold tangentXLog backwardXLogTangentUpper
  dsimp only
  rw [Real.exp_neg, Real.exp_log hom]
  dsimp [p, om, pB, omM] at hfirst hlogom ⊢
  linarith

lemma tangent_xlog_le_backward {β B z : ℝ}
    (hβ : 0 ≤ β) (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hB0 : 0 ≤ B) (hB : B ≤ tangentBlue β z)
    (hB1 : B < 1) :
    tangentXLog β z ≤ backwardXLogUpper B z := by
  have happrox := backward_exp_approx5 hz
  have hM :
      backwardMuLower z ≤ optimizationM z := by
    unfold backwardMuLower backwardExpLower5 optimizationM
    exact mul_le_mul_of_nonneg_left
      (by linarith [abs_le.mp happrox]) hz.1
  have hM0 : 0 ≤ backwardMuLower z := by
    unfold backwardMuLower
    exact mul_nonneg hz.1 (backward_exp_lower5_nonneg hz)
  have hM1 : backwardMuLower z < 1 :=
    hM.trans_lt (optimizationM_lt_one_of_Icc hz.1 hz.2)
  let p : ℝ := 1 - tangentBlue β z
  let om : ℝ := 1 - optimizationM z
  let pB : ℝ := 1 - B
  let omM : ℝ := 1 - backwardMuLower z
  have hp : 0 < p :=
    sub_pos.mpr (tangentBlue_lt_one hβ hz.1 hz.2)
  have hom : 0 < om :=
    sub_pos.mpr (optimizationM_lt_one_of_Icc hz.1 hz.2)
  have hpB : 0 < pB := by dsimp [pB]; linarith
  have homM : 0 < omM := by dsimp [omM]; linarith
  have hp_le : p ≤ pB := by dsimp [p, pB]; linarith
  have hom_le : om ≤ omM := by dsimp [om, omM]; linarith
  have hlogp :
      Real.log p ≤ backwardLogUpperBelowFive pB := by
    exact (Real.strictMonoOn_log.monotoneOn hp hpB hp_le).trans
      (backward_log_upper_below_five hpB (by
        dsimp [pB]
        linarith))
  have hlogom :
      Real.log om ≤ backwardLogUpperBelowFive omM := by
    exact (Real.strictMonoOn_log.monotoneOn hom homM hom_le).trans
      (backward_log_upper_below_five homM (by
        dsimp [omM]
        linarith))
  have hubp : backwardLogUpperBelowFive pB ≤ 0 := by
    have hy0 : 0 ≤ 1 - pB := by
      simpa [pB] using hB0
    dsimp [backwardLogUpperBelowFive]
    exact neg_nonpos.mpr (by positivity)
  have hinv : omM⁻¹ ≤ om⁻¹ :=
    (inv_le_inv₀ homM hom).mpr hom_le
  have hfirst :
      Real.log p * om⁻¹ ≤
        backwardLogUpperBelowFive pB * omM⁻¹ := by
    calc
      Real.log p * om⁻¹ ≤
          backwardLogUpperBelowFive pB * om⁻¹ :=
        mul_le_mul_of_nonneg_right hlogp (inv_nonneg.mpr hom.le)
      _ ≤ backwardLogUpperBelowFive pB * omM⁻¹ :=
        mul_le_mul_of_nonpos_left hinv hubp
  unfold tangentXLog backwardXLogUpper
  dsimp only
  rw [Real.exp_neg, Real.exp_log hom]
  dsimp [p, om, pB, omM] at hfirst hlogom ⊢
  linarith

end

end Arxiv2407_19026
