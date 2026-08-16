import Arxiv.Arxiv2407_19026.NumericalProfilesLimitScaledCertificateOne
import Arxiv.Arxiv2407_19026.NumericalProfilesLimitScaledCertificateTwo
import Arxiv.Arxiv2407_19026.NumericalProfilesLimitScaledCertificateThree
import Arxiv.Arxiv2407_19026.NumericalProfilesLimitScaledCertificateFour

/-!
# Positivity of the first-profile limit polynomial

The exact Bernstein certificates on four adjacent intervals imply that the
rational numerator used in the analytic limit estimate is at least one on
`[3 / 1000, 1]`.
-/

namespace Arxiv2407_19026

noncomputable section

private lemma beta0_limit_numerator_ge_one_of_certificate
    {left width : ℚ} {scale : ℕ} {coefficients : List ℕ}
    {z u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hz : z = (left : ℝ) + (width : ℝ) * u)
    (hcertificate :
      ∀ x,
        rationalPowerEval
            (rationalPowerComp beta0LimitReservePower
              [left, width]) x =
          beta0LimitBernsteinValue 128 coefficients x / scale) :
    1 ≤ beta0LimitNumerator z := by
  have hnonnegative :=
    beta0LimitBernsteinValue_nonneg 128 coefficients hu
  have hevaluation := hcertificate u
  rw [rationalPowerEval_comp] at hevaluation
  have haffine :
      rationalPowerEval [left, width] u =
        (left : ℝ) + (width : ℝ) * u := by
    simp [rationalPowerEval]
    ring
  rw [haffine, ← hz] at hevaluation
  have hreserve :
      0 ≤ rationalPowerEval beta0LimitReservePower z := by
    rw [hevaluation]
    exact div_nonneg hnonnegative (Nat.cast_nonneg _)
  rw [beta0_limit_reserve_power_eval] at hreserve
  linarith

lemma beta0_limit_numerator_ge_one
    {z : ℝ} (hz : z ∈ Set.Icc (3 / 1000 : ℝ) 1) :
    1 ≤ beta0LimitNumerator z := by
  by_cases h₁ : z ≤ 1 / 100
  · let u : ℝ := (1000 * z - 3) / 7
    have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
      dsimp [u]
      constructor <;> nlinarith [hz.1, h₁]
    apply beta0_limit_numerator_ge_one_of_certificate hu
      (left := 3 / 1000) (width := 7 / 1000)
      (scale := beta0LimitScaleOneFast)
      (coefficients := beta0LimitCoeffsOneFast)
    · dsimp [u]
      norm_num
      ring
    · exact beta0_limit_one_evaluation
  by_cases h₂ : z ≤ 1 / 10
  · let u : ℝ := (100 * z - 1) / 9
    have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
      dsimp [u]
      constructor <;> nlinarith [lt_of_not_ge h₁, h₂]
    apply beta0_limit_numerator_ge_one_of_certificate hu
      (left := 1 / 100) (width := 9 / 100)
      (scale := beta0LimitScaleTwoFast)
      (coefficients := beta0LimitCoeffsTwoFast)
    · dsimp [u]
      norm_num
      ring
    · exact beta0_limit_two_evaluation
  by_cases h₃ : z ≤ 1 / 2
  · let u : ℝ := (10 * z - 1) / 4
    have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
      dsimp [u]
      constructor <;> nlinarith [lt_of_not_ge h₂, h₃]
    apply beta0_limit_numerator_ge_one_of_certificate hu
      (left := 1 / 10) (width := 2 / 5)
      (scale := beta0LimitScaleThreeFast)
      (coefficients := beta0LimitCoeffsThreeFast)
    · dsimp [u]
      norm_num
      ring
    · exact beta0_limit_three_evaluation
  · let u : ℝ := 2 * z - 1
    have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
      dsimp [u]
      constructor <;> nlinarith [lt_of_not_ge h₃, hz.2]
    apply beta0_limit_numerator_ge_one_of_certificate hu
      (left := 1 / 2) (width := 1 / 2)
      (scale := beta0LimitScaleFourFast)
      (coefficients := beta0LimitCoeffsFourFast)
    · dsimp [u]
      norm_num
      ring
    · exact beta0_limit_four_evaluation

private lemma beta0_limit_v_sub_exp_upper_lower
    {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    (1 / 10 : ℝ) ≤ beta0VLarge z - expNegUpper z := by
  have hnonnegative :=
    beta0LimitBernsteinValue_nonneg 10
      [683249503928040, 5555925309277791,
        20599400415496014, 46042752079465911,
        68691159818464743, 71362112478929559,
        52212754221850971, 26536896272745981,
        8954766265693275, 1809811805987179,
        166167549098378] hz
  have hidentity :
      beta0VLarge z - expNegUpper z - 1 / 10 =
        beta0LimitBernsteinValue 10
            [683249503928040, 5555925309277791,
              20599400415496014, 46042752079465911,
              68691159818464743, 71362112478929559,
              52212754221850971, 26536896272745981,
              8954766265693275, 1809811805987179,
              166167549098378] z /
          567000000000000 := by
    norm_num [beta0LimitBernsteinValue, beta0VLarge, expNegUpper,
      KernelBounds.expNegTaylor9, KernelBounds.expNegError10]
    ring
  rw [← sub_nonneg, hidentity]
  positivity

private lemma beta0_limit_a_lower_lower
    {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    (1 / 2 : ℝ) ≤ beta0LimitALower z := by
  have hnonnegative :=
    beta0LimitBernsteinValue_nonneg 11
      [18144000, 163296000, 671328000, 1669248000,
        2800224000, 3343032000, 2912414400,
        1859709600, 855597600, 270366300,
        52738300, 4794389] hz
  have hidentity :
      beta0LimitALower z - 1 / 2 =
        beta0LimitBernsteinValue 11
            [18144000, 163296000, 671328000, 1669248000,
              2800224000, 3343032000, 2912414400,
              1859709600, 855597600, 270366300,
              52738300, 4794389] z /
          36288000 := by
    norm_num [beta0LimitBernsteinValue, beta0LimitALower, expNegUpper,
      KernelBounds.expNegTaylor9, KernelBounds.expNegError10]
    ring
  rw [← sub_nonneg, hidentity]
  positivity

private lemma beta0_limit_log_fraction_identity
    {q : ℝ} (hb : 2 - q ≠ 0)
    (hdifference : (2 - q) ^ 2 - q ^ 2 ≠ 0) :
    (-2 *
          (15 * q * (2 - q) ^ 2 *
              ((2 - q) ^ 2 - q ^ 2) +
            5 * q ^ 3 * ((2 - q) ^ 2 - q ^ 2) +
            3 * q ^ 5)) /
        (15 * (2 - q) ^ 3 *
          ((2 - q) ^ 2 - q ^ 2)) =
      logLowerBelowTwoSharp (1 - q) := by
  unfold logLowerBelowTwoSharp
  have hratio :
      (1 - (1 - q)) / (1 + (1 - q)) = q / (2 - q) := by
    ring
  rw [hratio]
  have htail :
      1 - (q / (2 - q)) ^ 2 ≠ 0 := by
    rw [show 1 - (q / (2 - q)) ^ 2 =
        ((2 - q) ^ 2 - q ^ 2) / (2 - q) ^ 2 by
      field_simp [hb]]
    exact div_ne_zero hdifference (pow_ne_zero 2 hb)
  field_simp [hb, hdifference, htail]
  ring

lemma beta0_polynomial_limit_log_margin_large_pos
    {z : ℝ} (hz : z ∈ Set.Ioc (3 / 1000 : ℝ) 1) :
    0 < beta0PolynomialLimitLogMargin z := by
  have hzIcc : z ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith [hz.1], hz.2⟩
  have hzcut : ¬z ≤ (3 / 1000 : ℝ) :=
    not_le.mpr hz.1
  let exponential : ℝ := Real.exp (-z)
  let a : ℝ := 1 - z * exponential
  let x : ℝ := 1 - z * beta0VLarge z
  let d : ℝ := z * (beta0VLarge z - exponential)
  let s : ℝ := d / (2 * a - d)
  let t : ℝ :=
    beta0LimitDLower z / beta0LimitSDenominator z
  let series : ℝ → ℝ :=
    fun y => y + y ^ 3 / 3 + y ^ 5 / 5 + y ^ 7 / 7
  have hpLower := Beta0Affine.p_lower z hzIcc
  have hpPos : 0 < beta0PolynomialP z := by
    linarith
  have hpUpper : beta0PolynomialP z ≤ 1 := by
    have huLower := Beta0Affine.u_lower z hzIcc
    have huNonnegative : 0 ≤ beta0U z := by
      linarith
    unfold beta0PolynomialP
    nlinarith [mul_nonneg hzIcc.1 huNonnegative]
  have hxLower := Beta0Affine.x_lower z hzIcc
  rw [beta0PolynomialX, beta0V, if_neg hzcut] at hxLower
  have hxPos : 0 < x := by
    dsimp [x]
    linarith
  have hexpApprox := KernelBounds.exp_neg_approx hzIcc
  have hexpLower : beta0LimitExpLower z ≤ exponential := by
    have h := (abs_le.mp hexpApprox).1
    dsimp [exponential, beta0LimitExpLower]
    linarith
  have hexpUpper : exponential ≤ expNegUpper z := by
    have h := (abs_le.mp hexpApprox).2
    dsimp [exponential, expNegUpper]
    linarith
  have haLower : beta0LimitALower z ≤ a := by
    have hmul :=
      mul_le_mul_of_nonneg_left hexpUpper hzIcc.1
    dsimp [a, beta0LimitALower]
    linarith
  have haUpper : a ≤ beta0LimitAUpper z := by
    have hmul :=
      mul_le_mul_of_nonneg_left hexpLower hzIcc.1
    dsimp [a, beta0LimitAUpper]
    linarith
  have haLowerPos : 0 < beta0LimitALower z := by
    linarith [beta0_limit_a_lower_lower hzIcc]
  have haPos : 0 < a :=
    lt_of_lt_of_le haLowerPos haLower
  have hdLowerPos : 0 < beta0LimitDLower z := by
    have hgap :=
      beta0_limit_v_sub_exp_upper_lower hzIcc
    dsimp [beta0LimitDLower]
    exact mul_pos (by linarith [hz.1]) (by linarith)
  have hdLower : beta0LimitDLower z ≤ d := by
    have hgap :
        beta0VLarge z - expNegUpper z ≤
          beta0VLarge z - exponential := by
      linarith
    have hmul :=
      mul_le_mul_of_nonneg_left hgap hzIcc.1
    simpa [beta0LimitDLower, d] using hmul
  have hdIdentity : d = a - x := by
    dsimp [d, a, x]
    ring
  have hdPos : 0 < d :=
    lt_of_lt_of_le hdLowerPos hdLower
  have hactualDenominator :
      2 * a - d = a + x := by
    rw [hdIdentity]
    ring
  have hactualDenominatorPos : 0 < 2 * a - d := by
    rw [hactualDenominator]
    positivity
  have hsNonnegative : 0 ≤ s :=
    div_nonneg hdPos.le hactualDenominatorPos.le
  have hsLessOne : s < 1 := by
    rw [div_lt_one hactualDenominatorPos]
    rw [hdIdentity]
    linarith
  have hsDenominator :
      beta0LimitSDenominator z ≥ 2 * a - d := by
    dsimp [beta0LimitSDenominator]
    linarith
  have hsDenominatorPos :
      0 < beta0LimitSDenominator z :=
    lt_of_lt_of_le hactualDenominatorPos hsDenominator
  have htNonnegative : 0 ≤ t :=
    div_nonneg hdLowerPos.le hsDenominatorPos.le
  have htLe : t ≤ s := by
    rw [div_le_div_iff₀ hsDenominatorPos
      hactualDenominatorPos]
    have hleft :
        beta0LimitDLower z * (2 * a - d) ≤
          d * (2 * a - d) :=
      mul_le_mul_of_nonneg_right hdLower
        hactualDenominatorPos.le
    have hright :
        d * (2 * a - d) ≤
          d * beta0LimitSDenominator z :=
      mul_le_mul_of_nonneg_left hsDenominator hdPos.le
    exact hleft.trans hright
  have hseriesNonnegative : 0 ≤ series t := by
    dsimp [series]
    positivity
  have hseriesMonotone : series t ≤ series s := by
    have hpowThree := pow_le_pow_left₀ htNonnegative htLe 3
    have hpowFive := pow_le_pow_left₀ htNonnegative htLe 5
    have hpowSeven := pow_le_pow_left₀ htNonnegative htLe 7
    dsimp [series]
    linarith
  have hlogSeries :=
    Real.sum_range_le_log_div hsNonnegative hsLessOne 4
  have hlogSeries' :
      2 * series s ≤
        Real.log ((1 + s) / (1 - s)) := by
    norm_num [Finset.sum_range_succ, series] at hlogSeries ⊢
    linarith
  have hsRatio : (1 + s) / (1 - s) = a / x := by
    dsimp [s]
    rw [hdIdentity]
    rw [show 2 * a - (a - x) = a + x by ring]
    have hsumPos : 0 < a + x := add_pos haPos hxPos
    have hdenominator :
        1 - (a - x) / (a + x) ≠ 0 := by
      rw [sub_ne_zero]
      exact ne_of_gt ((div_lt_one hsumPos).2 (by linarith))
    rw [div_eq_iff hdenominator]
    field_simp [hxPos.ne', hsumPos.ne']
    ring
  have hlogRatio :
      Real.log ((1 + s) / (1 - s)) =
        Real.log a - Real.log x := by
    rw [hsRatio, Real.log_div haPos.ne' hxPos.ne']
  have hreserveEstimate :
      2 * beta0LimitALower z * series t ≤
        -a * (Real.log x - Real.log a) := by
    calc
      2 * beta0LimitALower z * series t ≤
          2 * a * series t := by
        exact mul_le_mul_of_nonneg_right
          (by linarith [haLower]) hseriesNonnegative
      _ ≤ 2 * a * series s :=
        mul_le_mul_of_nonneg_left hseriesMonotone
          (by positivity)
      _ ≤ a * Real.log ((1 + s) / (1 - s)) := by
        nlinarith [mul_le_mul_of_nonneg_left
          hlogSeries' haPos.le]
      _ = -a * (Real.log x - Real.log a) := by
        rw [hlogRatio]
        ring
  have hlogDenominatorPos :
      0 < beta0LimitLogDenominator z := by
    have hqNonnegative :
        0 ≤ beta0LimitQ z := by
      have huLower := Beta0Affine.u_lower z hzIcc
      exact mul_nonneg hzIcc.1 (by linarith)
    have hqUpper :
        beta0LimitQ z ≤ 1 / 2 := by
      dsimp [beta0LimitQ, beta0PolynomialP] at hpLower ⊢
      linarith
    have hbPos : 0 < beta0LimitB z := by
      dsimp [beta0LimitB]
      linarith
    have hdifferencePos :
        0 <
          beta0LimitB z ^ 2 - beta0LimitQ z ^ 2 := by
      dsimp [beta0LimitB]
      nlinarith
    dsimp [beta0LimitLogDenominator]
    positivity
  have hreserveDenominatorPos :
      0 < beta0LimitReserveDenominator z := by
    dsimp [beta0LimitReserveDenominator]
    positivity
  have hlogIdentity :
      beta0LimitLogNumerator z /
          beta0LimitLogDenominator z =
        logLowerBelowTwoSharp (beta0PolynomialP z) := by
    have hbNe : beta0LimitB z ≠ 0 := by
      have hqUpper :
          beta0LimitQ z ≤ 1 / 2 := by
        dsimp [beta0LimitQ, beta0PolynomialP] at hpLower ⊢
        linarith
      dsimp [beta0LimitB]
      linarith
    have hdifferenceNe :
        beta0LimitB z ^ 2 - beta0LimitQ z ^ 2 ≠ 0 := by
      have hqNonnegative :
          0 ≤ beta0LimitQ z := by
        have huLower := Beta0Affine.u_lower z hzIcc
        exact mul_nonneg hzIcc.1 (by linarith)
      have hqUpper :
          beta0LimitQ z ≤ 1 / 2 := by
        dsimp [beta0LimitQ, beta0PolynomialP] at hpLower ⊢
        linarith
      have hidentity :
          beta0LimitB z ^ 2 - beta0LimitQ z ^ 2 =
            4 * (1 - beta0LimitQ z) := by
        unfold beta0LimitB
        ring
      rw [hidentity]
      positivity
    simpa [beta0LimitLogNumerator,
      beta0LimitLogDenominator, beta0LimitB,
      beta0PolynomialP, beta0LimitQ] using
      (beta0_limit_log_fraction_identity
        (q := beta0LimitQ z) hbNe hdifferenceNe)
  have hlogEstimate :
      beta0LimitLogNumerator z /
          beta0LimitLogDenominator z ≤
        Real.log (beta0PolynomialP z) := by
    rw [hlogIdentity]
    exact log_lower_below_two_sharp hpPos hpUpper
  have hreserveIdentity :
      beta0LimitReserveNumerator z /
          beta0LimitReserveDenominator z =
        2 * beta0LimitALower z * series t := by
    dsimp [beta0LimitReserveNumerator,
      beta0LimitReserveDenominator, series, t]
    field_simp [hsDenominatorPos.ne']
    ring
  have hcombinedIdentity :
      beta0LimitNumerator z / beta0LimitDenominator z =
        beta0LimitLogNumerator z /
            beta0LimitLogDenominator z +
          beta0LimitReserveNumerator z /
            beta0LimitReserveDenominator z := by
    dsimp [beta0LimitNumerator, beta0LimitDenominator]
    field_simp [hlogDenominatorPos.ne',
      hreserveDenominatorPos.ne']
  have hlowerPos :
      0 <
        beta0LimitNumerator z /
          beta0LimitDenominator z := by
    have hnumerator :=
      beta0_limit_numerator_ge_one
        ⟨le_of_lt hz.1, hz.2⟩
    have hdenominator :
        0 < beta0LimitDenominator z := by
      dsimp [beta0LimitDenominator]
      positivity
    exact div_pos (by linarith) hdenominator
  have hmarginLower :
      beta0LimitNumerator z / beta0LimitDenominator z ≤
        Real.log (beta0PolynomialP z) -
          a * (Real.log x - Real.log a) := by
    rw [hcombinedIdentity, hreserveIdentity]
    linarith
  have htarget :
      beta0PolynomialLimitLogMargin z =
        Real.log (beta0PolynomialP z) -
          a * (Real.log x - Real.log a) := by
    dsimp [beta0PolynomialLimitLogMargin, a, x, exponential]
    rw [beta0PolynomialX, beta0V, if_neg hzcut]
    unfold optimizationM
    rfl
  rw [htarget]
  exact lt_of_lt_of_le hlowerPos hmarginLower

end

end Arxiv2407_19026
