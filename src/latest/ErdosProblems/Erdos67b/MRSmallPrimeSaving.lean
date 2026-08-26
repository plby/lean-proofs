import ErdosProblems.Erdos67b.MRSampleCountSaving

/-!
# Small additional prime: explicit logarithmic energy budget

The count saving pays the sparse cofactor term when the extra prime
endpoint has the displayed small-power bound. The resulting integral
estimate still concerns only the small-prime part of the exceptional set.
-/

namespace Erdos67b

open MeasureTheory

noncomputable section

theorem mrSqrt_two_mul_le_exp_log {T : ℝ} (hT : 0 < T) :
    Real.sqrt (2 * T) ≤ 2 * Real.exp (Real.log T / 2) := by
  have he := Real.exp_pos (Real.log T / 2)
  have hs := Real.sq_sqrt (show 0 ≤ 2 * T by positivity)
  have hexp : Real.exp (Real.log T / 2) ^ 2 = T := by
    rw [← Real.exp_nat_mul]
    rw [show (2 : ℕ) * (Real.log T / 2) = Real.log T by norm_num; ring]
    exact Real.exp_log hT
  nlinarith [Real.sqrt_nonneg (2 * T)]

theorem mrSparseCount_scale_le_two
    {eta R M T : ℝ} (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    {U X : ℕ} (hX : 0 < X) (hR : R = Real.log (X : ℝ)) (hR0 : 0 ≤ R)
    (hT : 1 ≤ T) (hTX : T ≤ X)
    (hM : M ≤ Real.exp (eta * R / 4) * Real.exp ((1 / 2 - eta) * Real.log T))
    (hU : (U : ℝ) ≤ Real.exp (eta * R / 4)) :
    M * U / X * Real.sqrt (2 * T) ≤ 2 := by
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hTr : 0 < T := by linarith
  have hexpR : Real.exp R = X := by rw [hR, Real.exp_log hXr]
  have hlogT : Real.log T ≤ R := by
    rw [hR]
    exact Real.log_le_log hTr hTX
  have hmul := mul_le_mul hM hU (by positivity : (0 : ℝ) ≤ U) (by positivity)
  have hdiv := div_le_div_of_nonneg_right hmul hXr.le
  have hroot := mrSqrt_two_mul_le_exp_log hTr
  have hwhole := mul_le_mul hdiv hroot (Real.sqrt_nonneg _) (by positivity)
  calc
    _ ≤ ((Real.exp (eta * R / 4) * Real.exp ((1 / 2 - eta) * Real.log T)) *
        Real.exp (eta * R / 4) / X) * (2 * Real.exp (Real.log T / 2)) := hwhole
    _ = 2 * Real.exp (eta * R / 2 - R + (1 - eta) * Real.log T) := by
      rw [← hexpR, div_eq_mul_inv, ← Real.exp_neg]
      rw [show eta * R / 2 - R + (1 - eta) * Real.log T =
        eta * R / 4 + (1 / 2 - eta) * Real.log T + eta * R / 4 + -R + Real.log T / 2 by ring]
      simp only [Real.exp_add]
      ring
    _ ≤ 2 * Real.exp (-eta * R / 2) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
      have hh := mul_le_mul_of_nonneg_left hlogT (show 0 ≤ 1 - eta by linarith)
      linarith
    _ ≤ 2 := by
      have hh : Real.exp (-eta * R / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      linarith

theorem mrSparseCofactor_log_factors
    {T R : ℝ} {X : ℕ} (hX : 0 < X) (hR : R = Real.log (X : ℝ))
    (hR1 : 1 ≤ R) (hT : 1 ≤ T) (hTX : T ≤ X) :
    1 + Real.log (2 * T + 1) ≤ 4 * R ∧ 1 + Real.log (16 * T) ≤ 6 * R := by
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hX1 : (1 : ℝ) ≤ X := hT.trans hTX
  have hlog3 : Real.log 3 ≤ 2 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hfirst : Real.log (2 * T + 1) ≤ Real.log 3 + R := by
    calc
      _ ≤ Real.log (3 * (X : ℝ)) := Real.log_le_log (by linarith) (by linarith)
      _ = _ := by rw [Real.log_mul (by norm_num) hXr.ne', ← hR]
  have hsecond : Real.log (16 * T) ≤ 4 * Real.log 2 + R := by
    calc
      _ ≤ Real.log (16 * (X : ℝ)) := Real.log_le_log (by linarith) (by linarith)
      _ = _ := by
        rw [Real.log_mul (by norm_num) hXr.ne', ← hR,
          show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
        norm_num
  constructor <;> linarith

def mrSmallPrimeLogConstant : ℝ := 230416 + 768 * Real.pi

theorem mrSmallPrimeLogConstant_pos : 0 < mrSmallPrimeLogConstant := by
  unfold mrSmallPrimeLogConstant
  positivity

theorem mrAuxiliary_log_upper_le_small_power
    {eta R : ℝ} (heta : 0 < eta) (hR : 8 / eta ≤ R)
    (hlogR : 8 / eta ≤ Real.log R) : R / Real.log R + 1 ≤ eta * R / 4 := by
  have hfrac : 0 < 8 / eta := div_pos (by norm_num) heta
  have hR0 : 0 ≤ R := by linarith
  have hL : 0 < Real.log R := lt_of_lt_of_le hfrac hlogR
  have hpaid : 8 ≤ R * eta := (div_le_iff₀ heta).mp hR
  have hpaidlog : 8 ≤ Real.log R * eta := (div_le_iff₀ heta).mp hlogR
  have hdiv : R / Real.log R ≤ eta * R / 8 := by
    apply (div_le_iff₀ hL).mpr
    nlinarith [mul_le_mul_of_nonneg_left hpaidlog hR0]
  linarith

theorem mrNarrowPrimeInterval_upper_le_small_power
    {eta R H : ℝ} (heta : 0 < eta) (hR : 8 / eta ≤ R)
    (hlogR : 8 / eta ≤ Real.log R) (hH : 1 ≤ H)
    {r : ℕ} (hr : (r : ℝ) / H ≤ R / Real.log R) :
    ((mrNarrowPrimeInterval H r).2 : ℝ) ≤ Real.exp (eta * R / 4) := by
  apply (mrNarrowPrimeInterval_upper_le_exp_shift hH r).trans
  apply Real.exp_le_exp.mpr
  have hh := mrAuxiliary_log_upper_le_small_power heta hR hlogR
  linarith

theorem mrSmallPrime_inverse_power_budget {R : ℝ} (hR : 0 < R) :
    2 * mrSmallPrimeLogConstant * ((R ^ 100)⁻¹) ^ 2 * R ^ 2 =
      2 * mrSmallPrimeLogConstant / R ^ 198 := by
  rw [inv_pow, ← pow_mul, show 100 * 2 = 198 + 2 by norm_num, pow_add, mul_inv]
  field_simp

theorem mrSparseCofactorSampleBudget_le_log_sq
    {M T R : ℝ} {U X : ℕ} (hX : 0 < X)
    (hR : R = Real.log (X : ℝ)) (hR1 : 1 ≤ R) (hT : 1 ≤ T) (hTX : T ≤ X)
    (hscale : M * U / X * Real.sqrt (2 * T) ≤ 2) :
    mrSparseCofactorSampleBudget M U X T ≤ mrSmallPrimeLogConstant * R ^ 2 := by
  have hlogs := mrSparseCofactor_log_factors hX hR hR1 hT hTX
  have hlog0 : 0 ≤ 1 + Real.log (16 * T) := by
    have hh := Real.log_nonneg (show 1 ≤ 16 * T by linarith)
    linarith
  have hsquare : (1 + Real.log (16 * T)) ^ 2 ≤ (6 * R) ^ 2 :=
    pow_le_pow_left₀ hlog0 hlogs.2 2
  have hsecond : 3200 * M * U / X * Real.sqrt (2 * T) * (1 + Real.log (16 * T)) ^ 2 ≤
      6400 * (6 * R) ^ 2 := by
    have hh := mul_le_mul hscale hsquare (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    have hh' := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 3200)
    calc
      _ = 3200 * ((M * U / X * Real.sqrt (2 * T)) * (1 + Real.log (16 * T)) ^ 2) := by ring
      _ ≤ 3200 * (2 * (6 * R) ^ 2) := hh'
      _ = _ := by ring
  have hfirst : 16 * (1 + 12 * Real.pi * (1 + Real.log (2 * T + 1))) ≤
      (16 + 768 * Real.pi) * R ^ 2 := by
    have hlog := mul_le_mul_of_nonneg_left hlogs.1 (show 0 ≤ 12 * Real.pi by positivity)
    have hR2 : R ≤ R ^ 2 := by nlinarith
    have hpi := mul_le_mul_of_nonneg_left hR2 (show 0 ≤ 768 * Real.pi by positivity)
    nlinarith [sq_nonneg (R - 1)]
  unfold mrSparseCofactorSampleBudget mrSmallPrimeLogConstant
  nlinarith

theorem mrExceptionalSmallPrimeEnergyBudget_le_log_sq
    {eta p₁ q₁ : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hq : 1 ≤ q₁) (hpq : p₁ ≤ q₁)
    (hlogq : 1 ≤ Real.log q₁) (hbudget : 4096 * Real.log q₁ ≤ eta * p₁)
    {J : ℕ} (hJ : 1 ≤ J) {U X : ℕ} (hX : 0 < X) {R T V : ℝ}
    (hR : R = Real.log (X : ℝ)) (hR1 : 1 ≤ R) (hT : 1 ≤ T) (hTX : T ≤ X)
    (hJR : mrLogScheduleUpper q₁ J ≤ Real.sqrt R)
    (hnext : Real.sqrt R ≤ mrLogScheduleUpper q₁ (J + 1))
    (hconstant : 8 * mrNoSmallCountConstant / eta ≤ R)
    (hsqrt : (56 / eta) ^ 2 ≤ R) (hU : (U : ℝ) ≤ Real.exp (eta * R / 4)) :
    mrExceptionalSmallPrimeEnergyBudget eta p₁ q₁ J U X T V ≤
      2 * mrSmallPrimeLogConstant * V ^ 2 * R ^ 2 := by
  have hTR : Real.log T ≤ R := by
    rw [hR]
    exact Real.log_le_log (by linarith) hTX
  have hcount := mrNoSmallOptimizedCountBudget_le_small_power heta0 heta1 hp hq hpq hlogq hbudget
    hJ hT hR1 hTR hJR hnext hconstant hsqrt
  have hscale := mrSparseCount_scale_le_two heta0.le (by linarith) hX hR (by linarith)
    hT hTX hcount hU
  have hcofactor := mrSparseCofactorSampleBudget_le_log_sq hX hR hR1 hT hTX hscale
  calc
    _ ≤ 2 * V ^ 2 * (mrSmallPrimeLogConstant * R ^ 2) :=
      mul_le_mul_of_nonneg_left hcofactor (by positivity)
    _ = _ := by ring

/-- The actual small-prime exceptional integral has a uniform logarithmic
budget at the explicitly selected final block and product scale. -/
theorem mrArithmetic_noSmall_smallPrime_integral_le_log_sq
    {eta p₁ q₁ : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hq : 1 ≤ q₁) (hpq : p₁ ≤ q₁)
    (hlogq : 1 ≤ Real.log q₁) (hbudget : 4096 * Real.log q₁ ≤ eta * p₁)
    {J : ℕ} (hJ : 1 ≤ J)
    (blocks : Finset (ℕ × ℕ)) (I Jaux : ℕ × ℕ) (P : Finset ℕ)
    (hL : 0 < Jaux.1) (hU : 0 < Jaux.2) (hUL : Jaux.2 ≤ 2 * Jaux.1)
    {X : ℕ} (hX : 0 < X) {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {T V R : ℝ} (hR : R = Real.log (X : ℝ)) (hR1 : 1 ≤ R)
    (hT : 1 ≤ T) (hTX : T ≤ X)
    (hJR : mrLogScheduleUpper q₁ J ≤ Real.sqrt R)
    (hnext : Real.sqrt R ≤ mrLogScheduleUpper q₁ (J + 1))
    (hconstant : 8 * mrNoSmallCountConstant / eta ≤ R)
    (hsqrt : (56 / eta) ^ 2 ≤ R)
    (haux : (Jaux.2 : ℝ) ≤ Real.exp (eta * R / 4)) :
    (∫ t in -T..T,
      (mrSmallPrimeFrequencySet
        (mrNoSmallFrequencyClass (mrArithmeticSmallFrequencySet eta p₁ q₁ f) J) P f V).indicator
        (fun t ↦ ‖logarithmicDirichletPolynomial P (mrFinitePrimeLineCoefficient f) t *
          logarithmicDirichletPolynomial (mrTypicalCofactorRectangle blocks I Jaux X)
            (mrFiniteCofactorLineCoefficient (primesInBlock I) f) t‖ ^ 2) t) ≤
      2 * mrSmallPrimeLogConstant * V ^ 2 * R ^ 2 := by
  exact (mrArithmetic_noSmall_smallPrime_integral_le heta0 heta1 hp hq hlogq hbudget hJ le_rfl
    blocks I Jaux P hL hU hUL hX hbound hT).trans
      (mrExceptionalSmallPrimeEnergyBudget_le_log_sq heta0 heta1 hp hq hpq hlogq hbudget
        hJ hX hR hR1 hT hTX hJR hnext hconstant hsqrt haux)

end

end Erdos67b
