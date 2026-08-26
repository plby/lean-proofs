import ErdosProblems.Erdos67b.MRExceptionalScale
import ErdosProblems.Erdos67b.MRSelectedSubblockScale

/-! # The actual small selected-prime branch at a fixed-power endpoint -/

open MeasureTheory
open scoped BigOperators Interval

namespace Erdos67b

noncomputable section

theorem mrSelectedSubblock_log_scale_upper {H b : ℝ} (hH : 0 < H)
    {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime)
    (hupper : ∀ p ∈ A, Real.log (p : ℝ) ≤ b) {s : ℕ}
    (hne : (mrPrimeSubblock H A s).Nonempty) : (s : ℝ) / H ≤ b := by
  obtain ⟨p, hp⟩ := hne
  have hpA := mrPrimeSubblock_subset H A s hp
  have hb := mrPrimeSubblock_real_bounds hH hA hp
  have hh := Real.log_le_log (Real.exp_pos _) hb.1
  rw [Real.log_exp] at hh
  exact hh.trans (hupper p hpA)

theorem mrSelectedNarrow_upper_le_small_power
    {eta theta L H : ℝ} (heta : 0 < eta) (hL : 0 ≤ L) (hH : 2 ≤ H)
    (htheta : theta ≤ eta / 8) (hlarge : 8 / eta ≤ L)
    {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime)
    (hupper : ∀ p ∈ A, Real.log (p : ℝ) ≤ theta * L) {s : ℕ}
    (hne : (mrPrimeSubblock H A s).Nonempty) :
    ((mrNarrowPrimeInterval H s).2 : ℝ) ≤ Real.exp (eta * L / 4) := by
  have hs := mrSelectedSubblock_log_scale_upper (by linarith : 0 < H) hA hupper hne
  have hmul := mul_le_mul_of_nonneg_right htheta hL
  have hpaid := (div_le_iff₀ heta).1 hlarge
  apply (mrNarrowPrimeInterval_upper_le_exp_shift (by linarith : 1 ≤ H) s).trans
  apply Real.exp_le_exp.mpr
  nlinarith

theorem mrSelectedSmallPrime_scaled_budget_le {L xi : ℝ} (hL : 1 ≤ L)
    (hxi : 0 < xi) (hlarge : 4 * mrSmallPrimeLogConstant / xi ≤ L) :
    L ^ 2 * (2 * mrSmallPrimeLogConstant * (Real.exp (-4 * Real.log L)) ^ 2 * L ^ 2) ≤
      xi / 2 := by
  have hLpos : 0 < L := by linarith
  have hC := mrSmallPrimeLogConstant_pos
  have hexp : Real.exp (-4 * Real.log L) = (L ^ 4)⁻¹ := by
    rw [neg_mul, Real.exp_neg]
    congr 1
    simpa only [Nat.cast_ofNat, Real.exp_log hLpos] using Real.exp_nat_mul (Real.log L) 4
  have hpaid := (div_le_iff₀ hxi).1 hlarge
  have hpow : L ≤ L ^ 4 := by nlinarith [sq_nonneg (L ^ 2 - 1)]
  calc
    _ = 2 * mrSmallPrimeLogConstant / L ^ 4 := by rw [hexp]; field_simp
    _ ≤ xi / 2 := by
      apply (div_le_iff₀ (pow_pos hLpos 4)).2
      nlinarith [mul_le_mul_of_nonneg_left hpow hxi.le]

theorem mrSelected_noSmall_smallPrime_integral_small
    {eta p₁ q₁ theta xi : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hq : 1 ≤ q₁) (hpq : p₁ ≤ q₁)
    (hlogq : 1 ≤ Real.log q₁) (hbudget : 4096 * Real.log q₁ ≤ eta * p₁)
    (htheta : theta ≤ eta / 8) (hxi : 0 < xi)
    {X J : ℕ} (hX : 2 ≤ X) (hJ : 1 ≤ J)
    (hscale : mrExceptionalLogScaleThreshold eta q₁ ≤ Real.log (X : ℝ))
    (hpaid : 4 * mrSmallPrimeLogConstant / xi ≤ Real.log (X : ℝ))
    (hupper : mrLogScheduleUpper q₁ J ≤ Real.sqrt (Real.log (X : ℝ)))
    (hnext : Real.sqrt (Real.log (X : ℝ)) ≤ mrLogScheduleUpper q₁ (J + 1))
    (I : ℕ × ℕ)
    (hIupper : ∀ p ∈ primesInBlock I, Real.log (p : ℝ) ≤ theta * Real.log (X : ℝ))
    {H : ℝ} (hH : 2 ≤ H) (s : ℕ)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) :
    (Real.log (X : ℝ)) ^ 2 *
      (∫ t in -((X : ℝ) / 2)..((X : ℝ) / 2),
        (mrSmallPrimeFrequencySet
          (mrNoSmallFrequencyClass (mrArithmeticSmallFrequencySet eta p₁ q₁ f) J)
          (mrPrimeSubblock H (primesInBlock I) s) f
          (Real.exp (-4 * Real.log (Real.log (X : ℝ))))).indicator
        (fun t ↦ ‖logarithmicDirichletPolynomial (mrPrimeSubblock H (primesInBlock I) s)
            (mrFinitePrimeLineCoefficient f) t *
          logarithmicDirichletPolynomial
            (mrTypicalCofactorRectangle (mrScheduledBlocks p₁ q₁ J) I
              (mrNarrowPrimeInterval H s) X)
            (mrFiniteCofactorLineCoefficient (primesInBlock I) f) t‖ ^ 2) t) ≤ xi / 2 := by
  classical
  obtain ⟨hL, _, hconstant, hsqrt, hlarge, _⟩ :=
    mrExceptionalLogScaleThreshold_spec heta0 hq hscale
  by_cases hne : (mrPrimeSubblock H (primesInBlock I) s).Nonempty
  · have haux := mrSelectedNarrow_upper_le_small_power heta0 (by linarith) hH htheta
      hlarge (fun p hp ↦ (mem_primesInBlock.mp hp).1) hIupper hne
    have hXr : (2 : ℝ) ≤ X := by exact_mod_cast hX
    have hh := mrArithmetic_noSmall_smallPrime_integral_le_log_sq
      (V := Real.exp (-4 * Real.log (Real.log (X : ℝ)))) heta0 heta1 hp hq hpq
      hlogq hbudget hJ (mrScheduledBlocks p₁ q₁ J) I (mrNarrowPrimeInterval H s)
      (mrPrimeSubblock H (primesInBlock I) s) (mrNarrowPrimeInterval_lower_pos _ _)
      (mrNarrowPrimeInterval_upper_pos (by linarith : 0 < H) s)
      (mrNarrowPrimeInterval_dyadic_width hH s) (by omega : 0 < X) hbound rfl hL
      (by linarith : 1 ≤ (X : ℝ) / 2) (by linarith : (X : ℝ) / 2 ≤ X)
      hupper hnext hconstant hsqrt haux
    exact (mul_le_mul_of_nonneg_left hh (sq_nonneg (Real.log (X : ℝ)))).trans
      (mrSelectedSmallPrime_scaled_budget_le hL hxi hpaid)
  · have hzero := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [hzero, logarithmicDirichletPolynomial, Finset.sum_empty, zero_mul, norm_zero,
      zero_pow (by norm_num : 2 ≠ 0), Set.indicator_zero,
      intervalIntegral.integral_zero, mul_zero]
    exact (half_pos hxi).le

end

end Erdos67b
