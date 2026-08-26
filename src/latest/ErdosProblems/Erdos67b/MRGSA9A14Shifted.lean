import ErdosProblems.Erdos67b.MRGSA9A14FullSeries
import ErdosProblems.Erdos67b.TwistSeparation

/-!
# The shifted A.13--A.14 Euler comparison

The A.10 contour evaluates the finite low-prime factor to the left of the
absolutely convergent high-prime factor.  This file records the elementary
cost of that displacement.  The cost is the horizontal gap times the
Chebyshev--Mertens sum `sum (log p) / p`; in the source contour this is an
absolute constant because the gap is `O(1 / log X)`.
-/

open scoped BigOperators LSeries.notation
open Complex

namespace Erdos67b.MRHalaszBands

noncomputable section

open BoundedGaps.Maynard

/-- Moving the real part of one prime monomial to the left costs its
logarithmic derivative at the line `re s = 1`. -/
theorem norm_nat_cpow_neg_low_sub_neg_high_le_log_div
    {p : ℕ} (hp : p.Prime) {sigmaLow sigmaHigh t : ℝ}
    (hlow : 1 ≤ sigmaLow) (hle : sigmaLow ≤ sigmaHigh) :
    ‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ))) -
        (p : ℂ) ^ (-((sigmaHigh : ℂ) + Complex.I * (t : ℂ)))‖ ≤
      (sigmaHigh - sigmaLow) * (Real.log p / (p : ℝ)) := by
  let d : ℝ := sigmaHigh - sigmaLow
  let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
  let sHigh : ℂ := (sigmaHigh : ℂ) + Complex.I * (t : ℂ)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hd : 0 ≤ d := sub_nonneg.mpr hle
  have hlogp : 0 ≤ Real.log (p : ℝ) := (Real.log_nonneg (by exact_mod_cast hp.one_le))
  have hfactor : (p : ℂ) ^ (-sLow) =
      (p : ℂ) ^ (d : ℂ) * (p : ℂ) ^ (-sHigh) := by
    rw [← Complex.cpow_add _ _ hpC]
    congr 1
    dsimp only [sLow, sHigh, d]
    push_cast
    ring
  have hrealPow : (p : ℂ) ^ (d : ℂ) = (((p : ℝ) ^ d : ℝ) : ℂ) := by
    exact (Complex.ofReal_cpow hpR.le d).symm
  have hpowOne : 1 ≤ (p : ℝ) ^ d := Real.one_le_rpow (by exact_mod_cast hp.one_le) hd
  have hexpPow : (p : ℝ) ^ d = Real.exp (d * Real.log p) := by
    rw [Real.rpow_def_of_pos hpR]
    congr 1
    ring
  have hx : 0 ≤ d * Real.log p := mul_nonneg hd hlogp
  have hexpSub : Real.exp (d * Real.log p) - 1 ≤
      (d * Real.log p) * Real.exp (d * Real.log p) := by
    have hone := Real.one_sub_le_exp_neg (d * Real.log p)
    have hmul := mul_le_mul_of_nonneg_left hone (Real.exp_pos (d * Real.log p)).le
    rw [mul_sub, mul_one, ← Real.exp_add] at hmul
    have hzero : d * Real.log p + -(d * Real.log p) = 0 := by ring
    rw [hzero, Real.exp_zero] at hmul
    nlinarith
  change ‖(p : ℂ) ^ (-sLow) - (p : ℂ) ^ (-sHigh)‖ ≤ _
  rw [hfactor]
  nth_rewrite 2 [← one_mul ((p : ℂ) ^ (-sHigh))]
  rw [← sub_mul, norm_mul, hrealPow, ← Complex.ofReal_one,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hpowOne)]
  have hnormHigh : ‖(p : ℂ) ^ (-sHigh)‖ =
      (p : ℝ) ^ (-sigmaHigh) := by
    dsimp only [sHigh]
    exact Erdos67b.HalaszCpowDeficit.norm_nat_cpow_neg_sigma_add_I_mul
      hp.pos sigmaHigh t
  rw [hnormHigh, hexpPow]
  have hpowHigh : (p : ℝ) ^ (-sigmaHigh) =
      Real.exp (-sigmaHigh * Real.log p) := by
    rw [Real.rpow_def_of_pos hpR]
    congr 1
    ring
  rw [hpowHigh]
  calc
    (Real.exp (d * Real.log p) - 1) *
          Real.exp (-sigmaHigh * Real.log p) ≤
        ((d * Real.log p) * Real.exp (d * Real.log p)) *
          Real.exp (-sigmaHigh * Real.log p) := by
      gcongr
    _ = d * Real.log p * Real.exp (-sigmaLow * Real.log p) := by
      calc
        (d * Real.log p * Real.exp (d * Real.log p)) *
              Real.exp (-sigmaHigh * Real.log p) =
            d * Real.log p *
              (Real.exp (d * Real.log p) *
                Real.exp (-sigmaHigh * Real.log p)) := by ring
        _ = d * Real.log p * Real.exp (-sigmaLow * Real.log p) := by
          rw [← Real.exp_add]
          congr 2
          dsimp only [d]
          ring
    _ ≤ d * Real.log p * ((p : ℝ)⁻¹) := by
      gcongr
      rw [← Real.rpow_neg_one, Real.rpow_def_of_pos hpR]
      apply Real.exp_le_exp.mpr
      calc
        -sigmaLow * Real.log p = sigmaLow * (-Real.log p) := by ring
        _ ≤ 1 * (-Real.log p) := by
          have := mul_le_mul_of_nonpos_right hlow (neg_nonpos.mpr hlogp)
          exact this
        _ = Real.log p * -1 := by ring
    _ = (sigmaHigh - sigmaLow) * (Real.log p / (p : ℝ)) := by
      dsimp only [d]
      rw [div_eq_mul_inv]
      ring

/-- The total horizontal displacement of all low primes is at most the gap
times the prime logarithmic harmonic sum. -/
theorem sum_norm_nat_cpow_neg_low_sub_neg_high_le
    {y : ℕ} {sigmaLow sigmaHigh t : ℝ}
    (hlow : 1 ≤ sigmaLow) (hle : sigmaLow ≤ sigmaHigh) :
    (∑ p ∈ primesUpTo y,
      ‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ))) -
        (p : ℂ) ^ (-((sigmaHigh : ℂ) + Complex.I * (t : ℂ)))‖) ≤
      (sigmaHigh - sigmaLow) * primeLogHarmonicSum y := by
  calc
    (∑ p ∈ primesUpTo y,
      ‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ))) -
        (p : ℂ) ^ (-((sigmaHigh : ℂ) + Complex.I * (t : ℂ)))‖) ≤
        ∑ p ∈ primesUpTo y,
          (sigmaHigh - sigmaLow) * (Real.log p / (p : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact norm_nat_cpow_neg_low_sub_neg_high_le_log_div
        (mem_primesUpTo.mp hp).1 hlow hle
    _ = (sigmaHigh - sigmaLow) * primeLogHarmonicSum y := by
      rw [← Finset.mul_sum]
      unfold primeLogHarmonicSum primesUpTo
      rw [Nat.primesLE_eq_filter_range]

/-- At the endpoint prime `2`, moving left within `Re s ≥ 1` costs at most
a factor two for an arbitrary one-bounded prime-power series.  This joint
comparison is the reason no spurious inverse distance from the line
`Re s = 1` appears in the shifted A.14 theorem. -/
theorem norm_localEulerSeries_shift_le_two
    (a : ℕ → ℂ) (ha0 : a 0 = 1) (ha : ∀ e, ‖a e‖ ≤ 1)
    {xLow xHigh : ℂ} {c : ℝ}
    (hc : 1 ≤ c) (hfactor : xLow = (c : ℂ) * xHigh)
    (hhalf : ‖xLow‖ ≤ (1 / 2 : ℝ)) :
    ‖∑' e : ℕ, a e * xLow ^ e‖ ≤
      2 * ‖∑' e : ℕ, a e * xHigh ^ e‖ := by
  let rLow : ℝ := ‖xLow‖
  let rHigh : ℝ := ‖xHigh‖
  have hrLow0 : 0 ≤ rLow := norm_nonneg _
  have hrHigh0 : 0 ≤ rHigh := norm_nonneg _
  have hrLow : rLow ≤ 1 / 2 := hhalf
  have hrLow1 : rLow < 1 := lt_of_le_of_lt hrLow (by norm_num)
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have hrFactor : rLow = c * rHigh := by
    dsimp only [rLow, rHigh]
    rw [hfactor, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hc0]
  have hrHigh : rHigh ≤ rLow := by
    rw [hrFactor]
    exact le_mul_of_one_le_left hrHigh0 hc
  have hrHigh1 : rHigh < 1 := hrHigh.trans_lt hrLow1
  have hgeomLow : Summable (fun e : ℕ ↦ rLow ^ e) :=
    summable_geometric_of_norm_lt_one (by
      simpa [Real.norm_eq_abs, abs_of_nonneg hrLow0] using hrLow1)
  have hgeomHigh : Summable (fun e : ℕ ↦ rHigh ^ e) :=
    summable_geometric_of_norm_lt_one (by
      simpa [Real.norm_eq_abs, abs_of_nonneg hrHigh0] using hrHigh1)
  have hnormLow : Summable (fun e : ℕ ↦ ‖a e * xLow ^ e‖) := by
    apply hgeomLow.of_nonneg_of_le (fun e ↦ norm_nonneg _)
    intro e
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (pow_nonneg hrLow0 e) (ha e)
  have hnormHigh : Summable (fun e : ℕ ↦ ‖a e * xHigh ^ e‖) := by
    apply hgeomHigh.of_nonneg_of_le (fun e ↦ norm_nonneg _)
    intro e
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (pow_nonneg hrHigh0 e) (ha e)
  have htermLow : Summable (fun e : ℕ ↦ a e * xLow ^ e) := hnormLow.of_norm
  have htermHigh : Summable (fun e : ℕ ↦ a e * xHigh ^ e) := hnormHigh.of_norm
  have hpowerDiff (e : ℕ) :
      ‖xLow ^ e - xHigh ^ e‖ = rLow ^ e - rHigh ^ e := by
    rw [hfactor, mul_pow]
    nth_rewrite 2 [← one_mul (xHigh ^ e)]
    rw [← sub_mul, norm_mul,
      ← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    have hcpow : 1 ≤ c ^ e := one_le_pow₀ hc
    rw [abs_of_nonneg (sub_nonneg.mpr hcpow), norm_pow, hrFactor, mul_pow]
    ring
  have hdiffNorm : Summable (fun e : ℕ ↦
      ‖a e * xLow ^ e - a e * xHigh ^ e‖) := by
    apply (hgeomLow.add hgeomHigh).of_nonneg_of_le (fun e ↦ norm_nonneg _)
    intro e
    rw [← mul_sub, norm_mul, hpowerDiff e]
    have hpow : rHigh ^ e ≤ rLow ^ e :=
      pow_le_pow_left₀ hrHigh0 hrHigh e
    have hdiff0 : 0 ≤ rLow ^ e - rHigh ^ e := sub_nonneg.mpr hpow
    calc
      ‖a e‖ * (rLow ^ e - rHigh ^ e) ≤
          1 * (rLow ^ e - rHigh ^ e) :=
        mul_le_mul_of_nonneg_right (ha e) hdiff0
      _ ≤ rLow ^ e + rHigh ^ e := by nlinarith [pow_nonneg hrHigh0 e]
  have hdiff :
      ‖(∑' e : ℕ, a e * xLow ^ e) -
          ∑' e : ℕ, a e * xHigh ^ e‖ ≤
        (∑' e : ℕ, rLow ^ e) - ∑' e : ℕ, rHigh ^ e := by
    rw [← htermLow.tsum_sub htermHigh]
    calc
      ‖∑' e : ℕ, (a e * xLow ^ e - a e * xHigh ^ e)‖ ≤
          ∑' e : ℕ, ‖a e * xLow ^ e - a e * xHigh ^ e‖ :=
        norm_tsum_le_tsum_norm hdiffNorm
      _ ≤ ∑' e : ℕ, (rLow ^ e - rHigh ^ e) := by
        apply Summable.tsum_le_tsum
        · intro e
          rw [← mul_sub, norm_mul, hpowerDiff e]
          exact mul_le_of_le_one_left
            (sub_nonneg.mpr (pow_le_pow_left₀ hrHigh0 hrHigh e)) (ha e)
        · exact hdiffNorm
        · exact hgeomLow.sub hgeomHigh
      _ = (∑' e : ℕ, rLow ^ e) - ∑' e : ℕ, rHigh ^ e :=
        hgeomLow.tsum_sub hgeomHigh
  have hsumLow : (∑' e : ℕ, rLow ^ e) = (1 - rLow)⁻¹ :=
    tsum_geometric_of_lt_one hrLow0 hrLow1
  have hsumHigh : (∑' e : ℕ, rHigh ^ e) = (1 - rHigh)⁻¹ :=
    tsum_geometric_of_lt_one hrHigh0 hrHigh1
  have hsumLowTwo : (∑' e : ℕ, rLow ^ e) ≤ 2 := by
    rw [hsumLow, inv_le_comm₀ (sub_pos.mpr hrLow1) (by norm_num)]
    linarith
  let tailHigh : ℂ := ∑' e : ℕ, a (e + 1) * xHigh ^ (e + 1)
  have htailNorm : Summable (fun e : ℕ ↦
      ‖a (e + 1) * xHigh ^ (e + 1)‖) :=
    hnormHigh.comp_injective (fun _ _ h ↦ Nat.add_right_cancel h)
  have htail : ‖tailHigh‖ ≤ (∑' e : ℕ, rHigh ^ e) - 1 := by
    calc
      ‖tailHigh‖ ≤ ∑' e : ℕ, ‖a (e + 1) * xHigh ^ (e + 1)‖ :=
        norm_tsum_le_tsum_norm htailNorm
      _ ≤ ∑' e : ℕ, rHigh ^ (e + 1) := by
        apply Summable.tsum_le_tsum
        · intro e
          rw [norm_mul, norm_pow]
          exact mul_le_of_le_one_left (pow_nonneg hrHigh0 _) (ha _)
        · exact htailNorm
        · exact hgeomHigh.comp_injective (fun _ _ h ↦ Nat.add_right_cancel h)
      _ = (∑' e : ℕ, rHigh ^ e) - 1 := by
        have hsplit := hgeomHigh.sum_add_tsum_nat_add 1
        have hsplit' : (∑' e : ℕ, rHigh ^ e) =
            1 + ∑' e : ℕ, rHigh ^ (e + 1) := by
          simpa using hsplit.symm
        linarith
  have hsplitHigh : (∑' e : ℕ, a e * xHigh ^ e) = 1 + tailHigh := by
    have hsplit := htermHigh.sum_add_tsum_nat_add 1
    rw [show (∑ e ∈ Finset.range 1, a e * xHigh ^ e) = 1 by simp [ha0]] at hsplit
    exact hsplit.symm
  have hhighLower :
      (1 : ℝ) - ((∑' e : ℕ, rHigh ^ e) - 1) ≤
        ‖∑' e : ℕ, a e * xHigh ^ e‖ := by
    rw [hsplitHigh]
    have htri : ‖(1 : ℂ)‖ ≤ ‖(1 : ℂ) + tailHigh‖ + ‖tailHigh‖ := by
      have h := norm_sub_le ((1 : ℂ) + tailHigh) tailHigh
      convert h using 1 <;> norm_num <;> ring
    norm_num at htri
    linarith
  have hdiffHigh :
      (∑' e : ℕ, rLow ^ e) - ∑' e : ℕ, rHigh ^ e ≤
        ‖∑' e : ℕ, a e * xHigh ^ e‖ := by
    calc
      (∑' e : ℕ, rLow ^ e) - ∑' e : ℕ, rHigh ^ e ≤
          2 - ∑' e : ℕ, rHigh ^ e := sub_le_sub_right hsumLowTwo _
      _ = 1 - ((∑' e : ℕ, rHigh ^ e) - 1) := by ring
      _ ≤ ‖∑' e : ℕ, a e * xHigh ^ e‖ := hhighLower
  have htriangle : ‖∑' e : ℕ, a e * xLow ^ e‖ ≤
      ‖∑' e : ℕ, a e * xHigh ^ e‖ +
        ‖(∑' e : ℕ, a e * xLow ^ e) -
          ∑' e : ℕ, a e * xHigh ^ e‖ := by
    simpa only [add_sub_cancel] using norm_add_le
      (∑' e : ℕ, a e * xHigh ^ e)
      ((∑' e : ℕ, a e * xLow ^ e) - ∑' e : ℕ, a e * xHigh ^ e)
  calc
    ‖∑' e : ℕ, a e * xLow ^ e‖ ≤
        ‖∑' e : ℕ, a e * xHigh ^ e‖ +
          ‖(∑' e : ℕ, a e * xLow ^ e) -
            ∑' e : ℕ, a e * xHigh ^ e‖ := htriangle
    _ ≤ ‖∑' e : ℕ, a e * xHigh ^ e‖ +
          ‖∑' e : ℕ, a e * xHigh ^ e‖ :=
      by nlinarith [hdiff.trans hdiffHigh]
    _ = 2 * ‖∑' e : ℕ, a e * xHigh ^ e‖ := by ring

/-- A loss which can be multiplied over primes.  Once the left Euler
variable has norm at most one third, moving it radially to the right costs
only the exponential of six times the radial displacement.  In contrast to
`norm_localEulerSeries_shift_le_two`, this estimate does not lose a fixed
factor at every prime. -/
theorem norm_localEulerSeries_shift_le_exp_norm_sub
    (a : ℕ → ℂ) (ha0 : a 0 = 1) (ha : ∀ e, ‖a e‖ ≤ 1)
    {xLow xHigh : ℂ} {c : ℝ}
    (hc : 1 ≤ c) (hfactor : xLow = (c : ℂ) * xHigh)
    (hthird : ‖xLow‖ ≤ (1 / 3 : ℝ)) :
    ‖∑' e : ℕ, a e * xLow ^ e‖ ≤
      ‖∑' e : ℕ, a e * xHigh ^ e‖ *
        Real.exp (6 * (‖xLow‖ - ‖xHigh‖)) := by
  let rLow : ℝ := ‖xLow‖
  let rHigh : ℝ := ‖xHigh‖
  have hrLow0 : 0 ≤ rLow := norm_nonneg _
  have hrHigh0 : 0 ≤ rHigh := norm_nonneg _
  have hrLow : rLow ≤ 1 / 3 := hthird
  have hrLow1 : rLow < 1 := lt_of_le_of_lt hrLow (by norm_num)
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have hrFactor : rLow = c * rHigh := by
    dsimp only [rLow, rHigh]
    rw [hfactor, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hc0]
  have hrHigh : rHigh ≤ rLow := by
    rw [hrFactor]
    exact le_mul_of_one_le_left hrHigh0 hc
  have hrHigh1 : rHigh < 1 := hrHigh.trans_lt hrLow1
  have hgeomLow : Summable (fun e : ℕ ↦ rLow ^ e) :=
    summable_geometric_of_norm_lt_one (by
      simpa [Real.norm_eq_abs, abs_of_nonneg hrLow0] using hrLow1)
  have hgeomHigh : Summable (fun e : ℕ ↦ rHigh ^ e) :=
    summable_geometric_of_norm_lt_one (by
      simpa [Real.norm_eq_abs, abs_of_nonneg hrHigh0] using hrHigh1)
  have hnormLow : Summable (fun e : ℕ ↦ ‖a e * xLow ^ e‖) := by
    apply hgeomLow.of_nonneg_of_le (fun e ↦ norm_nonneg _)
    intro e
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (pow_nonneg hrLow0 e) (ha e)
  have hnormHigh : Summable (fun e : ℕ ↦ ‖a e * xHigh ^ e‖) := by
    apply hgeomHigh.of_nonneg_of_le (fun e ↦ norm_nonneg _)
    intro e
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (pow_nonneg hrHigh0 e) (ha e)
  have htermLow : Summable (fun e : ℕ ↦ a e * xLow ^ e) := hnormLow.of_norm
  have htermHigh : Summable (fun e : ℕ ↦ a e * xHigh ^ e) := hnormHigh.of_norm
  have hpowerDiff (e : ℕ) :
      ‖xLow ^ e - xHigh ^ e‖ = rLow ^ e - rHigh ^ e := by
    rw [hfactor, mul_pow]
    nth_rewrite 2 [← one_mul (xHigh ^ e)]
    rw [← sub_mul, norm_mul,
      ← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    have hcpow : 1 ≤ c ^ e := one_le_pow₀ hc
    rw [abs_of_nonneg (sub_nonneg.mpr hcpow), norm_pow, hrFactor, mul_pow]
    ring
  have hdiffNorm : Summable (fun e : ℕ ↦
      ‖a e * xLow ^ e - a e * xHigh ^ e‖) := by
    apply (hgeomLow.add hgeomHigh).of_nonneg_of_le (fun e ↦ norm_nonneg _)
    intro e
    rw [← mul_sub, norm_mul, hpowerDiff e]
    have hpow : rHigh ^ e ≤ rLow ^ e :=
      pow_le_pow_left₀ hrHigh0 hrHigh e
    have hdiff0 : 0 ≤ rLow ^ e - rHigh ^ e := sub_nonneg.mpr hpow
    calc
      ‖a e‖ * (rLow ^ e - rHigh ^ e) ≤
          1 * (rLow ^ e - rHigh ^ e) :=
        mul_le_mul_of_nonneg_right (ha e) hdiff0
      _ ≤ rLow ^ e + rHigh ^ e := by nlinarith [pow_nonneg hrHigh0 e]
  have hdiff :
      ‖(∑' e : ℕ, a e * xLow ^ e) -
          ∑' e : ℕ, a e * xHigh ^ e‖ ≤
        (∑' e : ℕ, rLow ^ e) - ∑' e : ℕ, rHigh ^ e := by
    rw [← htermLow.tsum_sub htermHigh]
    calc
      ‖∑' e : ℕ, (a e * xLow ^ e - a e * xHigh ^ e)‖ ≤
          ∑' e : ℕ, ‖a e * xLow ^ e - a e * xHigh ^ e‖ :=
        norm_tsum_le_tsum_norm hdiffNorm
      _ ≤ ∑' e : ℕ, (rLow ^ e - rHigh ^ e) := by
        apply Summable.tsum_le_tsum
        · intro e
          rw [← mul_sub, norm_mul, hpowerDiff e]
          exact mul_le_of_le_one_left
            (sub_nonneg.mpr (pow_le_pow_left₀ hrHigh0 hrHigh e)) (ha e)
        · exact hdiffNorm
        · exact hgeomLow.sub hgeomHigh
      _ = (∑' e : ℕ, rLow ^ e) - ∑' e : ℕ, rHigh ^ e :=
        hgeomLow.tsum_sub hgeomHigh
  have hsumLow : (∑' e : ℕ, rLow ^ e) = (1 - rLow)⁻¹ :=
    tsum_geometric_of_lt_one hrLow0 hrLow1
  have hsumHigh : (∑' e : ℕ, rHigh ^ e) = (1 - rHigh)⁻¹ :=
    tsum_geometric_of_lt_one hrHigh0 hrHigh1
  have hdenLow : 2 / 3 ≤ 1 - rLow := by linarith
  have hdenHigh : 2 / 3 ≤ 1 - rHigh := by linarith
  have hdenLowPos : 0 < 1 - rLow := lt_of_lt_of_le (by norm_num) hdenLow
  have hdenHighPos : 0 < 1 - rHigh := lt_of_lt_of_le (by norm_num) hdenHigh
  have hgeomDiff :
      (∑' e : ℕ, rLow ^ e) - ∑' e : ℕ, rHigh ^ e ≤
        3 * (rLow - rHigh) := by
    rw [hsumLow, hsumHigh]
    rw [inv_sub_inv hdenLowPos.ne' hdenHighPos.ne']
    have hnum : 1 - rHigh - (1 - rLow) = rLow - rHigh := by ring
    rw [hnum]
    have hdenProd : 4 / 9 ≤ (1 - rLow) * (1 - rHigh) := by nlinarith
    have hdiff0 : 0 ≤ rLow - rHigh := sub_nonneg.mpr hrHigh
    rw [div_eq_mul_inv]
    have hinv : ((1 - rLow) * (1 - rHigh))⁻¹ ≤ 9 / 4 := by
      rw [inv_le_comm₀ (mul_pos hdenLowPos hdenHighPos) (by norm_num)]
      nlinarith
    calc
      (rLow - rHigh) * ((1 - rLow) * (1 - rHigh))⁻¹ ≤
          (rLow - rHigh) * (9 / 4) :=
        mul_le_mul_of_nonneg_left hinv hdiff0
      _ ≤ 3 * (rLow - rHigh) := by nlinarith
  let tailHigh : ℂ := ∑' e : ℕ, a (e + 1) * xHigh ^ (e + 1)
  have htailNorm : Summable (fun e : ℕ ↦
      ‖a (e + 1) * xHigh ^ (e + 1)‖) :=
    hnormHigh.comp_injective (fun _ _ h ↦ Nat.add_right_cancel h)
  have htail : ‖tailHigh‖ ≤ (∑' e : ℕ, rHigh ^ e) - 1 := by
    calc
      ‖tailHigh‖ ≤ ∑' e : ℕ, ‖a (e + 1) * xHigh ^ (e + 1)‖ :=
        norm_tsum_le_tsum_norm htailNorm
      _ ≤ ∑' e : ℕ, rHigh ^ (e + 1) := by
        apply Summable.tsum_le_tsum
        · intro e
          rw [norm_mul, norm_pow]
          exact mul_le_of_le_one_left (pow_nonneg hrHigh0 _) (ha _)
        · exact htailNorm
        · exact hgeomHigh.comp_injective (fun _ _ h ↦ Nat.add_right_cancel h)
      _ = (∑' e : ℕ, rHigh ^ e) - 1 := by
        have hsplit := hgeomHigh.sum_add_tsum_nat_add 1
        have hsplit' : (∑' e : ℕ, rHigh ^ e) =
            1 + ∑' e : ℕ, rHigh ^ (e + 1) := by
          simpa using hsplit.symm
        linarith
  have hsplitHigh : (∑' e : ℕ, a e * xHigh ^ e) = 1 + tailHigh := by
    have hsplit := htermHigh.sum_add_tsum_nat_add 1
    rw [show (∑ e ∈ Finset.range 1, a e * xHigh ^ e) = 1 by simp [ha0]] at hsplit
    exact hsplit.symm
  have hsumHighLe : (∑' e : ℕ, rHigh ^ e) ≤ 3 / 2 := by
    rw [hsumHigh, inv_le_comm₀ hdenHighPos (by norm_num)]
    norm_num
    exact hdenHigh
  have hhighLower : (1 / 2 : ℝ) ≤
      ‖∑' e : ℕ, a e * xHigh ^ e‖ := by
    rw [hsplitHigh]
    have htri : ‖(1 : ℂ)‖ ≤ ‖(1 : ℂ) + tailHigh‖ + ‖tailHigh‖ := by
      have h := norm_sub_le ((1 : ℂ) + tailHigh) tailHigh
      convert h using 1 <;> norm_num <;> ring
    norm_num at htri
    linarith
  have htriangle : ‖∑' e : ℕ, a e * xLow ^ e‖ ≤
      ‖∑' e : ℕ, a e * xHigh ^ e‖ +
        ‖(∑' e : ℕ, a e * xLow ^ e) -
          ∑' e : ℕ, a e * xHigh ^ e‖ := by
    simpa only [add_sub_cancel] using norm_add_le
      (∑' e : ℕ, a e * xHigh ^ e)
      ((∑' e : ℕ, a e * xLow ^ e) - ∑' e : ℕ, a e * xHigh ^ e)
  have hdelta0 : 0 ≤ rLow - rHigh := sub_nonneg.mpr hrHigh
  have hexp : 1 + 6 * (rLow - rHigh) ≤
      Real.exp (6 * (rLow - rHigh)) := by
    simpa [add_comm] using Real.add_one_le_exp (6 * (rLow - rHigh))
  calc
    ‖∑' e : ℕ, a e * xLow ^ e‖ ≤
        ‖∑' e : ℕ, a e * xHigh ^ e‖ +
          ‖(∑' e : ℕ, a e * xLow ^ e) -
            ∑' e : ℕ, a e * xHigh ^ e‖ := htriangle
    _ ≤ ‖∑' e : ℕ, a e * xHigh ^ e‖ +
          3 * (rLow - rHigh) := by
      gcongr
      exact hdiff.trans hgeomDiff
    _ ≤ ‖∑' e : ℕ, a e * xHigh ^ e‖ *
          (1 + 6 * (rLow - rHigh)) := by
      nlinarith [norm_nonneg (∑' e : ℕ, a e * xHigh ^ e)]
    _ ≤ ‖∑' e : ℕ, a e * xHigh ^ e‖ *
          Real.exp (6 * (rLow - rHigh)) := by
      gcongr

/-- Multiplicative form of the preceding local estimate.  It compares two
finite Euler products without a loss depending on the number of primes. -/
theorem norm_prod_gsA9LocalEulerFactor_shift_le_exp_sum_norm_sub
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    {sLow sHigh : ℂ} (c : ℕ → ℝ)
    (hc : ∀ p ∈ S, 1 ≤ c p)
    (hfactor : ∀ p ∈ S,
      (p : ℂ) ^ (-sLow) = (c p : ℂ) * (p : ℂ) ^ (-sHigh))
    (hthird : ∀ p ∈ S, ‖(p : ℂ) ^ (-sLow)‖ ≤ (1 / 3 : ℝ)) :
    ‖∏ p ∈ S, gsA9LocalEulerFactor f sLow p‖ ≤
      ‖∏ p ∈ S, gsA9LocalEulerFactor f sHigh p‖ *
        Real.exp (6 * ∑ p ∈ S,
          (‖(p : ℂ) ^ (-sLow)‖ - ‖(p : ℂ) ^ (-sHigh)‖)) := by
  rw [norm_prod, norm_prod]
  calc
    (∏ p ∈ S, ‖gsA9LocalEulerFactor f sLow p‖) ≤
        ∏ p ∈ S,
          (‖gsA9LocalEulerFactor f sHigh p‖ *
            Real.exp (6 *
              (‖(p : ℂ) ^ (-sLow)‖ - ‖(p : ℂ) ^ (-sHigh)‖))) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact norm_nonneg _
      · intro p hp
        unfold gsA9LocalEulerFactor
        exact norm_localEulerSeries_shift_le_exp_norm_sub
          (fun e ↦ f (p ^ e)) (by simpa using hmul.1)
          (fun e ↦ hbound _ (pow_pos (hprime p hp).pos e))
          (hc p hp) (hfactor p hp) (hthird p hp)
    _ = (∏ p ∈ S, ‖gsA9LocalEulerFactor f sHigh p‖) *
        (∏ p ∈ S,
          Real.exp (6 *
            (‖(p : ℂ) ^ (-sLow)‖ - ‖(p : ℂ) ^ (-sHigh)‖))) := by
      rw [Finset.prod_mul_distrib]
    _ = (∏ p ∈ S, ‖gsA9LocalEulerFactor f sHigh p‖) *
        Real.exp (∑ p ∈ S,
          6 * (‖(p : ℂ) ^ (-sLow)‖ - ‖(p : ℂ) ^ (-sHigh)‖)) := by
      rw [Real.exp_sum]
    _ = (∏ p ∈ S, ‖gsA9LocalEulerFactor f sHigh p‖) *
        Real.exp (6 * ∑ p ∈ S,
          (‖(p : ℂ) ^ (-sLow)‖ - ‖(p : ℂ) ^ (-sHigh)‖)) := by
      rw [Finset.mul_sum]

/-- Absolute geometric majorant for an arbitrary one-bounded local
prime-power series. -/
theorem norm_localEulerSeries_le_inv_one_sub
    (a : ℕ → ℂ) (ha : ∀ e, ‖a e‖ ≤ 1)
    {x : ℂ} (hx : ‖x‖ < 1) :
    ‖∑' e : ℕ, a e * x ^ e‖ ≤ (1 - ‖x‖)⁻¹ := by
  let r : ℝ := ‖x‖
  have hr0 : 0 ≤ r := norm_nonneg x
  have hgeom : Summable (fun e : ℕ ↦ r ^ e) :=
    summable_geometric_of_norm_lt_one (by
      simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hx)
  have hnorm : Summable (fun e : ℕ ↦ ‖a e * x ^ e‖) := by
    apply hgeom.of_nonneg_of_le (fun e ↦ norm_nonneg _)
    intro e
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (pow_nonneg hr0 e) (ha e)
  calc
    ‖∑' e : ℕ, a e * x ^ e‖ ≤ ∑' e : ℕ, ‖a e * x ^ e‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' e : ℕ, r ^ e := by
      apply Summable.tsum_le_tsum
      · intro e
        rw [norm_mul, norm_pow]
        exact mul_le_of_le_one_left (pow_nonneg hr0 e) (ha e)
      · exact hnorm
      · exact hgeom
    _ = (1 - ‖x‖)⁻¹ := tsum_geometric_of_lt_one hr0 hx

/-- Finite-product Euler majorant under a direct half-norm hypothesis. -/
theorem norm_prod_gsA9LocalEulerFactor_le_exp_linear_add_square_of_norm_le_half
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    {s : ℂ} (hsmall : ∀ p ∈ S,
      ‖(p : ℂ) ^ (-s)‖ ≤ (1 / 2 : ℝ)) :
    ‖∏ p ∈ S, gsA9LocalEulerFactor f s p‖ ≤
      Real.exp
        ((∑ p ∈ S, (f p * (p : ℂ) ^ (-s)).re) +
          3 * ∑ p ∈ S, ‖(p : ℂ) ^ (-s)‖ ^ 2) := by
  rw [norm_prod]
  calc
    (∏ p ∈ S, ‖gsA9LocalEulerFactor f s p‖) ≤
        ∏ p ∈ S, Real.exp
          ((f p * (p : ℂ) ^ (-s)).re +
            3 * ‖(p : ℂ) ^ (-s)‖ ^ 2) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact norm_nonneg _
      · intro p hp
        unfold gsA9LocalEulerFactor
        simpa only [pow_one] using
          Erdos67b.MRMultiplicativeEuler.norm_localEulerFactor_le_exp
            (fun e ↦ f (p ^ e)) (by simpa using hmul.1)
            (fun e ↦ hbound (p ^ e) (pow_pos (hprime p hp).pos e))
            ((p : ℂ) ^ (-s)) (hsmall p hp)
    _ = Real.exp (∑ p ∈ S,
          ((f p * (p : ℂ) ^ (-s)).re +
            3 * ‖(p : ℂ) ^ (-s)‖ ^ 2)) := by
      rw [Real.exp_sum]
    _ = Real.exp
        ((∑ p ∈ S, (f p * (p : ℂ) ^ (-s)).re) +
          3 * ∑ p ∈ S, ‖(p : ℂ) ^ (-s)‖ ^ 2) := by
      congr 1
      rw [Finset.sum_add_distrib, Finset.mul_sum]

end

end Erdos67b.MRHalaszBands
