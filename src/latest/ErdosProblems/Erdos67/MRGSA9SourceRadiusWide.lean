import ErdosProblems.Erdos67.MRGSA9SourceRadius

/-!
# The widened source line for the beta-dependent A.10 contour

Choosing the Perron parameter `c beta = taoExponent X - beta` keeps the
high factor on the Halasz line.  Its low factor can then lie as far left as
`1 - 3 / log y`.  This file records the corresponding elementary prime
monomial, horizontal-displacement, and quadratic-mass estimates.  The
constants are still absolute: `exp 3` replaces `exp 2`, and `exp 6`
replaces `exp 4`.
-/

open scoped BigOperators

namespace Erdos67.MRHalaszBands

noncomputable section

open BoundedGaps.Maynard

/-- The absolute displacement budget for the widened source line. -/
def gsA9WideSourceShiftConstant : ℝ :=
  3 * Real.exp 3 *
    (1 + primeLogMertensConstant / Real.log 2)

/-- At distance at most `3 / log y` left of one, every prime monomial
through `y` is bounded by `e^3 / p`. -/
theorem norm_prime_cpow_wideSourceLow_le_exp_three_div
    {p y : ℕ} (hp : p.Prime) (hpy : p ≤ y) {sigmaLow t : ℝ}
    (hsigma : 1 - 3 / Real.log (y : ℝ) ≤ sigmaLow) :
    ‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ ≤
      Real.exp 3 / (p : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hyOne : (1 : ℝ) < y := by
    exact_mod_cast hp.one_lt.trans_le hpy
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos hyOne
  have hlogp : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hlogle : Real.log (p : ℝ) ≤ Real.log (y : ℝ) := by
    exact Real.log_le_log hpR (by exact_mod_cast hpy)
  have hratio : Real.log (p : ℝ) / Real.log (y : ℝ) ≤ 1 :=
    (div_le_one hlogy).mpr hlogle
  have hthree : 3 / Real.log (y : ℝ) * Real.log (p : ℝ) ≤ 3 := by
    calc
      3 / Real.log (y : ℝ) * Real.log (p : ℝ) =
          3 * (Real.log (p : ℝ) / Real.log (y : ℝ)) := by ring
      _ ≤ 3 * 1 := by gcongr
      _ = 3 := by ring
  have hexponent : Real.log (p : ℝ) * -sigmaLow ≤
      3 - Real.log (p : ℝ) := by
    have haux : Real.log (p : ℝ) - 3 ≤
        (1 - 3 / Real.log (y : ℝ)) * Real.log (p : ℝ) := by
      rw [sub_mul, one_mul]
      linarith
    nlinarith [mul_le_mul_of_nonneg_right hsigma hlogp]
  rw [Erdos67.HalaszCpowDeficit.norm_nat_cpow_neg_sigma_add_I_mul hp.pos,
    Real.rpow_def_of_pos hpR]
  calc
    Real.exp (Real.log (p : ℝ) * -sigmaLow) ≤
        Real.exp (3 - Real.log (p : ℝ)) := Real.exp_le_exp.mpr hexponent
    _ = Real.exp 3 / (p : ℝ) := by
      rw [Real.exp_sub, Real.exp_log hpR]

/-- The complete radial displacement on the widened source line. -/
theorem sum_prime_radial_norm_sub_wideSourceLow_le
    {y : ℕ} {sigmaLow sigmaHigh t : ℝ}
    (hle : sigmaLow ≤ sigmaHigh)
    (hsigma : 1 - 3 / Real.log (y : ℝ) ≤ sigmaLow) :
    (∑ p ∈ primesUpTo y,
      (‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ -
        ‖(p : ℂ) ^ (-((sigmaHigh : ℂ) + Complex.I * (t : ℂ)))‖)) ≤
      Real.exp 3 * (sigmaHigh - sigmaLow) * primeLogHarmonicSum y := by
  apply sum_prime_radial_norm_sub_le_mul_primeLogHarmonicSum hle
  intro p hp
  exact norm_prime_cpow_wideSourceLow_le_exp_three_div
    (mem_primesUpTo.mp hp).1 (mem_primesUpTo.mp hp).2 hsigma

/-- A gap of at most `3 / log y` still has an absolute total radial cost
on the widened line. -/
theorem sum_prime_radial_norm_sub_wideSourceGap_le_constant
    {y : ℕ} (hy : 2 ≤ y) {sigmaLow sigmaHigh t : ℝ}
    (hle : sigmaLow ≤ sigmaHigh)
    (hsigma : 1 - 3 / Real.log (y : ℝ) ≤ sigmaLow)
    (hgap : sigmaHigh - sigmaLow ≤ 3 / Real.log (y : ℝ)) :
    (∑ p ∈ primesUpTo y,
      (‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ -
        ‖(p : ℂ) ^ (-((sigmaHigh : ℂ) + Complex.I * (t : ℂ)))‖)) ≤
      gsA9WideSourceShiftConstant := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hyR : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) hyR)
  have hlogle : Real.log 2 ≤ Real.log (y : ℝ) :=
    Real.log_le_log (by norm_num) hyR
  have hPH0 : 0 ≤ primeLogHarmonicSum y := by
    unfold primeLogHarmonicSum
    apply Finset.sum_nonneg
    intro p hp
    have hpPrime : p.Prime := by
      have hp' : p ≤ y ∧ p.Prime := by
        simpa [Nat.primesLE_eq_filter_range] using hp
      exact hp'.2
    exact div_nonneg
      (Real.log_nonneg (by exact_mod_cast hpPrime.one_le)) (by positivity)
  have hPH : primeLogHarmonicSum y ≤
      Real.log (y : ℝ) + primeLogMertensConstant := by
    have hs := primeLogMertensConstant_spec y
    linarith [le_abs_self (primeLogHarmonicSum y - Real.log y)]
  have hCdiv : primeLogMertensConstant / Real.log (y : ℝ) ≤
      primeLogMertensConstant / Real.log 2 := by
    exact div_le_div_of_nonneg_left primeLogMertensConstant_nonneg
      hlogTwo hlogle
  calc
    (∑ p ∈ primesUpTo y,
      (‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ -
        ‖(p : ℂ) ^ (-((sigmaHigh : ℂ) + Complex.I * (t : ℂ)))‖)) ≤
        Real.exp 3 * (sigmaHigh - sigmaLow) * primeLogHarmonicSum y :=
      sum_prime_radial_norm_sub_wideSourceLow_le hle hsigma
    _ ≤ Real.exp 3 * (3 / Real.log (y : ℝ)) *
        (Real.log (y : ℝ) + primeLogMertensConstant) := by
      gcongr
    _ = 3 * Real.exp 3 *
        (1 + primeLogMertensConstant / Real.log (y : ℝ)) := by
      field_simp
    _ ≤ 3 * Real.exp 3 *
        (1 + primeLogMertensConstant / Real.log 2) := by
      gcongr
    _ = gsA9WideSourceShiftConstant := rfl

/-- Every subblock inherits the widened displacement budget. -/
theorem sum_prime_radial_norm_sub_subset_wideSourceGap_le_constant
    {y : ℕ} (hy : 2 ≤ y) (S : Finset ℕ)
    (hS : S ⊆ primesUpTo y)
    {sigmaLow sigmaHigh t : ℝ}
    (hle : sigmaLow ≤ sigmaHigh)
    (hsigma : 1 - 3 / Real.log (y : ℝ) ≤ sigmaLow)
    (hgap : sigmaHigh - sigmaLow ≤ 3 / Real.log (y : ℝ)) :
    (∑ p ∈ S,
      (‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ -
        ‖(p : ℂ) ^ (-((sigmaHigh : ℂ) + Complex.I * (t : ℂ)))‖)) ≤
      gsA9WideSourceShiftConstant := by
  have hsub :
      (∑ p ∈ S,
        (‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ -
          ‖(p : ℂ) ^ (-((sigmaHigh : ℂ) + Complex.I * (t : ℂ)))‖)) ≤
        ∑ p ∈ primesUpTo y,
        (‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ -
          ‖(p : ℂ) ^ (-((sigmaHigh : ℂ) + Complex.I * (t : ℂ)))‖) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hS
    intro p hp _
    exact sub_nonneg.mpr
      (norm_prime_cpow_antitone_real (mem_primesUpTo.mp hp).1 hle)
  exact hsub.trans
    (sum_prime_radial_norm_sub_wideSourceGap_le_constant
      hy hle hsigma hgap)

/-- The quadratic Euler mass on the widened line is absolutely bounded. -/
theorem two_mul_sum_norm_prime_cpow_sq_wideSourceLow_le
    {y : ℕ} (S : Finset ℕ) (hS : S ⊆ primesUpTo y)
    {sigmaLow t : ℝ}
    (hsigma : 1 - 3 / Real.log (y : ℝ) ≤ sigmaLow) :
    2 * (∑ p ∈ S,
      ‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ ^ 2) ≤
      Real.exp 6 * Erdos67.EulerQuantitative.primeQuadraticConstant := by
  let e : {p // p ∈ S} → Nat.Primes := fun p ↦
    ⟨p, (mem_primesUpTo.mp (hS p.property)).1⟩
  have heinj : Function.Injective e := by
    intro p q hpq
    apply Subtype.ext
    exact congrArg (fun z : Nat.Primes ↦ (z : ℕ)) hpq
  let T : Finset Nat.Primes := Finset.univ.map ⟨e, heinj⟩
  let G : Nat.Primes → ℝ := fun p ↦ (p.1 : ℝ) ^ (-2 : ℝ)
  have hGs : Summable G :=
    (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).subtype
      Nat.Prime
  have hpoint (p : ℕ) (hp : p ∈ S) :
      ‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ ^ 2 ≤
        Real.exp 6 * (p : ℝ) ^ (-2 : ℝ) := by
    have hpPrime := (mem_primesUpTo.mp (hS hp)).1
    have hnorm := norm_prime_cpow_wideSourceLow_le_exp_three_div
      hpPrime (mem_primesUpTo.mp (hS hp)).2 hsigma (t := t)
    have hnorm0 : 0 ≤
        ‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ := norm_nonneg _
    have hdiv0 : 0 ≤ Real.exp 3 / (p : ℝ) := by positivity
    have hsq := (sq_le_sq₀ hnorm0 hdiv0).2 hnorm
    calc
      ‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ ^ 2 ≤
          (Real.exp 3 / (p : ℝ)) ^ 2 := hsq
      _ = Real.exp 6 * (p : ℝ) ^ (-2 : ℝ) := by
        rw [div_pow, ← Real.exp_nat_mul]
        have hp0 : (0 : ℝ) ≤ p := by positivity
        rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
          Real.rpow_neg hp0]
        norm_num [div_eq_mul_inv]
  have hsumEq :
      (∑ p ∈ S, Real.exp 6 * (p : ℝ) ^ (-2 : ℝ)) =
        ∑ p ∈ T, Real.exp 6 * G p := by
    rw [Finset.sum_subtype S (fun _ ↦ Iff.rfl), Finset.sum_map]
    rfl
  have hfinite :
      (∑ p ∈ S,
        ‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ ^ 2) ≤
        Real.exp 6 * ∑' p : Nat.Primes, G p := by
    calc
      _ ≤ ∑ p ∈ S, Real.exp 6 * (p : ℝ) ^ (-2 : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        exact hpoint p hp
      _ = ∑ p ∈ T, Real.exp 6 * G p := hsumEq
      _ ≤ ∑' p : Nat.Primes, Real.exp 6 * G p := by
        exact (hGs.mul_left (Real.exp 6)).sum_le_tsum T
          (fun p _ ↦ mul_nonneg (Real.exp_pos _).le
            (Real.rpow_nonneg (by positivity) _))
      _ = Real.exp 6 * ∑' p : Nat.Primes, G p := by
        rw [hGs.tsum_mul_left]
  have hconst : 2 * ∑' p : Nat.Primes, G p =
      Erdos67.EulerQuantitative.primeQuadraticConstant := by
    unfold Erdos67.EulerQuantitative.primeQuadraticConstant
    rw [hGs.tsum_mul_left]
  calc
    2 * (∑ p ∈ S,
      ‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ ^ 2) ≤
        2 * (Real.exp 6 * ∑' p : Nat.Primes, G p) := by gcongr
    _ = Real.exp 6 * Erdos67.EulerQuantitative.primeQuadraticConstant := by
      rw [← hconst]
      ring

end

end Erdos67.MRHalaszBands

#print axioms Erdos67.MRHalaszBands.norm_prime_cpow_wideSourceLow_le_exp_three_div
#print axioms Erdos67.MRHalaszBands.sum_prime_radial_norm_sub_wideSourceGap_le_constant
#print axioms Erdos67.MRHalaszBands.two_mul_sum_norm_prime_cpow_sq_wideSourceLow_le
