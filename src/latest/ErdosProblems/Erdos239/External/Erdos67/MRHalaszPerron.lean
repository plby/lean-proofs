import ErdosProblems.Erdos239.External.Erdos67.MRHalaszEuler
import BoundedGaps.BombieriVinogradov.Analytic.DirichletPerronSeries

/-!
# A truncated Perron bridge for dyadic means

This file records the part of the Halász argument which passes from a
uniform bound for an absolutely convergent `LSeries` on a finite vertical
line to a bound for a dyadic coefficient sum.  The truncation errors are the
explicit errors from the BoundedGaps Dirichlet--Perron theorem; in particular,
no mean-value estimate is hidden in an interface proposition.

The result is a global dyadic-mean estimate.  It is useful in the major-arc
analysis, but is strictly weaker than the short-interval second-moment
statement `MRComplexNonpretentiousMeanSquareInput`.
-/

open scoped BigOperators
open Complex Finset

namespace Erdos67.MRHalaszPerron

noncomputable section

open BoundedGaps.Maynard

/-- The explicit truncation error in the countable Dirichlet--Perron theorem. -/
def perronTruncationError (a : ℕ → ℂ) (x : ℕ) (sigma T : ℝ) : ℝ :=
  dirichletPerronNearMass a x T +
    (32 * (x : ℝ) ^ sigma / T) *
      dirichletPerronCoefficientMass a sigma

/-- The vertical-integral majorant obtained from a uniform bound `M` for the
`LSeries` on `|t| ≤ T`. -/
def perronVerticalMajorant (M y sigma T : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ((M * y ^ sigma / sigma) * (2 * T))

/-- Pointwise control of the Perron integrand on a vertical line. -/
theorem norm_perronLineIntegrand_le
    {a : ℕ → ℂ} {y sigma T M t : ℝ}
    (hy : 0 < y) (hsigma : 0 < sigma) (hM : 0 ≤ M)
    (hL : ∀ u : ℝ, |u| ≤ T →
      ‖LSeries a ((sigma : ℂ) + u * I)‖ ≤ M)
    (ht : |t| ≤ T) :
    ‖LSeries a ((sigma : ℂ) + t * I) *
        (y : ℂ) ^ ((sigma : ℂ) + t * I) /
          ((sigma : ℂ) + t * I)‖ ≤
      M * y ^ sigma / sigma := by
  let s : ℂ := (sigma : ℂ) + t * I
  have hsRe : s.re = sigma := by simp [s]
  have hsNorm : sigma ≤ ‖s‖ := by
    have h := Complex.abs_re_le_norm s
    simpa [hsRe, abs_of_pos hsigma] using h
  have hsNormPos : 0 < ‖s‖ := hsigma.trans_le hsNorm
  have hyNorm : ‖(y : ℂ) ^ s‖ = y ^ sigma := by
    simpa [hsRe] using Complex.norm_cpow_eq_rpow_re_of_pos hy s
  have hyPowNonneg : 0 ≤ y ^ sigma := Real.rpow_nonneg hy.le _
  have hLMul :
      ‖LSeries a s‖ * y ^ sigma ≤ M * y ^ sigma :=
    mul_le_mul_of_nonneg_right (hL t ht) hyPowNonneg
  change ‖LSeries a s * (y : ℂ) ^ s / s‖ ≤ _
  rw [norm_div, norm_mul, hyNorm]
  calc
    ‖LSeries a s‖ * y ^ sigma / ‖s‖ ≤
        M * y ^ sigma / ‖s‖ :=
      div_le_div_of_nonneg_right hLMul hsNormPos.le
    _ ≤ M * y ^ sigma / sigma :=
      div_le_div_of_nonneg_left
        (mul_nonneg hM hyPowNonneg) hsigma hsNorm

/-- A uniform `LSeries` bound on a finite vertical line bounds the normalized
Perron integral, with all constants explicit. -/
theorem norm_dirichletPerronIntegral_le_of_uniform
    {a : ℕ → ℂ} {y sigma T M : ℝ}
    (hy : 0 < y) (hsigma : 0 < sigma) (hT : 0 ≤ T)
    (hM : 0 ≤ M)
    (hL : ∀ t : ℝ, |t| ≤ T →
      ‖LSeries a ((sigma : ℂ) + t * I)‖ ≤ M) :
    ‖dirichletPerronIntegral a y sigma T‖ ≤
      perronVerticalMajorant M y sigma T := by
  have hline :
      ‖∫ t in -T..T,
          LSeries a ((sigma : ℂ) + t * I) *
            (y : ℂ) ^ ((sigma : ℂ) + t * I) /
              ((sigma : ℂ) + t * I)‖ ≤
        (M * y ^ sigma / sigma) * (2 * T) := by
    have hraw := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun t : ℝ =>
        LSeries a ((sigma : ℂ) + t * I) *
          (y : ℂ) ^ ((sigma : ℂ) + t * I) /
            ((sigma : ℂ) + t * I))
      (C := M * y ^ sigma / sigma) (a := -T) (b := T) (fun t ht => by
        rw [Set.uIoc_of_le (by linarith)] at ht
        apply norm_perronLineIntegrand_le hy hsigma hM hL
        exact abs_le.mpr ⟨ht.1.le, ht.2⟩)
    simpa [abs_of_nonneg (add_nonneg hT hT), two_mul] using hraw
  unfold dirichletPerronIntegral perronVerticalMajorant
  rw [norm_mul]
  have hscalar :
      ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ = (2 * Real.pi)⁻¹ := by
    have hpi : 0 ≤ 2 * Real.pi := by positivity
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hpi]
  rw [hscalar]
  exact mul_le_mul_of_nonneg_left hline (inv_nonneg.mpr (by positivity))

/-- The Perron starred sum is bounded by its explicit truncation error and
the vertical-line majorant. -/
theorem norm_dirichletPerronStarredSum_le_of_uniform
    {a : ℕ → ℂ} {x : ℕ} {sigma T M : ℝ}
    (hsum : LSeriesSummable a (sigma : ℂ))
    (hx : 0 < x) (hsigma : 0 < sigma) (hsigmaUpper : sigma ≤ 2)
    (hT : 0 < T) (hM : 0 ≤ M)
    (hL : ∀ t : ℝ, |t| ≤ T →
      ‖LSeries a ((sigma : ℂ) + t * I)‖ ≤ M) :
    ‖dirichletPerronStarredSum a x‖ ≤
      perronTruncationError a x sigma T +
        perronVerticalMajorant M x sigma T := by
  have hperron := norm_dirichletPerronStarredSum_sub_integral_le
    hsum hx hsigma hsigmaUpper hT
  have hintegral := norm_dirichletPerronIntegral_le_of_uniform
    (a := a) (y := (x : ℝ)) (sigma := sigma) (T := T) (M := M)
    (by exact_mod_cast hx) hsigma hT.le hM hL
  have htriangle := norm_le_norm_add_norm_sub
    (dirichletPerronIntegral a x sigma T)
    (dirichletPerronStarredSum a x)
  rw [norm_sub_rev] at htriangle
  calc
    ‖dirichletPerronStarredSum a x‖ ≤
        ‖dirichletPerronIntegral a x sigma T‖ +
          ‖dirichletPerronStarredSum a x -
            dirichletPerronIntegral a x sigma T‖ := htriangle
    _ ≤ perronVerticalMajorant M x sigma T +
          perronTruncationError a x sigma T :=
      add_le_add hintegral (by simpa [perronTruncationError] using hperron)
    _ = perronTruncationError a x sigma T +
          perronVerticalMajorant M x sigma T := add_comm _ _

/-- Exact endpoint bookkeeping: the usual dyadic interval is the difference
of two Perron starred sums plus the two half-endpoint corrections. -/
theorem sum_Ioc_eq_starred_sub_starred_add_endpoints
    (a : ℕ → ℂ) {X : ℕ} (hX : 0 < X) :
    (∑ n ∈ Finset.Ioc X (2 * X), a n) =
      dirichletPerronStarredSum a (2 * X) -
        dirichletPerronStarredSum a X +
          (1 / 2 : ℂ) * (a (2 * X) - a X) := by
  have hIoc :
      (∑ n ∈ Finset.Ioc X (2 * X), a n) =
        (∑ n ∈ Finset.range (2 * X), a n) -
          (∑ n ∈ Finset.range X, a n) - a X + a (2 * X) := by
    rw [← Finset.Ico_add_one_add_one_eq_Ioc]
    rw [Finset.sum_Ico_eq_sub a (by omega), Finset.sum_range_succ,
      Finset.sum_range_succ]
    ring
  rw [hIoc]
  unfold dirichletPerronStarredSum
  rw [Finset.sum_Ico_eq_sub a (by omega),
    Finset.sum_Ico_eq_sub a (by omega)]
  simp only [Finset.sum_range_one]
  ring

/-- A uniform vertical-line bound gives a genuine dyadic coefficient-sum
bound.  Only the explicit Perron truncation errors and endpoint coefficients
remain on the right. -/
theorem norm_sum_Ioc_le_of_uniform_vertical_LSeries
    {a : ℕ → ℂ} {X : ℕ} {sigma T M : ℝ}
    (hsum : LSeriesSummable a (sigma : ℂ))
    (hX : 0 < X) (hsigma : 0 < sigma) (hsigmaUpper : sigma ≤ 2)
    (hT : 0 < T) (hM : 0 ≤ M)
    (hL : ∀ t : ℝ, |t| ≤ T →
      ‖LSeries a ((sigma : ℂ) + t * I)‖ ≤ M) :
    ‖∑ n ∈ Finset.Ioc X (2 * X), a n‖ ≤
      perronTruncationError a (2 * X) sigma T +
        perronVerticalMajorant M (2 * X) sigma T +
      (perronTruncationError a X sigma T +
        perronVerticalMajorant M X sigma T) +
      (1 / 2 : ℝ) * (‖a (2 * X)‖ + ‖a X‖) := by
  have h2X : 0 < 2 * X := by omega
  have hupper := norm_dirichletPerronStarredSum_le_of_uniform
    hsum h2X hsigma hsigmaUpper hT hM hL
  have hupper' :
      ‖dirichletPerronStarredSum a (2 * X)‖ ≤
        perronTruncationError a (2 * X) sigma T +
          perronVerticalMajorant M (2 * (X : ℝ)) sigma T := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hupper
  have hlower := norm_dirichletPerronStarredSum_le_of_uniform
    hsum hX hsigma hsigmaUpper hT hM hL
  rw [sum_Ioc_eq_starred_sub_starred_add_endpoints a hX]
  calc
    ‖dirichletPerronStarredSum a (2 * X) -
        dirichletPerronStarredSum a X +
          (1 / 2 : ℂ) * (a (2 * X) - a X)‖ ≤
      ‖dirichletPerronStarredSum a (2 * X)‖ +
        ‖dirichletPerronStarredSum a X‖ +
          (1 / 2 : ℝ) * (‖a (2 * X)‖ + ‖a X‖) := by
      calc
        _ ≤ ‖dirichletPerronStarredSum a (2 * X) -
              dirichletPerronStarredSum a X‖ +
              ‖(1 / 2 : ℂ) * (a (2 * X) - a X)‖ := norm_add_le _ _
        _ ≤ (‖dirichletPerronStarredSum a (2 * X)‖ +
              ‖dirichletPerronStarredSum a X‖) +
              (1 / 2 : ℝ) * (‖a (2 * X)‖ + ‖a X‖) := by
          gcongr
          · exact norm_sub_le _ _
          · rw [norm_mul]
            have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
            rw [hhalf]
            exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
        _ = _ := by ring
    _ ≤ perronTruncationError a (2 * X) sigma T +
          perronVerticalMajorant M (2 * X) sigma T +
        (perronTruncationError a X sigma T +
          perronVerticalMajorant M X sigma T) +
        (1 / 2 : ℝ) * (‖a (2 * X)‖ + ‖a X‖) := by
      exact add_le_add (add_le_add hupper' hlower) le_rfl

/-- Unit-norm coefficients reduce the absolute coefficient mass in the
Perron error exactly to the scalar coefficient-one mass. -/
theorem perronCoefficientMass_eq_one_of_unitNorm
    {a : ℕ → ℂ} (ha : ∀ n ≠ 0, ‖a n‖ = 1) (sigma : ℝ) :
    dirichletPerronCoefficientMass a sigma =
      dirichletPerronCoefficientMass (fun _ ↦ (1 : ℂ)) sigma := by
  unfold dirichletPerronCoefficientMass
  apply tsum_congr
  intro n
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, if_false, ha n hn, norm_one]

/-- Unit-norm coefficients likewise reduce the near-diagonal Perron mass
exactly to the scalar kernel mass. -/
theorem perronNearMass_eq_scalar_of_unitNorm
    {a : ℕ → ℂ} (ha : ∀ n ≠ 0, ‖a n‖ = 1) (x : ℕ) (T : ℝ) :
    dirichletPerronNearMass a x T =
      ∑' n : ℕ, dirichletPerronNearError x T n := by
  unfold dirichletPerronNearMass
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  · rw [ha n hn, one_mul]

/-- A one-bounded coefficient sequence has an absolutely convergent
`LSeries` on every line `sigma > 1`, and its two endpoint corrections cost at
most one.  This form also covers Dirichlet twists which may vanish at primes
dividing the conductor. -/
theorem norm_sum_Ioc_le_of_oneBounded_uniform_vertical_LSeries
    {a : ℕ → ℂ} (ha : ∀ n ≠ 0, ‖a n‖ ≤ 1)
    {X : ℕ} {sigma T M : ℝ}
    (hX : 0 < X) (hsigma : 1 < sigma) (hsigmaUpper : sigma ≤ 2)
    (hT : 0 < T) (hM : 0 ≤ M)
    (hL : ∀ t : ℝ, |t| ≤ T →
      ‖LSeries a ((sigma : ℂ) + t * I)‖ ≤ M) :
    ‖∑ n ∈ Finset.Ioc X (2 * X), a n‖ ≤
      perronTruncationError a (2 * X) sigma T +
        perronVerticalMajorant M (2 * X) sigma T +
      (perronTruncationError a X sigma T +
        perronVerticalMajorant M X sigma T) + 1 := by
  have hsum : LSeriesSummable a (sigma : ℂ) := by
    apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) ha
    simpa using hsigma
  have hbound := norm_sum_Ioc_le_of_uniform_vertical_LSeries
    hsum hX (lt_trans zero_lt_one hsigma) hsigmaUpper hT hM hL
  let R : ℝ :=
    perronTruncationError a (2 * X) sigma T +
        perronVerticalMajorant M (2 * X) sigma T +
      (perronTruncationError a X sigma T +
        perronVerticalMajorant M X sigma T)
  have h2X : 2 * X ≠ 0 := by omega
  have hend : (1 / 2 : ℝ) * (‖a (2 * X)‖ + ‖a X‖) ≤ 1 := by
    have htwo := add_le_add (ha (2 * X) h2X) (ha X hX.ne')
    nlinarith
  change ‖∑ n ∈ Finset.Ioc X (2 * X), a n‖ ≤ R + 1
  change ‖∑ n ∈ Finset.Ioc X (2 * X), a n‖ ≤
    R + (1 / 2 : ℝ) * (‖a (2 * X)‖ + ‖a X‖) at hbound
  apply hbound.trans
  gcongr

/-- For a unit-circle-valued completely multiplicative coefficient, absolute
convergence on `sigma > 1` and both endpoint corrections are automatic. -/
theorem norm_sum_Ioc_le_of_unitNorm_uniform_vertical_LSeries
    {h : ℕ →*₀ ℂ} (hh : Erdos67.EulerResidue.HasUnitNorm h)
    {X : ℕ} {sigma T M : ℝ}
    (hX : 0 < X) (hsigma : 1 < sigma) (hsigmaUpper : sigma ≤ 2)
    (hT : 0 < T) (hM : 0 ≤ M)
    (hL : ∀ t : ℝ, |t| ≤ T →
      ‖LSeries h ((sigma : ℂ) + t * I)‖ ≤ M) :
    ‖∑ n ∈ Finset.Ioc X (2 * X), h n‖ ≤
      perronTruncationError h (2 * X) sigma T +
        perronVerticalMajorant M (2 * X) sigma T +
      (perronTruncationError h X sigma T +
        perronVerticalMajorant M X sigma T) + 1 := by
  apply norm_sum_Ioc_le_of_oneBounded_uniform_vertical_LSeries
    (fun n hn ↦ (hh (n := n) hn).le) hX hsigma hsigmaUpper hT hM hL

/-- The same estimate in the normalization used by `longIntervalMean`. -/
theorem norm_longIntervalMean_le_of_uniform_vertical_LSeries
    {a : ℕ → ℂ} {X : ℕ} {sigma T M R : ℝ}
    (hsum : LSeriesSummable a (sigma : ℂ))
    (hX : 0 < X) (hsigma : 0 < sigma) (hsigmaUpper : sigma ≤ 2)
    (hT : 0 < T) (hM : 0 ≤ M)
    (hL : ∀ t : ℝ, |t| ≤ T →
      ‖LSeries a ((sigma : ℂ) + t * I)‖ ≤ M)
    (hR :
      perronTruncationError a (2 * X) sigma T +
          perronVerticalMajorant M (2 * X) sigma T +
        (perronTruncationError a X sigma T +
          perronVerticalMajorant M X sigma T) +
        (1 / 2 : ℝ) * (‖a (2 * X)‖ + ‖a X‖) ≤ R) :
    ‖Erdos67.longIntervalMean a X‖ ≤ R / X := by
  have hsumBound := (norm_sum_Ioc_le_of_uniform_vertical_LSeries
    hsum hX hsigma hsigmaUpper hT hM hL).trans hR
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  unfold Erdos67.longIntervalMean
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    (X : ℝ)⁻¹ * ‖∑ m ∈ Finset.Ioc X (2 * X), a m‖ ≤
        (X : ℝ)⁻¹ * R :=
      mul_le_mul_of_nonneg_left hsumBound (inv_nonneg.mpr hXR.le)
    _ = R / X := by rw [div_eq_mul_inv]; ring

end

end Erdos67.MRHalaszPerron
