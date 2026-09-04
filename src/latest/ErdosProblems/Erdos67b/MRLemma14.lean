import ErdosProblems.Erdos67b.MRShortIntervalFourier
import ErdosProblems.Erdos67b.MRHalaszPerron
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A finite Lemma-14 vertical mean-square reduction

This file isolates the Parseval/Perron-shaped reduction used in Lemma 14 of
Matomäki--Radziwiłł.  Everything here is finite.  The coefficient polynomial
is supported on one dyadic interval, and its vertical mean square is split
exactly into a central segment and finitely many dyadic shells.
-/

open scoped BigOperators ComplexConjugate
open Finset MeasureTheory

namespace Erdos67b

noncomputable section

open BoundedGaps.Maynard

/-- The coefficient support on one dyadic interval. -/
def dyadicRestrictedSupport (S : Finset ℕ) (X : ℕ) : Finset ℕ :=
  Finset.Ioc X (2 * X) ∩ S

/-- The zero extension of a coefficient restricted to `(X,2X] ∩ S`. -/
def dyadicRestrictedCoefficient (S : Finset ℕ) (f : ℕ → ℂ) (X n : ℕ) : ℂ :=
  if n ∈ dyadicRestrictedSupport S X then f n else 0

/-- The finite vertical Dirichlet polynomial.  The sign convention is the
usual `F(1+it)`: the logarithmic phase is evaluated at `-t`. -/
def dyadicVerticalDirichletPolynomial
    (S : Finset ℕ) (f : ℕ → ℂ) (X : ℕ) (t : ℝ) : ℂ :=
  logarithmicDirichletPolynomial (dyadicRestrictedSupport S X)
    (fun n ↦ f n / (n : ℂ)) (-t)

/-- A symmetric vertical `L²` segment. -/
def symmetricVerticalEnergy (F : ℝ → ℂ) (T : ℝ) : ℝ :=
  ∫ t in -T..T, Complex.normSq (F t)

/-- The central segment together with the first `J` positive and negative
dyadic shells.  Its outer endpoint is `2^J T`. -/
def dyadicVerticalEnergy (F : ℝ → ℂ) (T : ℝ) (J : ℕ) : ℝ :=
  symmetricVerticalEnergy F T +
    ∑ j ∈ Finset.range J,
      ((∫ t in -(((2 : ℕ) ^ (j + 1) : ℕ) : ℝ) * T..
                    -(((2 : ℕ) ^ j : ℕ) : ℝ) * T,
            Complex.normSq (F t)) +
        ∫ t in (((2 : ℕ) ^ j : ℕ) : ℝ) * T..
                  (((2 : ℕ) ^ (j + 1) : ℕ) : ℝ) * T,
            Complex.normSq (F t))

private theorem dyadicScale_succ (T : ℝ) (j : ℕ) :
    ((((2 : ℕ) ^ (j + 1) : ℕ) : ℝ) * T) =
      2 * ((((2 : ℕ) ^ j : ℕ) : ℝ) * T) := by
  push_cast
  rw [pow_succ]
  ring

/-- The displayed low-frequency plus dyadic-shell expression is exactly the
single symmetric integral up to its outer endpoint. -/
theorem dyadicVerticalEnergy_eq_symmetric
    (F : ℝ → ℂ) (hF : Continuous F) (T : ℝ) (J : ℕ) :
    dyadicVerticalEnergy F T J =
      symmetricVerticalEnergy F ((((2 : ℕ) ^ J : ℕ) : ℝ) * T) := by
  induction J with
  | zero => simp [dyadicVerticalEnergy, symmetricVerticalEnergy]
  | succ J ih =>
      have hcont : Continuous (fun t : ℝ ↦ Complex.normSq (F t)) := by
        fun_prop
      rw [dyadicVerticalEnergy, Finset.sum_range_succ]
      rw [← add_assoc]
      change dyadicVerticalEnergy F T J + _ = _
      rw [ih]
      unfold symmetricVerticalEnergy
      let A : ℝ := (((2 : ℕ) ^ J : ℕ) : ℝ) * T
      let B : ℝ := (((2 : ℕ) ^ (J + 1) : ℕ) : ℝ) * T
      have hneg : IntervalIntegrable (fun t : ℝ ↦ Complex.normSq (F t)) volume (-B) (-A) :=
        hcont.intervalIntegrable _ _
      have hmid : IntervalIntegrable (fun t : ℝ ↦ Complex.normSq (F t)) volume (-A) A :=
        hcont.intervalIntegrable _ _
      have hpos : IntervalIntegrable (fun t : ℝ ↦ Complex.normSq (F t)) volume A B :=
        hcont.intervalIntegrable _ _
      have hleft := intervalIntegral.integral_add_adjacent_intervals hneg hmid
      have hright := intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable (-B) A) hpos
      dsimp [A, B] at hleft hright
      simp only [← neg_mul] at hleft hright
      simp only [← neg_mul]
      rw [← add_assoc]
      rw [add_comm
        (∫ t in -(((2 : ℕ) ^ J : ℕ) : ℝ) * T..
                    (((2 : ℕ) ^ J : ℕ) : ℝ) * T,
              Complex.normSq (F t))
        (∫ t in -(((2 : ℕ) ^ (J + 1) : ℕ) : ℝ) * T..
                    -(((2 : ℕ) ^ J : ℕ) : ℝ) * T,
              Complex.normSq (F t))]
      rw [hleft, hright]

/-- The subtype-indexed frequency polynomial is the finset-indexed
logarithmic Dirichlet polynomial. -/
theorem finiteFrequencyPolynomial_subtype_eq_logarithmic
    (D : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    finiteFrequencyPolynomial (fun n : ↥D ↦ Real.log n.1)
        (fun n : ↥D ↦ a n.1) t =
      logarithmicDirichletPolynomial D a t := by
  classical
  unfold finiteFrequencyPolynomial logarithmicDirichletPolynomial
  rw [Finset.univ_eq_attach D]
  change (∑ n ∈ D.attach, a n.1 * logarithmicPhase n.1 t) = _
  exact Finset.sum_attach D (fun n ↦ a n * logarithmicPhase n t)

/-- A finite vertical Dirichlet polynomial is continuous in its height. -/
theorem continuous_dyadicVerticalDirichletPolynomial
    (S : Finset ℕ) (f : ℕ → ℂ) (X : ℕ) :
    Continuous (dyadicVerticalDirichletPolynomial S f X) := by
  unfold dyadicVerticalDirichletPolynomial logarithmicDirichletPolynomial
  unfold logarithmicPhase
  fun_prop

/-- The normalized Perron increment on the line `Re s = 1`.  This is the
kernel that occurs after dividing a short sum by its interval length. -/
def perronIncrementKernel (x h t : ℝ) : ℂ :=
  (((x + h : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) -
      (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)) /
    ((h : ℂ) * ((1 : ℂ) + (t : ℂ) * Complex.I))

/-- The Perron increment is exactly the average of the phases
`y ↦ y^(it)` across the short interval. -/
theorem perronIncrementKernel_eq_average (x h t : ℝ) :
    perronIncrementKernel x h t =
      (h : ℂ)⁻¹ * ∫ y in x..x + h, (y : ℂ) ^ ((t : ℂ) * Complex.I) := by
  have hint := integral_cpow (a := x) (b := x + h)
    (r := (t : ℂ) * Complex.I) (Or.inl (by simp))
  unfold perronIncrementKernel
  rw [hint]
  have hs : (t : ℂ) * Complex.I + 1 = 1 + (t : ℂ) * Complex.I := by ring
  rw [hs]
  field_simp

/-- On `Re s = 1`, the normalized Perron increment has norm at most one. -/
theorem norm_perronIncrementKernel_le_one
    {x h : ℝ} (hx : 0 < x) (hh : 0 < h) (t : ℝ) :
    ‖perronIncrementKernel x h t‖ ≤ 1 := by
  rw [perronIncrementKernel_eq_average]
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hh]
  have hnorm :
      ‖∫ y in x..x + h, (y : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤ h := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun y : ℝ ↦ (y : ℂ) ^ ((t : ℂ) * Complex.I))
      (C := 1) (a := x) (b := x + h) (fun y hy ↦ by
        rw [Set.uIoc_of_le (by linarith)] at hy
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (hx.trans hy.1)]
        simp)
    simpa [abs_of_pos hh] using hb
  calc
    h⁻¹ * ‖∫ y in x..x + h, (y : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤
        h⁻¹ * h := mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hh.le)
    _ = 1 := inv_mul_cancel₀ hh.ne'

/-- Away from zero, the endpoint form of the Perron kernel gives the
high-frequency decay used in the dyadic-shell part of Lemma 14. -/
theorem norm_perronIncrementKernel_le_div_abs
    {x h t : ℝ} (hx : 0 ≤ x) (hh : 0 < h) (ht : t ≠ 0) :
    ‖perronIncrementKernel x h t‖ ≤ (2 * x + h) / (h * |t|) := by
  unfold perronIncrementKernel
  have hxph : 0 < x + h := by linarith
  have hpow1 :
      ‖((x + h : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)‖ = x + h := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxph]
    simp
  have hpow0 :
      ‖(x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)‖ = x := by
    rcases hx.eq_or_lt with rfl | hxpos
    · have hsne : (1 : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
        intro hs
        apply_fun Complex.re at hs
        norm_num at hs
      simp [Complex.zero_cpow hsne]
    · rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
      simp
  have hsNorm : |t| ≤ ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ := by
    have hi : (((1 : ℂ) + (t : ℂ) * Complex.I).im) = t := by simp
    simpa [hi] using Complex.abs_im_le_norm ((1 : ℂ) + (t : ℂ) * Complex.I)
  have htpos : 0 < |t| := abs_pos.mpr ht
  have hspos : 0 < ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ := htpos.trans_le hsNorm
  have hnum :
      ‖((x + h : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) -
        (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 2 * x + h := by
    calc
      _ ≤ ‖((x + h : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)‖ +
          ‖(x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)‖ := norm_sub_le _ _
      _ = 2 * x + h := by rw [hpow1, hpow0]; ring
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  calc
    _ ≤ (2 * x + h) / (h * ‖(1 : ℂ) + (t : ℂ) * Complex.I‖) :=
      div_le_div_of_nonneg_right hnum (mul_pos hh hspos).le
    _ ≤ (2 * x + h) / (h * |t|) := by
      apply div_le_div_of_nonneg_left (by linarith) (mul_pos hh htpos)
      exact mul_le_mul_of_nonneg_left hsNorm hh.le

/-- Factorization of the Perron monomial on `Re s = 1` into its size and
unit logarithmic phase. -/
theorem nat_cpow_one_add_mul_I_eq_phase
    {y : ℕ} (hy : 0 < y) (t : ℝ) :
    (y : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) =
      (y : ℂ) * realExponentialPhase (t * Real.log y) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hy.ne')]
  have hlog : Complex.log (y : ℂ) = (Real.log y : ℂ) := by
    simpa only [Complex.ofReal_natCast] using
      (Complex.ofReal_log (show (0 : ℝ) ≤ y by positivity)).symm
  rw [hlog]
  unfold realExponentialPhase
  have hexp :
      (Real.log y : ℂ) * ((1 : ℂ) + (t : ℂ) * Complex.I) =
        (Real.log y : ℂ) + ((t * Real.log y : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hexp, Complex.exp_add, ← Complex.ofReal_exp,
    Real.exp_log (by positivity)]
  norm_num

/-- Real-base version of the same Perron-monomial factorization. -/
theorem ofReal_cpow_one_add_mul_I_eq_phase
    {y : ℝ} (hy : 0 < y) (t : ℝ) :
    (y : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) =
      (y : ℂ) * realExponentialPhase (t * Real.log y) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne')]
  have hlog : Complex.log (y : ℂ) = (Real.log y : ℂ) := by
    exact (Complex.ofReal_log hy.le).symm
  rw [hlog]
  unfold realExponentialPhase
  have hexp :
      (Real.log y : ℂ) * ((1 : ℂ) + (t : ℂ) * Complex.I) =
        (Real.log y : ℂ) + ((t * Real.log y : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hexp, Complex.exp_add, ← Complex.ofReal_exp,
    Real.exp_log hy]

/-- The dyadically restricted coefficient has a finite-support `LSeries`,
so it is summable on every vertical line, including the critical Perron line
`Re s = 1`. -/
theorem dyadicRestrictedCoefficient_LSeriesSummable
    (S : Finset ℕ) (f : ℕ → ℂ) (X : ℕ) (s : ℂ) :
    LSeriesSummable (dyadicRestrictedCoefficient S f X) s := by
  rw [LSeriesSummable]
  apply summable_of_ne_finset_zero (s := dyadicRestrictedSupport S X)
  intro n hn
  unfold LSeries.term dyadicRestrictedCoefficient
  simp [hn]

/-- On the line `Re s = 1`, the finite `LSeries` of the restricted
coefficient is exactly the vertical Dirichlet polynomial defined above. -/
theorem LSeries_dyadicRestrictedCoefficient_eq_vertical
    (S : Finset ℕ) (f : ℕ → ℂ) (X : ℕ) (t : ℝ) :
    LSeries (dyadicRestrictedCoefficient S f X)
        ((1 : ℂ) + (t : ℂ) * Complex.I) =
      dyadicVerticalDirichletPolynomial S f X t := by
  classical
  unfold LSeries
  rw [tsum_eq_sum (s := dyadicRestrictedSupport S X)]
  · unfold dyadicVerticalDirichletPolynomial logarithmicDirichletPolynomial
    apply Finset.sum_congr rfl
    intro n hn
    have hnpos : 0 < n := by
      rw [dyadicRestrictedSupport, Finset.mem_inter, Finset.mem_Ioc] at hn
      omega
    unfold LSeries.term dyadicRestrictedCoefficient logarithmicPhase
    rw [if_pos hn, if_neg hnpos.ne']
    have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
      simpa only [Complex.ofReal_natCast] using
        (Complex.ofReal_log (show (0 : ℝ) ≤ n by positivity)).symm
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hnpos.ne')]
    rw [hlog]
    have hexp :
        (Real.log n : ℂ) * ((1 : ℂ) + (t : ℂ) * Complex.I) =
          (Real.log n : ℂ) + (Real.log n : ℂ) * (t : ℂ) * Complex.I := by
      ring
    rw [hexp, Complex.exp_add]
    rw [← Complex.ofReal_exp, Real.exp_log (by positivity)]
    have hphase :
        -(Real.log n : ℂ) * (t : ℂ) * Complex.I =
          (-t * Real.log n : ℝ) * Complex.I := by
      push_cast
      ring
    rw [← hphase]
    have hneg :
        -(Real.log n : ℂ) * (t : ℂ) * Complex.I =
          -((Real.log n : ℂ) * (t : ℂ) * Complex.I) := by ring
    rw [hneg, Complex.exp_neg]
    field_simp
    norm_num
  · intro n hn
    unfold LSeries.term dyadicRestrictedCoefficient
    simp [hn]

/-- Exact finite Perron reduction for a normalized short interval.  The
difference of the two truncated Perron integrals is the vertical integral of
the source Lemma-14 increment kernel; no truncation or endpoint error is
hidden in this identity. -/
theorem dirichletPerronIntegral_shortDifference_eq
    {a : ℕ → ℂ} (hsum : LSeriesSummable a (1 : ℂ))
    {x h : ℝ} (hx : 0 < x) (hh : 0 < h) (T : ℝ) :
    (dirichletPerronIntegral a (x + h) 1 T -
        dirichletPerronIntegral a x 1 T) / (h : ℂ) =
      (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
        ∫ t in -T..T,
          LSeries a ((1 : ℂ) + (t : ℂ) * Complex.I) *
            perronIncrementKernel x h t := by
  have hxph : 0 < x + h := by linarith
  have hplus := intervalIntegrable_dirichletPerronLSeriesIntegrand
    (a := a) (y := x + h) (alpha := 1) (U := T) hsum hxph (by norm_num)
  have hbase := intervalIntegrable_dirichletPerronLSeriesIntegrand
    (a := a) (y := x) (alpha := 1) (U := T) hsum hx (by norm_num)
  let c : ℂ := (((2 * Real.pi : ℝ) : ℂ)⁻¹)
  let L : ℝ → ℂ := fun t ↦ LSeries a ((1 : ℂ) + (t : ℂ) * Complex.I)
  let A : ℝ → ℂ := fun t ↦
    L t * ((((x + h : ℝ) : ℂ)) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) /
      ((1 : ℂ) + (t : ℂ) * Complex.I))
  let B : ℝ → ℂ := fun t ↦
    L t * ((x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I) /
      ((1 : ℂ) + (t : ℂ) * Complex.I))
  unfold dirichletPerronIntegral
  simp only [mul_div_assoc, Complex.ofReal_one]
  change (c * (∫ t in -T..T, A t) - c * (∫ t in -T..T, B t)) / (h : ℂ) =
    c * ∫ t in -T..T, L t * perronIncrementKernel x h t
  have hA : IntervalIntegrable A volume (-T) T := by
    convert hplus using 1 <;> norm_num [A, L, mul_div_assoc]
  have hB : IntervalIntegrable B volume (-T) T := by
    convert hbase using 1 <;> norm_num [B, L, mul_div_assoc]
  rw [← mul_sub]
  rw [mul_div_assoc]
  rw [← intervalIntegral.integral_sub hA hB]
  calc
    c * ((∫ t in -T..T, A t - B t) / (h : ℂ)) =
        c * ∫ t in -T..T, (A t - B t) / (h : ℂ) := by
      rw [intervalIntegral.integral_div]
    _ = c * ∫ t in -T..T, L t * perronIncrementKernel x h t := by
      congr 1
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only [A, B]
      unfold perronIncrementKernel
      field_simp

/-- Specialized source-ready form: for the finite typical/dyadic
coefficient, the exact Perron integrand contains the concrete polynomial
`F(1+it)` rather than an abstract `LSeries`. -/
theorem dyadicRestrictedPerron_shortDifference_eq
    (S : Finset ℕ) (f : ℕ → ℂ) (X : ℕ)
    {x h : ℝ} (hx : 0 < x) (hh : 0 < h) (T : ℝ) :
    (dirichletPerronIntegral (dyadicRestrictedCoefficient S f X)
          (x + h) 1 T -
        dirichletPerronIntegral (dyadicRestrictedCoefficient S f X)
          x 1 T) / (h : ℂ) =
      (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
        ∫ t in -T..T,
          dyadicVerticalDirichletPolynomial S f X t *
            perronIncrementKernel x h t := by
  simpa only [LSeries_dyadicRestrictedCoefficient_eq_vertical] using
    (dirichletPerronIntegral_shortDifference_eq
      (dyadicRestrictedCoefficient_LSeriesSummable S f X (1 : ℂ)) hx hh T)

/-- Exact comparison of two normalized Perron short averages, the form in
which Lemma 14 exploits cancellation at low frequency. -/
theorem dyadicRestrictedPerron_twoLengths_eq
    (S : Finset ℕ) (f : ℕ → ℂ) (X : ℕ)
    {x h₁ h₂ : ℝ} (hx : 0 < x) (hh₁ : 0 < h₁) (hh₂ : 0 < h₂)
    (T : ℝ) :
    (dirichletPerronIntegral (dyadicRestrictedCoefficient S f X)
          (x + h₁) 1 T -
        dirichletPerronIntegral (dyadicRestrictedCoefficient S f X)
          x 1 T) / (h₁ : ℂ) -
      (dirichletPerronIntegral (dyadicRestrictedCoefficient S f X)
          (x + h₂) 1 T -
        dirichletPerronIntegral (dyadicRestrictedCoefficient S f X)
          x 1 T) / (h₂ : ℂ) =
      (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
        ((∫ t in -T..T,
            dyadicVerticalDirichletPolynomial S f X t *
              perronIncrementKernel x h₁ t) -
          ∫ t in -T..T,
            dyadicVerticalDirichletPolynomial S f X t *
              perronIncrementKernel x h₂ t) := by
  rw [dyadicRestrictedPerron_shortDifference_eq S f X hx hh₁ T,
    dyadicRestrictedPerron_shortDifference_eq S f X hx hh₂ T]
  ring

/-- Uniform low-frequency bound for the difference of the two normalized
Perron kernels. -/
theorem norm_perronIncrementKernel_sub_le_two
    {x h₁ h₂ : ℝ} (hx : 0 < x) (hh₁ : 0 < h₁) (hh₂ : 0 < h₂)
    (t : ℝ) :
    ‖perronIncrementKernel x h₁ t - perronIncrementKernel x h₂ t‖ ≤ 2 := by
  calc
    _ ≤ ‖perronIncrementKernel x h₁ t‖ +
        ‖perronIncrementKernel x h₂ t‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add
      (norm_perronIncrementKernel_le_one hx hh₁ t)
      (norm_perronIncrementKernel_le_one hx hh₂ t)
    _ = 2 := by norm_num

/-- Pure-imaginary powers of a positive real number are logarithmic
phases. -/
theorem ofReal_cpow_mul_I_eq_phase
    {y : ℝ} (hy : 0 < y) (t : ℝ) :
    (y : ℂ) ^ ((t : ℂ) * Complex.I) =
      realExponentialPhase (t * Real.log y) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne')]
  rw [(Complex.ofReal_log hy.le).symm]
  unfold realExponentialPhase
  congr 1
  push_cast
  ring

/-- Real exponential phases are one-Lipschitz. -/
theorem norm_realExponentialPhase_sub_le (u v : ℝ) :
    ‖realExponentialPhase u - realExponentialPhase v‖ ≤ |u - v| := by
  unfold realExponentialPhase
  have hid : Complex.exp (u * Complex.I) - Complex.exp (v * Complex.I) =
      Complex.exp (v * Complex.I) *
        (Complex.exp ((u - v) * Complex.I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hid, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  convert (Real.norm_exp_I_mul_ofReal_sub_one_le (x := u - v)) using 1 <;>
    try { push_cast; ring_nf }
  rw [Real.norm_eq_abs]

/-- The logarithm changes by at most relative interval length. -/
theorem log_sub_log_le_sub_div
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Real.log y - Real.log x ≤ (y - x) / x := by
  have hy : 0 < y := hx.trans_le hxy
  calc
    Real.log y - Real.log x = Real.log (y / x) := by
      rw [Real.log_div hy.ne' hx.ne']
    _ ≤ y / x - 1 := Real.log_le_sub_one_of_pos (div_pos hy hx)
    _ = (y - x) / x := by
      field_simp

/-- A normalized Perron increment differs from the phase at its left
endpoint by at most `|t| h/x`.  This is the cancellation absent from a
single-kernel norm bound. -/
theorem norm_perronIncrementKernel_sub_leftPhase_le
    {x h : ℝ} (hx : 0 < x) (hh : 0 < h) (t : ℝ) :
    ‖perronIncrementKernel x h t -
        realExponentialPhase (t * Real.log x)‖ ≤ |t| * h / x := by
  let p : ℝ → ℂ := fun y ↦ realExponentialPhase (t * Real.log y)
  let px : ℂ := realExponentialPhase (t * Real.log x)
  have hxph : 0 < x + h := by linarith
  have hpcont : ContinuousOn p (Set.uIcc x (x + h)) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro y hy
    have hypos : 0 < y := hx.trans_le hy.1
    exact (by
      unfold p realExponentialPhase
      fun_prop : ContinuousAt p y).continuousWithinAt
  have havg : perronIncrementKernel x h t =
      (h : ℂ)⁻¹ * ∫ y in x..x + h, p y := by
    rw [perronIncrementKernel_eq_average]
    congr 1
    apply intervalIntegral.integral_congr
    intro y hy
    have hxh : x ≤ x + h := by linarith
    rw [Set.uIcc_of_le hxh] at hy
    have hypos : 0 < y := hx.trans_le hy.1
    exact ofReal_cpow_mul_I_eq_phase hypos t
  have hpconst : (∫ _y in x..x + h, px) = (h : ℂ) * px := by
    rw [intervalIntegral.integral_const]
    simp only [add_sub_cancel_left, Complex.real_smul]
  have hdiff : perronIncrementKernel x h t - px =
      (h : ℂ)⁻¹ * ∫ y in x..x + h, (p y - px) := by
    rw [havg]
    have hpx : px = (h : ℂ)⁻¹ * ((h : ℂ) * px) := by
      rw [← mul_assoc, inv_mul_cancel₀ (show (h : ℂ) ≠ 0 by exact_mod_cast hh.ne')]
      simp
    calc
      (h : ℂ)⁻¹ * (∫ y in x..x + h, p y) - px =
          (h : ℂ)⁻¹ * (∫ y in x..x + h, p y) -
            (h : ℂ)⁻¹ * ((h : ℂ) * px) := by rw [← hpx]
      _ = (h : ℂ)⁻¹ * (∫ y in x..x + h, p y) -
            (h : ℂ)⁻¹ * (∫ _y in x..x + h, px) := by rw [hpconst]
      _ = (h : ℂ)⁻¹ *
            ((∫ y in x..x + h, p y) - (∫ _y in x..x + h, px)) := by ring
      _ = (h : ℂ)⁻¹ * (∫ y in x..x + h, (p y - px)) := by
        rw [intervalIntegral.integral_sub
          (hpcont.intervalIntegrable)
          continuousOn_const.intervalIntegrable]
  have hpoint (y : ℝ) (hy : y ∈ Set.uIoc x (x + h)) :
      ‖p y - px‖ ≤ |t| * h / x := by
    rw [Set.uIoc_of_le (by linarith)] at hy
    have hypos : 0 < y := hx.trans hy.1
    have hlogNonneg : 0 ≤ Real.log y - Real.log x := by
      exact sub_nonneg.mpr (Real.strictMonoOn_log.monotoneOn
        (show x ∈ Set.Ioi 0 from hx) (show y ∈ Set.Ioi 0 from hypos) hy.1.le)
    have hlog := log_sub_log_le_sub_div hx hy.1.le
    have hyx : y - x ≤ h := by linarith [hy.2]
    have hdiv : (y - x) / x ≤ h / x := by
      exact div_le_div_of_nonneg_right hyx hx.le
    have hphase := norm_realExponentialPhase_sub_le
      (t * Real.log y) (t * Real.log x)
    dsimp [p, px]
    calc
      _ ≤ |t * Real.log y - t * Real.log x| := hphase
      _ = |t| * (Real.log y - Real.log x) := by
        rw [← mul_sub, abs_mul, abs_of_nonneg hlogNonneg]
      _ ≤ |t| * (h / x) :=
        mul_le_mul_of_nonneg_left (hlog.trans hdiv) (abs_nonneg t)
      _ = |t| * h / x := by ring
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun y ↦ p y - px) (C := |t| * h / x)
    (a := x) (b := x + h) hpoint
  rw [hdiff, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hh]
  calc
    h⁻¹ * ‖∫ y in x..x + h, (p y - px)‖ ≤
        h⁻¹ * (|t| * h / x * |x + h - x|) :=
      mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hh.le)
    _ = |t| * h / x := by
      have habs : |x + h - x| = h := by
        rw [show x + h - x = h by ring, abs_of_pos hh]
      rw [habs]
      field_simp

/-- Low-frequency cancellation for two normalized short intervals. -/
theorem norm_perronIncrementKernel_sub_le_relative
    {x h₁ h₂ : ℝ} (hx : 0 < x) (hh₁ : 0 < h₁) (hh₂ : 0 < h₂)
    (t : ℝ) :
    ‖perronIncrementKernel x h₁ t - perronIncrementKernel x h₂ t‖ ≤
      |t| * (h₁ + h₂) / x := by
  let p : ℂ := realExponentialPhase (t * Real.log x)
  calc
    _ = ‖(perronIncrementKernel x h₁ t - p) -
          (perronIncrementKernel x h₂ t - p)‖ := by congr 1; ring
    _ ≤ ‖perronIncrementKernel x h₁ t - p‖ +
        ‖perronIncrementKernel x h₂ t - p‖ := norm_sub_le _ _
    _ ≤ |t| * h₁ / x + |t| * h₂ / x := add_le_add
      (norm_perronIncrementKernel_sub_leftPhase_le hx hh₁ t)
      (norm_perronIncrementKernel_sub_leftPhase_le hx hh₂ t)
    _ = |t| * (h₁ + h₂) / x := by ring

/-- Explicit high-frequency decay for the difference of two normalized
Perron kernels.  Dyadic integration of this estimate produces precisely the
`X/(hT)` shell weight after the logarithmic Plancherel step. -/
theorem norm_perronIncrementKernel_sub_le_div_abs
    {x h₁ h₂ t : ℝ} (hx : 0 ≤ x) (hh₁ : 0 < h₁) (hh₂ : 0 < h₂)
    (ht : t ≠ 0) :
    ‖perronIncrementKernel x h₁ t - perronIncrementKernel x h₂ t‖ ≤
      (2 * x + h₁) / (h₁ * |t|) +
        (2 * x + h₂) / (h₂ * |t|) := by
  exact (norm_sub_le _ _).trans (add_le_add
    (norm_perronIncrementKernel_le_div_abs hx hh₁ ht)
    (norm_perronIncrementKernel_le_div_abs hx hh₂ ht))

/-- Exact endpoint bookkeeping for an arbitrary short interval. -/
theorem sum_Ioc_eq_starred_shortDifference_add_endpoints
    (a : ℕ → ℂ) {x H : ℕ} (hx : 0 < x) :
    (∑ n ∈ Finset.Ioc x (x + H), a n) =
      dirichletPerronStarredSum a (x + H) -
        dirichletPerronStarredSum a x +
          (1 / 2 : ℂ) * (a (x + H) - a x) := by
  have hIoc :
      (∑ n ∈ Finset.Ioc x (x + H), a n) =
        (∑ n ∈ Finset.range (x + H), a n) -
          (∑ n ∈ Finset.range x, a n) - a x + a (x + H) := by
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

/-- The completely explicit Perron truncation and half-endpoint error for a
normalized short interval. -/
def lemma14PerronEndpointError
    (a : ℕ → ℂ) (x H : ℕ) (T : ℝ) : ℝ :=
  (MRHalaszPerron.perronTruncationError a (x + H) 1 T +
      MRHalaszPerron.perronTruncationError a x 1 T +
      (1 / 2 : ℝ) * (‖a (x + H)‖ + ‖a x‖)) / H

/-- The part of the Perron error that genuinely vanishes with truncation
height.  Half-endpoint terms are not included: they are absorbed into the
endpoint-corrected Perron model below. -/
def lemma14PerronTruncationError
    (a : ℕ → ℂ) (x H : ℕ) (T : ℝ) : ℝ :=
  (MRHalaszPerron.perronTruncationError a (x + H) 1 T +
      MRHalaszPerron.perronTruncationError a x 1 T) / H

/-- Each individual near-diagonal Perron kernel error vanishes as the
vertical height tends to infinity. -/
theorem tendsto_dirichletPerronNearError_atTop (z n : ℕ) :
    Filter.Tendsto (fun T : ℝ ↦ dirichletPerronNearError z T n)
      Filter.atTop (nhds 0) := by
  unfold dirichletPerronNearError
  split_ifs with hcentral
  · have hdist : 0 < |(z : ℝ) - n| := by
      apply abs_pos.mpr
      rw [sub_ne_zero]
      exact_mod_cast hcentral.2.2.2.symm
    have hquot : Filter.Tendsto
        (fun T : ℝ ↦ (2 * (z : ℝ) / |(z : ℝ) - n|) / T)
        Filter.atTop (nhds 0) :=
      Filter.tendsto_id.const_div_atTop _
    have heq : (fun T : ℝ ↦
        2 * (z : ℝ) / (T * |(z : ℝ) - n|)) =
        fun T : ℝ ↦ (2 * (z : ℝ) / |(z : ℝ) - n|) / T := by
      funext T
      field_simp [hdist.ne']
    have heqmin : (fun T : ℝ ↦
        min 1 (2 * (z : ℝ) / (T * |(z : ℝ) - n|))) =
        fun T : ℝ ↦ min 1 ((2 * (z : ℝ) / |(z : ℝ) - n|) / T) :=
      congrArg (fun q : ℝ → ℝ ↦ fun T ↦ min 1 (q T)) heq
    rw [heqmin]
    simpa using ((tendsto_const_nhds : Filter.Tendsto
      (fun _ : ℝ ↦ (1 : ℝ)) Filter.atTop (nhds 1)).min hquot)
  · exact tendsto_const_nhds

/-- The entire near-diagonal mass tends to zero.  Its apparently infinite
sum is actually supported on the fixed finite set `range (2*z)`. -/
theorem tendsto_dirichletPerronNearMass_atTop (a : ℕ → ℂ) (z : ℕ) :
    Filter.Tendsto (fun T : ℝ ↦ dirichletPerronNearMass a z T)
      Filter.atTop (nhds 0) := by
  have heq : (fun T : ℝ ↦ dirichletPerronNearMass a z T) =
      fun T : ℝ ↦ ∑ n ∈ Finset.range (2 * z),
        ‖a n‖ * dirichletPerronNearError z T n := by
    funext T
    unfold dirichletPerronNearMass
    rw [tsum_eq_sum (s := Finset.range (2 * z))]
    intro n hn
    have hnLower : 2 * z ≤ n := by simpa using hn
    have hnLowerR : (2 : ℝ) * z ≤ n := by exact_mod_cast hnLower
    rw [dirichletPerronNearError, if_neg]
    · simp
    · intro h
      exact (not_lt_of_ge hnLowerR) h.2.2.1
  rw [heq]
  simpa using tendsto_finset_sum (Finset.range (2 * z)) (fun n hn ↦
    (tendsto_dirichletPerronNearError_atTop z n).const_mul ‖a n‖)

/-- The explicit Perron truncation error tends to zero for every fixed
coefficient and endpoint. -/
theorem tendsto_perronTruncationError_atTop (a : ℕ → ℂ) (z : ℕ) :
    Filter.Tendsto (fun T : ℝ ↦
        MRHalaszPerron.perronTruncationError a z 1 T)
      Filter.atTop (nhds 0) := by
  have hnear := tendsto_dirichletPerronNearMass_atTop a z
  have htail : Filter.Tendsto (fun T : ℝ ↦
      (32 * (z : ℝ) ^ (1 : ℝ) / T) *
        dirichletPerronCoefficientMass a 1) Filter.atTop (nhds 0) := by
    have hdiv : Filter.Tendsto (fun T : ℝ ↦
        (32 * (z : ℝ) ^ (1 : ℝ)) / T) Filter.atTop (nhds 0) :=
      Filter.tendsto_id.const_div_atTop _
    simpa using hdiv.mul_const (dirichletPerronCoefficientMass a 1)
  unfold MRHalaszPerron.perronTruncationError
  simpa using hnear.add htail

/-- The pure two-endpoint normalized truncation error tends to zero. -/
theorem tendsto_lemma14PerronTruncationError_atTop
    (a : ℕ → ℂ) (x H : ℕ) :
    Filter.Tendsto (fun T : ℝ ↦ lemma14PerronTruncationError a x H T)
      Filter.atTop (nhds 0) := by
  unfold lemma14PerronTruncationError
  simpa using ((tendsto_perronTruncationError_atTop a (x + H)).add
    (tendsto_perronTruncationError_atTop a x)).div_const (H : ℝ)

/-- The actual normalized dyadically restricted short sum. -/
def dyadicRestrictedShortAverage
    (S : Finset ℕ) (f : ℕ → ℂ) (X x H : ℕ) : ℂ :=
  (∑ n ∈ Finset.Ioc x (x + H),
    dyadicRestrictedCoefficient S f X n) / (H : ℂ)

/-- The truncated Perron model for the normalized short sum. -/
def dyadicRestrictedPerronAverage
    (S : Finset ℕ) (f : ℕ → ℂ) (X : ℕ)
    (x H T : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
    ∫ t in -T..T,
      dyadicVerticalDirichletPolynomial S f X t *
        perronIncrementKernel x H t

/-- The half-endpoint term which must be added to a Perron integral before
taking its truncation height to infinity. -/
def dyadicRestrictedPerronEndpointCorrection
    (S : Finset ℕ) (f : ℕ → ℂ) (X x H : ℕ) : ℂ :=
  (1 / 2 : ℂ) *
      (dyadicRestrictedCoefficient S f X (x + H) -
        dyadicRestrictedCoefficient S f X x) / (H : ℂ)

/-- Perron model with the exact half-endpoint convention reconciled with
the actual interval `(x,x+H]`. -/
def dyadicRestrictedCorrectedPerronAverage
    (S : Finset ℕ) (f : ℕ → ℂ) (X x H : ℕ) (T : ℝ) : ℂ :=
  dyadicRestrictedPerronAverage S f X x H T +
    dyadicRestrictedPerronEndpointCorrection S f X x H

/-- The actual normalized finite short sum differs from the concrete
Perron-kernel integral by only the explicit countable-Perron truncation and
half-endpoint terms.  This is the pointwise finite version of the first
reduction in source Lemma 14. -/
theorem norm_dyadicShortAverage_sub_perron_le_endpointError
    (S : Finset ℕ) (f : ℕ → ℂ) (X : ℕ)
    {x H : ℕ} (hx : 0 < x) (hH : 0 < H) {T : ℝ} (hT : 0 < T) :
    ‖((∑ n ∈ Finset.Ioc x (x + H),
          dyadicRestrictedCoefficient S f X n) / (H : ℂ)) -
        (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
          ∫ t in -T..T,
            dyadicVerticalDirichletPolynomial S f X t *
              perronIncrementKernel x H t‖ ≤
      lemma14PerronEndpointError (dyadicRestrictedCoefficient S f X) x H T := by
  let a : ℕ → ℂ := dyadicRestrictedCoefficient S f X
  let P : ℕ → ℂ := fun y ↦ dirichletPerronIntegral a y 1 T
  let R : ℕ → ℂ := fun y ↦ dirichletPerronStarredSum a y - P y
  have hxH : 0 < x + H := by omega
  have hsum : LSeriesSummable a (1 : ℂ) :=
    dyadicRestrictedCoefficient_LSeriesSummable S f X 1
  have herrX := norm_dirichletPerronStarredSum_sub_integral_le
    hsum hx (by norm_num) (by norm_num) hT
  have herrXH := norm_dirichletPerronStarredSum_sub_integral_le
    hsum hxH (by norm_num) (by norm_num) hT
  have hmodel := dyadicRestrictedPerron_shortDifference_eq S f X
    (show (0 : ℝ) < x by exact_mod_cast hx)
    (show (0 : ℝ) < H by exact_mod_cast hH) T
  have hsumEq := sum_Ioc_eq_starred_shortDifference_add_endpoints a (H := H) hx
  change ‖((∑ n ∈ Finset.Ioc x (x + H), a n) / (H : ℂ)) - _‖ ≤ _
  rw [← hmodel]
  rw [hsumEq]
  rw [← Nat.cast_add]
  norm_num only [Complex.ofReal_natCast]
  change ‖(dirichletPerronStarredSum a (x + H) -
        dirichletPerronStarredSum a x +
          (1 / 2 : ℂ) * (a (x + H) - a x)) / (H : ℂ) -
      (P (x + H) - P x) / (H : ℂ)‖ ≤ _
  have hid :
      (dirichletPerronStarredSum a (x + H) -
          dirichletPerronStarredSum a x +
            (1 / 2 : ℂ) * (a (x + H) - a x)) / (H : ℂ) -
        (P (x + H) - P x) / (H : ℂ) =
      (R (x + H) - R x + (1 / 2 : ℂ) * (a (x + H) - a x)) /
        (H : ℂ) := by
    dsimp [R, P]
    ring
  rw [hid]
  rw [norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ H)
  calc
    ‖R (x + H) - R x + (1 / 2 : ℂ) * (a (x + H) - a x)‖ ≤
        ‖R (x + H)‖ + ‖R x‖ +
          (1 / 2 : ℝ) * (‖a (x + H)‖ + ‖a x‖) := by
      calc
        _ ≤ ‖R (x + H) - R x‖ +
            ‖(1 / 2 : ℂ) * (a (x + H) - a x)‖ := norm_add_le _ _
        _ ≤ (‖R (x + H)‖ + ‖R x‖) +
            (1 / 2 : ℝ) * (‖a (x + H)‖ + ‖a x‖) := by
          gcongr
          · exact norm_sub_le _ _
          · rw [norm_mul]
            norm_num
            exact norm_sub_le _ _
        _ = _ := by ring
    _ ≤ MRHalaszPerron.perronTruncationError a (x + H) 1 T +
          MRHalaszPerron.perronTruncationError a x 1 T +
          (1 / 2 : ℝ) * (‖a (x + H)‖ + ‖a x‖) := by
      dsimp [R, P]
      unfold MRHalaszPerron.perronTruncationError
      exact add_le_add (add_le_add herrXH herrX) le_rfl
    _ = _ := by rfl

/-- Endpoint-corrected version of the pointwise Perron approximation.  Its
right side is a pure truncation error and therefore tends to zero. -/
theorem norm_dyadicShortAverage_sub_correctedPerron_le_truncationError
    (S : Finset ℕ) (f : ℕ → ℂ) (X : ℕ)
    {x H : ℕ} (hx : 0 < x) (hH : 0 < H) {T : ℝ} (hT : 0 < T) :
    ‖dyadicRestrictedShortAverage S f X x H -
        dyadicRestrictedCorrectedPerronAverage S f X x H T‖ ≤
      lemma14PerronTruncationError
        (dyadicRestrictedCoefficient S f X) x H T := by
  let a : ℕ → ℂ := dyadicRestrictedCoefficient S f X
  let P : ℕ → ℂ := fun y ↦ dirichletPerronIntegral a y 1 T
  let R : ℕ → ℂ := fun y ↦ dirichletPerronStarredSum a y - P y
  have hxH : 0 < x + H := by omega
  have hsum : LSeriesSummable a (1 : ℂ) :=
    dyadicRestrictedCoefficient_LSeriesSummable S f X 1
  have herrX := norm_dirichletPerronStarredSum_sub_integral_le
    hsum hx (by norm_num) (by norm_num) hT
  have herrXH := norm_dirichletPerronStarredSum_sub_integral_le
    hsum hxH (by norm_num) (by norm_num) hT
  have hmodel := dyadicRestrictedPerron_shortDifference_eq S f X
    (show (0 : ℝ) < x by exact_mod_cast hx)
    (show (0 : ℝ) < H by exact_mod_cast hH) T
  have hsumEq := sum_Ioc_eq_starred_shortDifference_add_endpoints a (H := H) hx
  unfold dyadicRestrictedShortAverage dyadicRestrictedCorrectedPerronAverage
    dyadicRestrictedPerronEndpointCorrection
  change ‖((∑ n ∈ Finset.Ioc x (x + H), a n) / (H : ℂ)) -
      (dyadicRestrictedPerronAverage S f X x H T +
        (1 / 2 : ℂ) * (a (x + H) - a x) / (H : ℂ))‖ ≤ _
  unfold dyadicRestrictedPerronAverage
  rw [← hmodel, hsumEq]
  rw [← Nat.cast_add]
  norm_num only [Complex.ofReal_natCast]
  have hid :
      (dirichletPerronStarredSum a (x + H) -
          dirichletPerronStarredSum a x +
            (1 / 2 : ℂ) * (a (x + H) - a x)) / (H : ℂ) -
        ((P (x + H) - P x) / (H : ℂ) +
          (1 / 2 : ℂ) * (a (x + H) - a x) / (H : ℂ)) =
      (R (x + H) - R x) / (H : ℂ) := by
    dsimp [R, P]
    ring
  rw [hid, norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ H)
  calc
    ‖R (x + H) - R x‖ ≤ ‖R (x + H)‖ + ‖R x‖ := norm_sub_le _ _
    _ ≤ MRHalaszPerron.perronTruncationError a (x + H) 1 T +
          MRHalaszPerron.perronTruncationError a x 1 T := by
      exact add_le_add herrXH herrX
    _ = _ := by rfl

/-- Genuine pointwise two-length Lemma-14 reduction.  The difference of the
two actual normalized short sums is approximated by the difference of the
two Perron-kernel integrals, with the sum of the two completely explicit
truncation/endpoint errors. -/
theorem norm_dyadicRestrictedShortAverage_sub_sub_perron_le
    (S : Finset ℕ) (f : ℕ → ℂ) (X : ℕ)
    {x H₁ H₂ : ℕ} (hx : 0 < x) (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    {T : ℝ} (hT : 0 < T) :
    ‖(dyadicRestrictedShortAverage S f X x H₁ -
          dyadicRestrictedShortAverage S f X x H₂) -
        (dyadicRestrictedPerronAverage S f X x H₁ T -
          dyadicRestrictedPerronAverage S f X x H₂ T)‖ ≤
      lemma14PerronEndpointError (dyadicRestrictedCoefficient S f X) x H₁ T +
        lemma14PerronEndpointError (dyadicRestrictedCoefficient S f X) x H₂ T := by
  have h₁ := norm_dyadicShortAverage_sub_perron_le_endpointError
    S f X hx hH₁ hT
  have h₂ := norm_dyadicShortAverage_sub_perron_le_endpointError
    S f X hx hH₂ hT
  change ‖(_ - _) - (_ - _)‖ ≤ _
  calc
    ‖(dyadicRestrictedShortAverage S f X x H₁ -
          dyadicRestrictedShortAverage S f X x H₂ -
        (dyadicRestrictedPerronAverage S f X x H₁ T -
          dyadicRestrictedPerronAverage S f X x H₂ T))‖ =
      ‖(dyadicRestrictedShortAverage S f X x H₁ -
          dyadicRestrictedPerronAverage S f X x H₁ T) -
        (dyadicRestrictedShortAverage S f X x H₂ -
          dyadicRestrictedPerronAverage S f X x H₂ T)‖ := by ring_nf
    _ ≤ ‖dyadicRestrictedShortAverage S f X x H₁ -
          dyadicRestrictedPerronAverage S f X x H₁ T‖ +
        ‖dyadicRestrictedShortAverage S f X x H₂ -
          dyadicRestrictedPerronAverage S f X x H₂ T‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add h₁ h₂

/-- Discrete dyadic mean square of the difference of two normalized short
sums, matching the left side of source Lemma 14. -/
def dyadicTwoLengthShortMeanSquare
    (S : Finset ℕ) (f : ℕ → ℂ) (X H₁ H₂ : ℕ) : ℝ :=
  ∑ x ∈ Finset.Ioc X (2 * X),
    Complex.normSq
      (dyadicRestrictedShortAverage S f X x H₁ -
        dyadicRestrictedShortAverage S f X x H₂)

/-- The corresponding finite truncated-Perron model mean square. -/
def dyadicTwoLengthPerronMeanSquare
    (S : Finset ℕ) (f : ℕ → ℂ) (X H₁ H₂ : ℕ) (T : ℝ) : ℝ :=
  ∑ x ∈ Finset.Ioc X (2 * X),
    Complex.normSq
      (dyadicRestrictedPerronAverage S f X x H₁ T -
        dyadicRestrictedPerronAverage S f X x H₂ T)

/-- Two-length square mean for the endpoint-corrected Perron models. -/
def dyadicTwoLengthCorrectedPerronMeanSquare
    (S : Finset ℕ) (f : ℕ → ℂ) (X H₁ H₂ : ℕ) (T : ℝ) : ℝ :=
  ∑ x ∈ Finset.Ioc X (2 * X),
    Complex.normSq
      (dyadicRestrictedCorrectedPerronAverage S f X x H₁ T -
        dyadicRestrictedCorrectedPerronAverage S f X x H₂ T)

/-- The square mass of all explicit Perron truncation/endpoint errors over
the dyadic starting points. -/
def dyadicTwoLengthPerronErrorMeanSquare
    (S : Finset ℕ) (f : ℕ → ℂ) (X H₁ H₂ : ℕ) (T : ℝ) : ℝ :=
  ∑ x ∈ Finset.Ioc X (2 * X),
    (lemma14PerronEndpointError (dyadicRestrictedCoefficient S f X) x H₁ T +
      lemma14PerronEndpointError (dyadicRestrictedCoefficient S f X) x H₂ T) ^ 2

/-- The genuinely vanishing square mass of the two-length Perron errors.
Unlike `dyadicTwoLengthPerronErrorMeanSquare`, this has no fixed endpoint
correction because that correction is built into the model. -/
def dyadicTwoLengthPerronTruncationErrorMeanSquare
    (S : Finset ℕ) (f : ℕ → ℂ) (X H₁ H₂ : ℕ) (T : ℝ) : ℝ :=
  ∑ x ∈ Finset.Ioc X (2 * X),
    (lemma14PerronTruncationError
        (dyadicRestrictedCoefficient S f X) x H₁ T +
      lemma14PerronTruncationError
        (dyadicRestrictedCoefficient S f X) x H₂ T) ^ 2

/-- The total corrected two-length truncation error tends to zero.  This is
the finite-set limit needed to replace truncated Perron by the full Perron
integral without ever evaluating a large pointwise error at height `X/2`. -/
theorem tendsto_dyadicTwoLengthPerronTruncationErrorMeanSquare_atTop
    (S : Finset ℕ) (f : ℕ → ℂ) (X H₁ H₂ : ℕ) :
    Filter.Tendsto (fun T : ℝ ↦
        dyadicTwoLengthPerronTruncationErrorMeanSquare S f X H₁ H₂ T)
      Filter.atTop (nhds 0) := by
  unfold dyadicTwoLengthPerronTruncationErrorMeanSquare
  simpa using tendsto_finset_sum (Finset.Ioc X (2 * X)) (fun x hx ↦
    (((tendsto_lemma14PerronTruncationError_atTop
        (dyadicRestrictedCoefficient S f X) x H₁).add
      (tendsto_lemma14PerronTruncationError_atTop
        (dyadicRestrictedCoefficient S f X) x H₂)).pow 2))

/-- Epsilon form of the corrected finite Perron limit. -/
theorem exists_dyadicTwoLengthPerronTruncationErrorMeanSquare_lt
    (S : Finset ℕ) (f : ℕ → ℂ) (X H₁ H₂ : ℕ)
    {e : ℝ} (he : 0 < e) :
    ∃ U₀ : ℝ, ∀ U ≥ U₀,
      dyadicTwoLengthPerronTruncationErrorMeanSquare S f X H₁ H₂ U < e := by
  obtain ⟨U₀, hU₀⟩ := Metric.tendsto_atTop.mp
    (tendsto_dyadicTwoLengthPerronTruncationErrorMeanSquare_atTop
      S f X H₁ H₂) e he
  refine ⟨U₀, fun U hU ↦ ?_⟩
  have hnonneg : 0 ≤
      dyadicTwoLengthPerronTruncationErrorMeanSquare S f X H₁ H₂ U := by
    unfold dyadicTwoLengthPerronTruncationErrorMeanSquare
    exact Finset.sum_nonneg (fun x hx ↦ sq_nonneg _)
  have h := hU₀ U hU
  rwa [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at h

/-- The genuine two-length Perron comparison with a vanishing error. -/
theorem dyadicTwoLengthShortMeanSquare_le_correctedPerron
    (S : Finset ℕ) (f : ℕ → ℂ) {X H₁ H₂ : ℕ}
    (hX : 0 < X) (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    {T : ℝ} (hT : 0 < T) :
    dyadicTwoLengthShortMeanSquare S f X H₁ H₂ ≤
      2 * dyadicTwoLengthCorrectedPerronMeanSquare S f X H₁ H₂ T +
        2 * dyadicTwoLengthPerronTruncationErrorMeanSquare S f X H₁ H₂ T := by
  classical
  unfold dyadicTwoLengthShortMeanSquare
    dyadicTwoLengthCorrectedPerronMeanSquare
    dyadicTwoLengthPerronTruncationErrorMeanSquare
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x hxmem
  have hxpos : 0 < x := by
    rw [Finset.mem_Ioc] at hxmem
    omega
  let A : ℂ := dyadicRestrictedShortAverage S f X x H₁ -
    dyadicRestrictedShortAverage S f X x H₂
  let M : ℂ := dyadicRestrictedCorrectedPerronAverage S f X x H₁ T -
    dyadicRestrictedCorrectedPerronAverage S f X x H₂ T
  let E : ℝ :=
    lemma14PerronTruncationError
        (dyadicRestrictedCoefficient S f X) x H₁ T +
      lemma14PerronTruncationError
        (dyadicRestrictedCoefficient S f X) x H₂ T
  have h₁ := norm_dyadicShortAverage_sub_correctedPerron_le_truncationError
    S f X hxpos hH₁ hT
  have h₂ := norm_dyadicShortAverage_sub_correctedPerron_le_truncationError
    S f X hxpos hH₂ hT
  have happrox : ‖A - M‖ ≤ E := by
    calc
      ‖A - M‖ =
          ‖(dyadicRestrictedShortAverage S f X x H₁ -
              dyadicRestrictedCorrectedPerronAverage S f X x H₁ T) -
            (dyadicRestrictedShortAverage S f X x H₂ -
              dyadicRestrictedCorrectedPerronAverage S f X x H₂ T)‖ := by
            dsimp [A, M]
            congr 1
            ring
      _ ≤ ‖dyadicRestrictedShortAverage S f X x H₁ -
              dyadicRestrictedCorrectedPerronAverage S f X x H₁ T‖ +
            ‖dyadicRestrictedShortAverage S f X x H₂ -
              dyadicRestrictedCorrectedPerronAverage S f X x H₂ T‖ := norm_sub_le _ _
      _ ≤ E := by dsimp [E]; exact add_le_add h₁ h₂
  have hsq : Complex.normSq (A - M) ≤ E ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg (E - ‖A - M‖), norm_nonneg (A - M)]
  have hnormA : ‖A‖ ≤ ‖M‖ + ‖A - M‖ := by
    calc
      ‖A‖ = ‖M + (A - M)‖ := by congr 1; abel
      _ ≤ ‖M‖ + ‖A - M‖ := norm_add_le _ _
  have hbasic : Complex.normSq A ≤
      2 * Complex.normSq M + 2 * Complex.normSq (A - M) := by
    simp only [Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg (‖M‖ - ‖A - M‖), norm_nonneg A,
      norm_nonneg M, norm_nonneg (A - M)]
  exact hbasic.trans (by nlinarith)

/-- Reindex a short sum from increments `j=1,...,H` to its actual integer
interval `(x,x+H]`. -/
theorem sum_Icc_add_eq_sum_Ioc
    (a : ℕ → ℂ) (x H : ℕ) :
    (∑ j ∈ Finset.Icc 1 H, a (x + j)) =
      ∑ n ∈ Finset.Ioc x (x + H), a n := by
  classical
  apply Finset.sum_bij (fun j _ ↦ x + j)
  · intro j hj
    rw [Finset.mem_Icc] at hj
    rw [Finset.mem_Ioc]
    omega
  · intro j₁ hj₁ j₂ hj₂ heq
    omega
  · intro n hn
    rw [Finset.mem_Ioc] at hn
    refine ⟨n - x, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      omega
    · omega
  · intro j hj
    rfl

/-- Single-length normalized short-average mean square. -/
def dyadicRestrictedShortAverageMeanSquare
    (S : Finset ℕ) (f : ℕ → ℂ) (X H : ℕ) : ℝ :=
  ∑ x ∈ Finset.Ioc X (2 * X),
    Complex.normSq (dyadicRestrictedShortAverage S f X x H)

/-- Single-length truncated-Perron mean square. -/
def dyadicRestrictedPerronAverageMeanSquare
    (S : Finset ℕ) (f : ℕ → ℂ) (X H : ℕ) (T : ℝ) : ℝ :=
  ∑ x ∈ Finset.Ioc X (2 * X),
    Complex.normSq (dyadicRestrictedPerronAverage S f X x H T)

/-- Square mass of the explicit single-length Perron errors. -/
def dyadicRestrictedPerronErrorMeanSquare
    (S : Finset ℕ) (f : ℕ → ℂ) (X H : ℕ) (T : ℝ) : ℝ :=
  ∑ x ∈ Finset.Ioc X (2 * X),
    (lemma14PerronEndpointError
      (dyadicRestrictedCoefficient S f X) x H T) ^ 2

/-- Spatially decoupled version: the coefficient is restricted at dyadic
scale `Y`, while starting points still range over `(X,2X]`.  This is needed
for the second `(2X,4X]` member of the exact two-dyadic cover. -/
def dyadicRestrictedShortAverageMeanSquareAt
    (S : Finset ℕ) (f : ℕ → ℂ) (Y X H : ℕ) : ℝ :=
  ∑ x ∈ Finset.Ioc X (2 * X),
    Complex.normSq (dyadicRestrictedShortAverage S f Y x H)

def dyadicRestrictedPerronAverageMeanSquareAt
    (S : Finset ℕ) (f : ℕ → ℂ) (Y X H : ℕ) (T : ℝ) : ℝ :=
  ∑ x ∈ Finset.Ioc X (2 * X),
    Complex.normSq (dyadicRestrictedPerronAverage S f Y x H T)

def dyadicRestrictedPerronErrorMeanSquareAt
    (S : Finset ℕ) (f : ℕ → ℂ) (Y X H : ℕ) (T : ℝ) : ℝ :=
  ∑ x ∈ Finset.Ioc X (2 * X),
    (lemma14PerronEndpointError
      (dyadicRestrictedCoefficient S f Y) x H T) ^ 2

/-- The unnormalized dyadically restricted UMS is exactly `H²` times the
normalized short-average mean square. -/
theorem uncenteredShortIntervalMeanSquare_dyadicRestricted_eq
    (S : Finset ℕ) (f : ℕ → ℂ) (X : ℕ) {H : ℕ} (hH : 0 < H) :
    uncenteredShortIntervalMeanSquare
        (dyadicRestrictedCoefficient S f X) X H =
      (H : ℝ) ^ 2 * dyadicRestrictedShortAverageMeanSquare S f X H := by
  classical
  unfold uncenteredShortIntervalMeanSquare
    dyadicRestrictedShortAverageMeanSquare
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [sum_Icc_add_eq_sum_Ioc]
  unfold dyadicRestrictedShortAverage
  rw [Complex.normSq_div, Complex.normSq_natCast]
  have hHR : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  field_simp

/-- Spatially decoupled form of the exact `H²` normalization identity. -/
theorem uncenteredShortIntervalMeanSquare_dyadicRestricted_eq_at
    (S : Finset ℕ) (f : ℕ → ℂ) (Y X : ℕ) {H : ℕ} (hH : 0 < H) :
    uncenteredShortIntervalMeanSquare
        (dyadicRestrictedCoefficient S f Y) X H =
      (H : ℝ) ^ 2 *
        dyadicRestrictedShortAverageMeanSquareAt S f Y X H := by
  classical
  unfold uncenteredShortIntervalMeanSquare
    dyadicRestrictedShortAverageMeanSquareAt
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [sum_Icc_add_eq_sum_Ioc]
  unfold dyadicRestrictedShortAverage
  rw [Complex.normSq_div, Complex.normSq_natCast]
  have hHR : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  field_simp

/-- Single-length squared Perron approximation. -/
theorem dyadicRestrictedShortAverageMeanSquare_le_perron
    (S : Finset ℕ) (f : ℕ → ℂ) {X H : ℕ}
    (hX : 0 < X) (hH : 0 < H) {T : ℝ} (hT : 0 < T) :
    dyadicRestrictedShortAverageMeanSquare S f X H ≤
      2 * dyadicRestrictedPerronAverageMeanSquare S f X H T +
        2 * dyadicRestrictedPerronErrorMeanSquare S f X H T := by
  classical
  unfold dyadicRestrictedShortAverageMeanSquare
    dyadicRestrictedPerronAverageMeanSquare
    dyadicRestrictedPerronErrorMeanSquare
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x hxmem
  have hxpos : 0 < x := by
    rw [Finset.mem_Ioc] at hxmem
    omega
  let A : ℂ := dyadicRestrictedShortAverage S f X x H
  let M : ℂ := dyadicRestrictedPerronAverage S f X x H T
  let E : ℝ := lemma14PerronEndpointError
    (dyadicRestrictedCoefficient S f X) x H T
  have happrox : ‖A - M‖ ≤ E :=
    norm_dyadicShortAverage_sub_perron_le_endpointError
      S f X hxpos hH hT
  have hsq : Complex.normSq (A - M) ≤ E ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg (E - ‖A - M‖), norm_nonneg (A - M)]
  have hbasic : Complex.normSq A ≤
      2 * Complex.normSq M + 2 * Complex.normSq (A - M) := by
    have hnormA : ‖A‖ ≤ ‖M‖ + ‖A - M‖ := by
      calc
        ‖A‖ = ‖M + (A - M)‖ := by congr 1; abel
        _ ≤ ‖M‖ + ‖A - M‖ := norm_add_le _ _
    simp only [Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg (‖M‖ - ‖A - M‖), norm_nonneg A,
      norm_nonneg M, norm_nonneg (A - M)]
  exact hbasic.trans (by nlinarith)

/-- Spatially decoupled single-length Perron approximation. -/
theorem dyadicRestrictedShortAverageMeanSquareAt_le_perron
    (S : Finset ℕ) (f : ℕ → ℂ) {Y X H : ℕ}
    (_hX : 0 < X) (hH : 0 < H) {T : ℝ} (hT : 0 < T) :
    dyadicRestrictedShortAverageMeanSquareAt S f Y X H ≤
      2 * dyadicRestrictedPerronAverageMeanSquareAt S f Y X H T +
        2 * dyadicRestrictedPerronErrorMeanSquareAt S f Y X H T := by
  classical
  unfold dyadicRestrictedShortAverageMeanSquareAt
    dyadicRestrictedPerronAverageMeanSquareAt
    dyadicRestrictedPerronErrorMeanSquareAt
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x hxmem
  have hxpos : 0 < x := by
    rw [Finset.mem_Ioc] at hxmem
    omega
  let A : ℂ := dyadicRestrictedShortAverage S f Y x H
  let M : ℂ := dyadicRestrictedPerronAverage S f Y x H T
  let E : ℝ := lemma14PerronEndpointError
    (dyadicRestrictedCoefficient S f Y) x H T
  have happrox : ‖A - M‖ ≤ E :=
    norm_dyadicShortAverage_sub_perron_le_endpointError
      S f Y hxpos hH hT
  have hsq : Complex.normSq (A - M) ≤ E ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg (E - ‖A - M‖), norm_nonneg (A - M)]
  have hbasic : Complex.normSq A ≤
      2 * Complex.normSq M + 2 * Complex.normSq (A - M) := by
    have hnormA : ‖A‖ ≤ ‖M‖ + ‖A - M‖ := by
      calc
        ‖A‖ = ‖M + (A - M)‖ := by congr 1; abel
        _ ≤ ‖M‖ + ‖A - M‖ := norm_add_le _ _
    simp only [Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg (‖M‖ - ‖A - M‖), norm_nonneg A,
      norm_nonneg M, norm_nonneg (A - M)]
  exact hbasic.trans (by nlinarith)

/-- Squared and summed finite Lemma-14 Perron reduction.  It reduces the
actual two-length mean square to the kernel-model mean square plus a fully
explicit endpoint-error square mass. -/
theorem dyadicTwoLengthShortMeanSquare_le_perron
    (S : Finset ℕ) (f : ℕ → ℂ) {X H₁ H₂ : ℕ}
    (hX : 0 < X) (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    {T : ℝ} (hT : 0 < T) :
    dyadicTwoLengthShortMeanSquare S f X H₁ H₂ ≤
      2 * dyadicTwoLengthPerronMeanSquare S f X H₁ H₂ T +
        2 * dyadicTwoLengthPerronErrorMeanSquare S f X H₁ H₂ T := by
  classical
  unfold dyadicTwoLengthShortMeanSquare dyadicTwoLengthPerronMeanSquare
    dyadicTwoLengthPerronErrorMeanSquare
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x hxmem
  have hxpos : 0 < x := by
    rw [Finset.mem_Ioc] at hxmem
    omega
  let A : ℂ := dyadicRestrictedShortAverage S f X x H₁ -
    dyadicRestrictedShortAverage S f X x H₂
  let M : ℂ := dyadicRestrictedPerronAverage S f X x H₁ T -
    dyadicRestrictedPerronAverage S f X x H₂ T
  let E : ℝ :=
    lemma14PerronEndpointError (dyadicRestrictedCoefficient S f X) x H₁ T +
      lemma14PerronEndpointError (dyadicRestrictedCoefficient S f X) x H₂ T
  have happrox : ‖A - M‖ ≤ E := by
    exact norm_dyadicRestrictedShortAverage_sub_sub_perron_le
      S f X hxpos hH₁ hH₂ hT
  have hsq : Complex.normSq (A - M) ≤ E ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg (E - ‖A - M‖), norm_nonneg (A - M)]
  have hAM : M + (A - M) = A := by abel
  have hnormA : ‖A‖ ≤ ‖M‖ + ‖A - M‖ := by
    calc
      ‖A‖ = ‖M + (A - M)‖ := congrArg norm hAM.symm
      _ ≤ ‖M‖ + ‖A - M‖ := norm_add_le M (A - M)
  have hbasic : Complex.normSq A ≤
      2 * Complex.normSq M + 2 * Complex.normSq (A - M) := by
    simp only [Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg (‖M‖ - ‖A - M‖), norm_nonneg A,
      norm_nonneg M, norm_nonneg (A - M)]
  calc
    Complex.normSq A ≤
        2 * Complex.normSq M + 2 * Complex.normSq (A - M) := hbasic
    _ ≤ 2 * Complex.normSq M + 2 * E ^ 2 := by nlinarith

/-- Analysis coefficient against one logarithmic/exponential frequency on a
symmetric vertical segment. -/
def finiteFrequencyAnalysisCoefficient
    {ι : Type*} [Fintype ι] (freq : ι → ℝ) (g : ℝ → ℂ) (T : ℝ) (r : ι) : ℂ :=
  ∫ t in -T..T, conj (realExponentialPhase (t * freq r)) * g t

/-- Dual finite mean-square theorem.  This is the logarithmic Plancherel
step needed in Lemma 14: integrating a continuous vertical coefficient
against separated phases and then squaring over the phases costs only the
vertical length plus the inverse separation. -/
theorem sum_normSq_finiteFrequencyAnalysisCoefficient_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (freq : ι → ℝ) (g : ℝ → ℂ) (hg : Continuous g)
    {T δ : ℝ} (hT : 0 ≤ T) (hδ : 0 < δ)
    (hsep : ∀ r s, r ≠ s → δ ≤ |freq r - freq s|) :
    (∑ r, Complex.normSq
      (finiteFrequencyAnalysisCoefficient freq g T r)) ≤
      (2 * T + 2 * Real.pi * δ⁻¹) *
        ∫ t in -T..T, Complex.normSq (g t) := by
  let z : ι → ℂ := finiteFrequencyAnalysisCoefficient freq g T
  let P : ℝ → ℂ := finiteFrequencyPolynomial freq z
  let S : ℝ := ∑ r, Complex.normSq (z r)
  let G : ℝ := ∫ t in -T..T, Complex.normSq (g t)
  let C : ℝ := 2 * T + 2 * Real.pi * δ⁻¹
  change S ≤ C * G
  have hC : 0 < C := by
    dsimp [C]
    have hinv : 0 < δ⁻¹ := inv_pos.mpr hδ
    nlinarith [Real.pi_pos]
  have hP : Continuous P := by
    unfold P finiteFrequencyPolynomial realExponentialPhase
    fun_prop
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg (fun i hi ↦ Complex.normSq_nonneg _)
  have hG : 0 ≤ G := by
    dsimp [G]
    exact intervalIntegral.integral_nonneg (by linarith)
      (fun _ _ ↦ Complex.normSq_nonneg _)
  have hid :
      (∫ t in -T..T, conj (P t) * g t) = (S : ℂ) := by
    unfold P finiteFrequencyPolynomial
    simp only [map_sum, map_mul, Finset.sum_mul]
    rw [intervalIntegral.integral_finsetSum]
    · dsimp only [S]
      push_cast
      apply Finset.sum_congr rfl
      intro r hr
      rw [show (fun x : ℝ ↦
          conj (z r) * conj (realExponentialPhase (x * freq r)) * g x) =
        fun x ↦ conj (z r) *
          (conj (realExponentialPhase (x * freq r)) * g x) by
            funext x; ring]
      rw [intervalIntegral.integral_const_mul]
      change conj (z r) *
          (∫ t in -T..T, conj (realExponentialPhase (t * freq r)) * g t) =
        (Complex.normSq (z r) : ℂ)
      rw [show (∫ t in -T..T,
          conj (realExponentialPhase (t * freq r)) * g t) = z r by rfl]
      rw [Complex.normSq_eq_conj_mul_self]
    · intro r hr
      exact ((continuous_const.mul
        (by unfold realExponentialPhase; fun_prop)).mul hg).intervalIntegrable _ _
  have hSnorm :
      S = ‖∫ t in -T..T, conj (P t) * g t‖ := by
    rw [hid, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS]
  have hfirst :
      S ≤ ∫ t in -T..T, ‖P t‖ * ‖g t‖ := by
    rw [hSnorm]
    simpa only [norm_mul, Complex.norm_conj] using
      (intervalIntegral.norm_integral_le_integral_norm (by linarith : -T ≤ T)
        (f := fun t ↦ conj (P t) * g t))
  have hyoung (t : ℝ) :
      2 * C * (‖P t‖ * ‖g t‖) ≤
        Complex.normSq (P t) + C ^ 2 * Complex.normSq (g t) := by
    simp only [Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg (‖P t‖ - C * ‖g t‖)]
  have hintYoung :
      ∫ t in -T..T, 2 * C * (‖P t‖ * ‖g t‖) ≤
        ∫ t in -T..T,
          Complex.normSq (P t) + C ^ 2 * Complex.normSq (g t) := by
    apply intervalIntegral.integral_mono (by linarith)
    · exact (hP.norm.mul hg.norm).const_mul _ |>.intervalIntegrable _ _
    · exact ((by fun_prop : Continuous fun t ↦ Complex.normSq (P t)).add
          ((by fun_prop : Continuous fun t ↦ Complex.normSq (g t)).const_mul _)).intervalIntegrable _ _
    · exact hyoung
  have hPenergy :
      (∫ t in -T..T, Complex.normSq (P t)) ≤ C * S := by
    have hmean := norm_finiteFrequencyPolynomial_intervalIntegral_le
      freq z hT hδ hsep
    have hcast :
        (((∫ t in -T..T, Complex.normSq (P t)) : ℝ) : ℂ) =
          ∫ t in -T..T, conj (P t) * P t := by
      rw [← intervalIntegral.integral_ofReal]
      apply intervalIntegral.integral_congr
      intro t ht
      exact Complex.normSq_eq_conj_mul_self
    have hnonneg : 0 ≤ ∫ t in -T..T, Complex.normSq (P t) :=
      intervalIntegral.integral_nonneg (by linarith)
        (fun _ _ ↦ Complex.normSq_nonneg _)
    rw [← hcast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hnonneg] at hmean
    simpa only [C, S, Complex.normSq_eq_norm_sq] using hmean
  have hscale :
      2 * C * S ≤
        (∫ t in -T..T, Complex.normSq (P t)) + C ^ 2 * G := by
    calc
      2 * C * S ≤ 2 * C * (∫ t in -T..T, ‖P t‖ * ‖g t‖) :=
        mul_le_mul_of_nonneg_left hfirst (by positivity)
      _ = ∫ t in -T..T, 2 * C * (‖P t‖ * ‖g t‖) := by
        rw [intervalIntegral.integral_const_mul]
      _ ≤ ∫ t in -T..T,
          Complex.normSq (P t) + C ^ 2 * Complex.normSq (g t) := hintYoung
      _ = (∫ t in -T..T, Complex.normSq (P t)) + C ^ 2 * G := by
        rw [intervalIntegral.integral_add]
        · rw [intervalIntegral.integral_const_mul]
        · exact (by fun_prop : Continuous fun t ↦ Complex.normSq (P t)).intervalIntegrable _ _
        · exact (by fun_prop : Continuous fun t ↦ C ^ 2 * Complex.normSq (g t)).intervalIntegrable _ _
  nlinarith

/-- Integer-logarithm specialization of the dual mean-square theorem.  For
starting points at most `N`, the inverse logarithmic spacing is at most `N`.
In particular this remains effective on every vertical segment of height at
most the ambient dyadic scale. -/
theorem sum_normSq_finiteLogAnalysisCoefficient_le
    {D : Finset ℕ} {N : ℕ} (hN : 0 < N)
    (hDpos : ∀ n ∈ D, 0 < n) (hDN : ∀ n ∈ D, n ≤ N)
    (g : ℝ → ℂ) (hg : Continuous g) {T : ℝ} (hT : 0 ≤ T) :
    (∑ n : ↑D, Complex.normSq
      (finiteFrequencyAnalysisCoefficient
        (fun m : ↑D ↦ Real.log m.1) g T n)) ≤
      (2 * T + 2 * Real.pi * N) *
        ∫ t in -T..T, Complex.normSq (g t) := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hδ : (0 : ℝ) < (N : ℝ)⁻¹ := inv_pos.mpr hNreal
  have hsep : ∀ r s : ↑D, r ≠ s →
      (N : ℝ)⁻¹ ≤ |Real.log r.1 - Real.log s.1| := by
    intro r s hrs
    apply inv_nat_le_abs_log_sub_log
    · exact hDpos r.1 r.2
    · exact hDpos s.1 s.2
    · exact hDN r.1 r.2
    · exact hDN s.1 s.2
    · intro h
      exact hrs (Subtype.ext h)
  simpa only [inv_inv] using
    (sum_normSq_finiteFrequencyAnalysisCoefficient_le
      (fun m : ↑D ↦ Real.log m.1) g hg hT hδ hsep)

/-- Analysis coefficient on an arbitrary finite vertical interval. -/
def finiteFrequencyAnalysisCoefficientOn
    {ι : Type*} [Fintype ι] (freq : ι → ℝ) (g : ℝ → ℂ)
    (A B : ℝ) (r : ι) : ℂ :=
  ∫ t in A..B, conj (realExponentialPhase (t * freq r)) * g t

/-- Arbitrary-interval form of dual logarithmic Plancherel.  This is the
form applied separately to each positive and negative dyadic shell. -/
theorem sum_normSq_finiteFrequencyAnalysisCoefficientOn_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (freq : ι → ℝ) (g : ℝ → ℂ) (hg : Continuous g)
    {A B δ : ℝ} (hAB : A ≤ B) (hδ : 0 < δ)
    (hsep : ∀ r s, r ≠ s → δ ≤ |freq r - freq s|) :
    (∑ r, Complex.normSq
      (finiteFrequencyAnalysisCoefficientOn freq g A B r)) ≤
      (B - A + 2 * Real.pi * δ⁻¹) *
        ∫ t in A..B, Complex.normSq (g t) := by
  let R : ℝ := (B - A) / 2
  let c : ℝ := (A + B) / 2
  let g' : ℝ → ℂ := fun u ↦ g (u + c)
  have hR : 0 ≤ R := by dsimp [R]; linarith
  have hg' : Continuous g' := by unfold g'; fun_prop
  have hbase := sum_normSq_finiteFrequencyAnalysisCoefficient_le
    freq g' hg' hR hδ hsep
  have hleft : -R + c = A := by dsimp [R, c]; ring
  have hright : R + c = B := by dsimp [R, c]; ring
  have henergy :
      (∫ u in -R..R, Complex.normSq (g' u)) =
        ∫ t in A..B, Complex.normSq (g t) := by
    unfold g'
    simpa only [hleft, hright] using
      (intervalIntegral.integral_comp_add_right
        (fun t : ℝ ↦ Complex.normSq (g t)) c (a := -R) (b := R))
  have hcoeff (r : ι) :
      finiteFrequencyAnalysisCoefficientOn freq g A B r =
        conj (realExponentialPhase (c * freq r)) *
          finiteFrequencyAnalysisCoefficient freq g' R r := by
    unfold finiteFrequencyAnalysisCoefficientOn finiteFrequencyAnalysisCoefficient g'
    rw [← hleft, ← hright, ← intervalIntegral.integral_comp_add_right]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    change conj (realExponentialPhase ((u + c) * freq r)) * g (u + c) =
      conj (realExponentialPhase (c * freq r)) *
        (conj (realExponentialPhase (u * freq r)) * g (u + c))
    have heq : (u + c) * freq r = u * freq r + c * freq r := by ring
    rw [heq, ← realExponentialPhase_mul, map_mul]
    ring
  have hnorm (r : ι) :
      Complex.normSq (finiteFrequencyAnalysisCoefficientOn freq g A B r) =
        Complex.normSq (finiteFrequencyAnalysisCoefficient freq g' R r) := by
    rw [hcoeff, Complex.normSq_mul]
    have hp : Complex.normSq (conj (realExponentialPhase (c * freq r))) = 1 := by
      rw [Complex.normSq_eq_norm_sq, Complex.norm_conj,
        norm_realExponentialPhase]
      norm_num
    rw [hp, one_mul]
  simp_rw [hnorm] at ⊢
  rw [henergy] at hbase
  have hconst : 2 * R + 2 * Real.pi * δ⁻¹ =
      B - A + 2 * Real.pi * δ⁻¹ := by dsimp [R]; ring
  rw [hconst] at hbase
  exact hbase

/-- One endpoint term after expanding the Perron increment kernel on a
vertical interval. -/
def perronEndpointOn (F : ℝ → ℂ) (y : ℕ) (A B : ℝ) : ℂ :=
  (y : ℂ) * ∫ t in A..B,
    realExponentialPhase (t * Real.log y) *
      (F t / ((1 : ℂ) + (t : ℂ) * Complex.I))

/-- Shellwise logarithmic Plancherel estimate for the expanded Perron
endpoint.  The bound is valid on any vertical interval and the only scale
loss is the expected `N² (length + 2πN)` before using `|1+it|⁻²` on a
high-frequency shell. -/
theorem sum_normSq_perronEndpointOn_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ℝ → ℂ) (hF : Continuous F) (y : ι → ℕ) {N : ℕ}
    (hN : 0 < N) (hypos : ∀ i, 0 < y i) (hyN : ∀ i, y i ≤ N)
    (hyinj : Function.Injective y) {A B : ℝ} (hAB : A ≤ B) :
    (∑ i, Complex.normSq (perronEndpointOn F (y i) A B)) ≤
      (N : ℝ) ^ 2 * (B - A + 2 * Real.pi * N) *
        ∫ t in A..B,
          Complex.normSq (F t / ((1 : ℂ) + (t : ℂ) * Complex.I)) := by
  let g : ℝ → ℂ := fun t ↦ F t / ((1 : ℂ) + (t : ℂ) * Complex.I)
  let freq : ι → ℝ := fun i ↦ -Real.log (y i)
  have hg : Continuous g := by
    unfold g
    apply hF.div
    · fun_prop
    · intro t ht
      have hre := congrArg Complex.re ht
      norm_num at hre
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hδ : (0 : ℝ) < (N : ℝ)⁻¹ := inv_pos.mpr hNreal
  have hsep : ∀ r s, r ≠ s →
      (N : ℝ)⁻¹ ≤ |freq r - freq s| := by
    intro r s hrs
    have hys : y r ≠ y s := fun h ↦ hrs (hyinj h)
    have h := inv_nat_le_abs_log_sub_log
      (hypos r) (hypos s) (hyN r) (hyN s) hys
    dsimp [freq]
    rw [show -Real.log (y r) - -Real.log (y s) =
      -(Real.log (y r) - Real.log (y s)) by ring, abs_neg]
    exact h
  have hbase := sum_normSq_finiteFrequencyAnalysisCoefficientOn_le
    freq g hg hAB hδ hsep
  have hcoeff (i : ι) :
      finiteFrequencyAnalysisCoefficientOn freq g A B i =
        ∫ t in A..B, realExponentialPhase (t * Real.log (y i)) * g t := by
    apply intervalIntegral.integral_congr
    intro t ht
    unfold freq
    change conj (realExponentialPhase (t * -Real.log (y i))) * g t =
      realExponentialPhase (t * Real.log (y i)) * g t
    rw [conj_realExponentialPhase]
    congr 2
    ring
  have hterm (i : ι) :
      Complex.normSq (perronEndpointOn F (y i) A B) ≤
        (N : ℝ) ^ 2 * Complex.normSq
          (finiteFrequencyAnalysisCoefficientOn freq g A B i) := by
    unfold perronEndpointOn
    rw [← hcoeff]
    rw [Complex.normSq_mul, Complex.normSq_natCast]
    have hyR : (y i : ℝ) ≤ N := by exact_mod_cast hyN i
    have hysq : (y i : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
      nlinarith [show (0 : ℝ) ≤ y i by positivity]
    exact mul_le_mul_of_nonneg_right (by simpa [pow_two] using hysq)
      (Complex.normSq_nonneg _)
  calc
    (∑ i, Complex.normSq (perronEndpointOn F (y i) A B)) ≤
        ∑ i, (N : ℝ) ^ 2 * Complex.normSq
          (finiteFrequencyAnalysisCoefficientOn freq g A B i) :=
      Finset.sum_le_sum (fun i hi ↦ hterm i)
    _ = (N : ℝ) ^ 2 * ∑ i, Complex.normSq
          (finiteFrequencyAnalysisCoefficientOn freq g A B i) := by
      rw [Finset.mul_sum]
    _ ≤ (N : ℝ) ^ 2 *
        ((B - A + 2 * Real.pi * (N : ℝ)) * ∫ t in A..B, Complex.normSq (g t)) :=
      mul_le_mul_of_nonneg_left (by simpa only [inv_inv] using hbase) (sq_nonneg _)
    _ = _ := by
      dsimp [g]
      ring

/-- On a high-frequency interval `|t| ≥ T`, the Perron divisor contributes
the expected factor `T⁻²` to vertical energy. -/
theorem integral_normSq_div_perronLine_le
    (F : ℝ → ℂ) (hF : Continuous F) {A B T : ℝ}
    (hAB : A ≤ B) (hT : 0 < T)
    (haway : ∀ t ∈ Set.Icc A B, T ≤ |t|) :
    (∫ t in A..B,
      Complex.normSq (F t / ((1 : ℂ) + (t : ℂ) * Complex.I))) ≤
      (T ^ 2)⁻¹ * ∫ t in A..B, Complex.normSq (F t) := by
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc A B) :
      Complex.normSq (F t / ((1 : ℂ) + (t : ℂ) * Complex.I)) ≤
        (T ^ 2)⁻¹ * Complex.normSq (F t) := by
    rw [Complex.normSq_div]
    have hs : Complex.normSq ((1 : ℂ) + (t : ℂ) * Complex.I) = 1 + t ^ 2 := by
      simp [Complex.normSq_apply]
      ring
    rw [hs]
    have ht2 : T ^ 2 ≤ t ^ 2 := by
      nlinarith [haway t ht, abs_nonneg t, sq_abs t]
    have hden : T ^ 2 ≤ 1 + t ^ 2 := by linarith
    have hT2 : 0 < T ^ 2 := sq_pos_of_pos hT
    have hdiv := div_le_div_of_nonneg_left
      (Complex.normSq_nonneg (F t)) hT2 hden
    simpa [div_eq_mul_inv, mul_comm] using hdiv
  have hsne (t : ℝ) : (1 : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro ht
    have hre := congrArg Complex.re ht
    norm_num at hre
  have hquot : Continuous (fun t ↦
      F t / ((1 : ℂ) + (t : ℂ) * Complex.I)) := by
    apply hF.div
    · fun_prop
    · exact hsne
  calc
    _ ≤ ∫ t in A..B, (T ^ 2)⁻¹ * Complex.normSq (F t) := by
      apply intervalIntegral.integral_mono_on hAB
      · exact (by
          have : Continuous fun t ↦
              Complex.normSq (F t / ((1 : ℂ) + (t : ℂ) * Complex.I)) := by
            rw [show (fun t ↦
                Complex.normSq (F t / ((1 : ℂ) + (t : ℂ) * Complex.I))) =
              fun t ↦ ‖F t / ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 by
                funext t; rw [Complex.normSq_eq_norm_sq]]
            exact hquot.norm.pow 2
          exact this.intervalIntegrable _ _)
      · exact (by fun_prop : Continuous fun t ↦
          (T ^ 2)⁻¹ * Complex.normSq (F t)).intervalIntegrable _ _
      · exact hpoint
    _ = _ := by rw [intervalIntegral.integral_const_mul]

/-- On every vertical interval, the Perron divisor has norm at least one,
so deleting it can only increase the `L²` energy. -/
theorem integral_normSq_div_perronLine_le_one
    (F : ℝ → ℂ) (hF : Continuous F) {A B : ℝ} (hAB : A ≤ B) :
    (∫ t in A..B,
      Complex.normSq (F t / ((1 : ℂ) + (t : ℂ) * Complex.I))) ≤
      ∫ t in A..B, Complex.normSq (F t) := by
  have hsne (t : ℝ) : (1 : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro ht
    have hre := congrArg Complex.re ht
    norm_num at hre
  have hquot : Continuous (fun t ↦
      F t / ((1 : ℂ) + (t : ℂ) * Complex.I)) := by
    apply hF.div
    · fun_prop
    · exact hsne
  apply intervalIntegral.integral_mono_on hAB
  · exact (by
      have : Continuous fun t ↦
          Complex.normSq (F t / ((1 : ℂ) + (t : ℂ) * Complex.I)) := by
        rw [show (fun t ↦
            Complex.normSq (F t / ((1 : ℂ) + (t : ℂ) * Complex.I))) =
          fun t ↦ ‖F t / ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 by
            funext t; rw [Complex.normSq_eq_norm_sq]]
        exact hquot.norm.pow 2
      exact this.intervalIntegrable _ _)
  · exact (by fun_prop : Continuous fun t ↦
      Complex.normSq (F t)).intervalIntegrable _ _
  · intro t ht
    rw [Complex.normSq_div]
    have hs : Complex.normSq ((1 : ℂ) + (t : ℂ) * Complex.I) = 1 + t ^ 2 := by
      simp [Complex.normSq_apply]
      ring
    rw [hs]
    exact div_le_self (Complex.normSq_nonneg (F t)) (by nlinarith [sq_nonneg t])

/-- High-frequency shell form of the endpoint estimate, with the Perron
divisor already converted into an explicit `T⁻²` factor. -/
theorem sum_normSq_perronEndpointOn_high_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ℝ → ℂ) (hF : Continuous F) (y : ι → ℕ) {N : ℕ}
    (hN : 0 < N) (hypos : ∀ i, 0 < y i) (hyN : ∀ i, y i ≤ N)
    (hyinj : Function.Injective y) {A B T : ℝ}
    (hAB : A ≤ B) (hT : 0 < T)
    (haway : ∀ t ∈ Set.Icc A B, T ≤ |t|) :
    (∑ i, Complex.normSq (perronEndpointOn F (y i) A B)) ≤
      (N : ℝ) ^ 2 * (B - A + 2 * Real.pi * N) * (T ^ 2)⁻¹ *
        ∫ t in A..B, Complex.normSq (F t) := by
  have hend := sum_normSq_perronEndpointOn_le
    F hF y hN hypos hyN hyinj hAB
  have hdiv := integral_normSq_div_perronLine_le F hF hAB hT haway
  have hcoef : 0 ≤ (N : ℝ) ^ 2 * (B - A + 2 * Real.pi * N) := by
    have : 0 ≤ B - A := sub_nonneg.mpr hAB
    positivity
  calc
    _ ≤ (N : ℝ) ^ 2 * (B - A + 2 * Real.pi * N) *
        ∫ t in A..B,
          Complex.normSq (F t / ((1 : ℂ) + (t : ℂ) * Complex.I)) := hend
    _ ≤ (N : ℝ) ^ 2 * (B - A + 2 * Real.pi * N) *
        ((T ^ 2)⁻¹ * ∫ t in A..B, Complex.normSq (F t)) :=
      mul_le_mul_of_nonneg_left hdiv hcoef
    _ = _ := by ring

/-- The Perron-kernel integral over an arbitrary vertical interval. -/
def perronKernelIntegralOn (F : ℝ → ℂ) (x H : ℕ) (A B : ℝ) : ℂ :=
  ∫ t in A..B, F t * perronIncrementKernel x H t

/-- Exact shellwise endpoint expansion of the Perron increment. -/
theorem perronKernelIntegralOn_eq_endpoint_sub
    (F : ℝ → ℂ) (hF : Continuous F) {x H : ℕ}
    (hx : 0 < x) (hH : 0 < H) (A B : ℝ) :
    perronKernelIntegralOn F x H A B =
      (perronEndpointOn F (x + H) A B - perronEndpointOn F x A B) / (H : ℂ) := by
  let g : ℝ → ℂ := fun t ↦ F t / ((1 : ℂ) + (t : ℂ) * Complex.I)
  let Q : ℕ → ℝ → ℂ := fun y t ↦
    (y : ℂ) * (realExponentialPhase (t * Real.log y) * g t)
  have hsne (t : ℝ) : (1 : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro ht
    have hre := congrArg Complex.re ht
    norm_num at hre
  have hg : Continuous g := by
    unfold g
    apply hF.div
    · fun_prop
    · exact hsne
  have hQ (y : ℕ) : Continuous (Q y) := by
    unfold Q
    fun_prop
  have hend (y : ℕ) :
      perronEndpointOn F y A B = ∫ t in A..B, Q y t := by
    unfold perronEndpointOn Q g
    rw [intervalIntegral.integral_const_mul]
  rw [hend, hend]
  rw [← intervalIntegral.integral_sub ((hQ (x + H)).intervalIntegrable A B)
    ((hQ x).intervalIntegrable A B)]
  rw [← intervalIntegral.integral_div]
  unfold perronKernelIntegralOn
  apply intervalIntegral.integral_congr
  intro t ht
  unfold Q g perronIncrementKernel
  norm_num only [Nat.cast_add, Complex.ofReal_natCast]
  rw [ofReal_cpow_one_add_mul_I_eq_phase (by exact_mod_cast (show 0 < x + H by omega)),
    nat_cpow_one_add_mul_I_eq_phase hx]
  push_cast
  field_simp

/-- Continuity of the finite Perron kernel integrand for positive integral
endpoints. -/
theorem continuous_mul_perronIncrementKernel_nat
    (F : ℝ → ℂ) (hF : Continuous F) {x H : ℕ}
    (hx : 0 < x) (hH : 0 < H) :
    Continuous (fun t ↦ F t * perronIncrementKernel x H t) := by
  unfold perronIncrementKernel
  apply hF.mul
  apply Continuous.div
  · have he : Continuous (fun t : ℝ ↦ (1 : ℂ) + (t : ℂ) * Complex.I) := by
      fun_prop
    have hxHc : ((x + H : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (show 0 < x + H by omega).ne'
    have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    convert (he.const_cpow (Or.inl hxHc)).sub
      (he.const_cpow (Or.inl hxc)) using 1
    ext t
    norm_num [Nat.cast_add]
  · fun_prop
  · intro t ht
    rcases mul_eq_zero.mp ht with hcast | hline
    · have hHc : (H : ℂ) ≠ 0 := by exact_mod_cast hH.ne'
      exact hHc hcast
    · have hre := congrArg Complex.re hline
      norm_num at hre

/-- Elementary Hilbert-space square bound used when the two Perron
endpoints are separated. -/
theorem normSq_sub_le_two_mul_add (z w : ℂ) :
    Complex.normSq (z - w) ≤
      2 * (Complex.normSq z + Complex.normSq w) := by
  simp only [Complex.normSq_eq_norm_sq]
  have hnorm : ‖z - w‖ ≤ ‖z‖ + ‖w‖ := norm_sub_le z w
  nlinarith [sq_nonneg (‖z‖ - ‖w‖), norm_nonneg (z - w),
    norm_nonneg z, norm_nonneg w]

/-- The square mean of one vertical piece of the normalized Perron kernel,
over the dyadic set of starting points. -/
def perronKernelMeanSquareOn
    (F : ℝ → ℂ) (X H : ℕ) (A B : ℝ) : ℝ :=
  ∑ x ∈ Finset.Ioc X (2 * X),
    Complex.normSq (perronKernelIntegralOn F x H A B)

/-- Shellwise Perron/Plancherel bound.  Both endpoint families have
logarithmic spacing at least `(2X+H)⁻¹`; after the Perron divisor is used on
`|t| ≥ T`, this gives the explicit `T⁻²` shell decay.  In particular no
vertical height beyond the interval `[A,B]` occurs in the conclusion. -/
theorem perronKernelMeanSquareOn_high_le
    (F : ℝ → ℂ) (hF : Continuous F) {X H : ℕ}
    (hX : 0 < X) (hH : 0 < H) {A B T : ℝ}
    (hAB : A ≤ B) (hT : 0 < T)
    (haway : ∀ t ∈ Set.Icc A B, T ≤ |t|) :
    perronKernelMeanSquareOn F X H A B ≤
      4 * ((2 * X + H : ℕ) : ℝ) ^ 2 *
        (B - A + 2 * Real.pi * (2 * X + H : ℕ)) * (T ^ 2)⁻¹ *
        ((H : ℝ) ^ 2)⁻¹ *
          ∫ t in A..B, Complex.normSq (F t) := by
  classical
  let D : Finset ℕ := Finset.Ioc X (2 * X)
  let N : ℕ := 2 * X + H
  let y₀ : ↥D → ℕ := fun x ↦ x.1
  let y₁ : ↥D → ℕ := fun x ↦ x.1 + H
  let C : ℝ := (N : ℝ) ^ 2 * (B - A + 2 * Real.pi * N) * (T ^ 2)⁻¹
  let E : ℝ := ∫ t in A..B, Complex.normSq (F t)
  have hN : 0 < N := by dsimp [N]; omega
  have hy₀pos : ∀ x, 0 < y₀ x := by
    intro x
    dsimp [y₀, D] at x ⊢
    have hx := Finset.mem_Ioc.mp x.2
    omega
  have hy₁pos : ∀ x, 0 < y₁ x := by
    intro x
    dsimp [y₁]
    omega
  have hy₀N : ∀ x, y₀ x ≤ N := by
    intro x
    dsimp [y₀, N, D] at x ⊢
    have hx := Finset.mem_Ioc.mp x.2
    omega
  have hy₁N : ∀ x, y₁ x ≤ N := by
    intro x
    dsimp [y₁, N, D] at x ⊢
    have hx := Finset.mem_Ioc.mp x.2
    omega
  have hy₀inj : Function.Injective y₀ := by
    intro x y hxy
    apply Subtype.ext
    exact hxy
  have hy₁inj : Function.Injective y₁ := by
    intro x y hxy
    apply Subtype.ext
    dsimp [y₁] at hxy
    omega
  have hend₀ :
      (∑ x : ↥D, Complex.normSq (perronEndpointOn F (y₀ x) A B)) ≤ C * E := by
    simpa only [C, E] using
      (sum_normSq_perronEndpointOn_high_le F hF y₀ hN hy₀pos hy₀N hy₀inj
        hAB hT haway)
  have hend₁ :
      (∑ x : ↥D, Complex.normSq (perronEndpointOn F (y₁ x) A B)) ≤ C * E := by
    simpa only [C, E] using
      (sum_normSq_perronEndpointOn_high_le F hF y₁ hN hy₁pos hy₁N hy₁inj
        hAB hT haway)
  have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
  have hHcomplex : (H : ℂ) ≠ 0 := by exact_mod_cast hH.ne'
  have hpoint (x : ↥D) :
      Complex.normSq (perronKernelIntegralOn F x.1 H A B) ≤
        2 * ((H : ℝ) ^ 2)⁻¹ *
          (Complex.normSq (perronEndpointOn F (y₁ x) A B) +
            Complex.normSq (perronEndpointOn F (y₀ x) A B)) := by
    have hx : 0 < x.1 := hy₀pos x
    rw [perronKernelIntegralOn_eq_endpoint_sub F hF hx hH A B]
    rw [Complex.normSq_div, Complex.normSq_natCast]
    have hsub := normSq_sub_le_two_mul_add
      (perronEndpointOn F (y₁ x) A B)
      (perronEndpointOn F (y₀ x) A B)
    dsimp [y₁, y₀] at hsub ⊢
    calc
      Complex.normSq
          (perronEndpointOn F (x.1 + H) A B - perronEndpointOn F x.1 A B) /
          ((H : ℝ) * H) =
        Complex.normSq
          (perronEndpointOn F (x.1 + H) A B - perronEndpointOn F x.1 A B) *
          ((H : ℝ) ^ 2)⁻¹ := by rw [div_eq_mul_inv, pow_two]
      _ ≤ (2 * (Complex.normSq (perronEndpointOn F (x.1 + H) A B) +
            Complex.normSq (perronEndpointOn F x.1 A B))) *
          ((H : ℝ) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hsub (inv_nonneg.mpr (sq_nonneg _))
      _ = 2 * ((H : ℝ) ^ 2)⁻¹ *
          (Complex.normSq (perronEndpointOn F (x.1 + H) A B) +
            Complex.normSq (perronEndpointOn F x.1 A B)) := by ring
  have hsum :
      (∑ x : ↥D, Complex.normSq (perronKernelIntegralOn F x.1 H A B)) ≤
        4 * ((H : ℝ) ^ 2)⁻¹ * C * E := by
    calc
      _ ≤ ∑ x : ↥D, 2 * ((H : ℝ) ^ 2)⁻¹ *
          (Complex.normSq (perronEndpointOn F (y₁ x) A B) +
            Complex.normSq (perronEndpointOn F (y₀ x) A B)) :=
        Finset.sum_le_sum (fun x _ ↦ hpoint x)
      _ = 2 * ((H : ℝ) ^ 2)⁻¹ *
          ((∑ x : ↥D, Complex.normSq (perronEndpointOn F (y₁ x) A B)) +
            ∑ x : ↥D, Complex.normSq (perronEndpointOn F (y₀ x) A B)) := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ 2 * ((H : ℝ) ^ 2)⁻¹ * (C * E + C * E) := by
        gcongr
      _ = 4 * ((H : ℝ) ^ 2)⁻¹ * C * E := by ring
  unfold perronKernelMeanSquareOn
  rw [← Finset.sum_attach]
  change (∑ x : ↥D, Complex.normSq (perronKernelIntegralOn F x.1 H A B)) ≤ _
  calc
    _ ≤ 4 * ((H : ℝ) ^ 2)⁻¹ * C * E := hsum
    _ = _ := by dsimp [C, E, N]; ring

/-- Central-band companion to `perronKernelMeanSquareOn_high_le`.  Here the
Perron divisor is only bounded by one; thus the low-frequency vertical
energy appears explicitly and no artificial outer height is introduced. -/
theorem perronKernelMeanSquareOn_low_le
    (F : ℝ → ℂ) (hF : Continuous F) {X H : ℕ}
    (hX : 0 < X) (hH : 0 < H) {A B : ℝ} (hAB : A ≤ B) :
    perronKernelMeanSquareOn F X H A B ≤
      4 * ((2 * X + H : ℕ) : ℝ) ^ 2 *
        (B - A + 2 * Real.pi * (2 * X + H : ℕ)) *
        ((H : ℝ) ^ 2)⁻¹ *
          ∫ t in A..B, Complex.normSq (F t) := by
  classical
  let D : Finset ℕ := Finset.Ioc X (2 * X)
  let N : ℕ := 2 * X + H
  let y₀ : ↥D → ℕ := fun x ↦ x.1
  let y₁ : ↥D → ℕ := fun x ↦ x.1 + H
  let C : ℝ := (N : ℝ) ^ 2 * (B - A + 2 * Real.pi * N)
  let E : ℝ := ∫ t in A..B,
    Complex.normSq (F t / ((1 : ℂ) + (t : ℂ) * Complex.I))
  have hN : 0 < N := by dsimp [N]; omega
  have hy₀pos : ∀ x, 0 < y₀ x := by
    intro x
    dsimp [y₀, D] at x ⊢
    have hx := Finset.mem_Ioc.mp x.2
    omega
  have hy₁pos : ∀ x, 0 < y₁ x := by
    intro x
    dsimp [y₁]
    omega
  have hy₀N : ∀ x, y₀ x ≤ N := by
    intro x
    dsimp [y₀, N, D] at x ⊢
    have hx := Finset.mem_Ioc.mp x.2
    omega
  have hy₁N : ∀ x, y₁ x ≤ N := by
    intro x
    dsimp [y₁, N, D] at x ⊢
    have hx := Finset.mem_Ioc.mp x.2
    omega
  have hy₀inj : Function.Injective y₀ := by
    intro x y hxy
    apply Subtype.ext
    exact hxy
  have hy₁inj : Function.Injective y₁ := by
    intro x y hxy
    apply Subtype.ext
    dsimp [y₁] at hxy
    omega
  have hend₀ :
      (∑ x : ↥D, Complex.normSq (perronEndpointOn F (y₀ x) A B)) ≤ C * E := by
    simpa only [C, E] using
      (sum_normSq_perronEndpointOn_le F hF y₀ hN hy₀pos hy₀N hy₀inj hAB)
  have hend₁ :
      (∑ x : ↥D, Complex.normSq (perronEndpointOn F (y₁ x) A B)) ≤ C * E := by
    simpa only [C, E] using
      (sum_normSq_perronEndpointOn_le F hF y₁ hN hy₁pos hy₁N hy₁inj hAB)
  have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
  have hpoint (x : ↥D) :
      Complex.normSq (perronKernelIntegralOn F x.1 H A B) ≤
        2 * ((H : ℝ) ^ 2)⁻¹ *
          (Complex.normSq (perronEndpointOn F (y₁ x) A B) +
            Complex.normSq (perronEndpointOn F (y₀ x) A B)) := by
    have hx : 0 < x.1 := hy₀pos x
    rw [perronKernelIntegralOn_eq_endpoint_sub F hF hx hH A B]
    rw [Complex.normSq_div, Complex.normSq_natCast]
    have hsub := normSq_sub_le_two_mul_add
      (perronEndpointOn F (y₁ x) A B)
      (perronEndpointOn F (y₀ x) A B)
    dsimp [y₁, y₀] at hsub ⊢
    calc
      Complex.normSq
          (perronEndpointOn F (x.1 + H) A B - perronEndpointOn F x.1 A B) /
          ((H : ℝ) * H) =
        Complex.normSq
          (perronEndpointOn F (x.1 + H) A B - perronEndpointOn F x.1 A B) *
          ((H : ℝ) ^ 2)⁻¹ := by rw [div_eq_mul_inv, pow_two]
      _ ≤ (2 * (Complex.normSq (perronEndpointOn F (x.1 + H) A B) +
            Complex.normSq (perronEndpointOn F x.1 A B))) *
          ((H : ℝ) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hsub (inv_nonneg.mpr (sq_nonneg _))
      _ = 2 * ((H : ℝ) ^ 2)⁻¹ *
          (Complex.normSq (perronEndpointOn F (x.1 + H) A B) +
            Complex.normSq (perronEndpointOn F x.1 A B)) := by ring
  have hsum :
      (∑ x : ↥D, Complex.normSq (perronKernelIntegralOn F x.1 H A B)) ≤
        4 * ((H : ℝ) ^ 2)⁻¹ * C * E := by
    calc
      _ ≤ ∑ x : ↥D, 2 * ((H : ℝ) ^ 2)⁻¹ *
          (Complex.normSq (perronEndpointOn F (y₁ x) A B) +
            Complex.normSq (perronEndpointOn F (y₀ x) A B)) :=
        Finset.sum_le_sum (fun x _ ↦ hpoint x)
      _ = 2 * ((H : ℝ) ^ 2)⁻¹ *
          ((∑ x : ↥D, Complex.normSq (perronEndpointOn F (y₁ x) A B)) +
            ∑ x : ↥D, Complex.normSq (perronEndpointOn F (y₀ x) A B)) := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ 2 * ((H : ℝ) ^ 2)⁻¹ * (C * E + C * E) := by
        gcongr
      _ = 4 * ((H : ℝ) ^ 2)⁻¹ * C * E := by ring
  have hE := integral_normSq_div_perronLine_le_one F hF hAB
  have hC : 0 ≤ C := by
    dsimp [C]
    have : 0 ≤ B - A := sub_nonneg.mpr hAB
    positivity
  unfold perronKernelMeanSquareOn
  rw [← Finset.sum_attach]
  change (∑ x : ↥D, Complex.normSq (perronKernelIntegralOn F x.1 H A B)) ≤ _
  calc
    _ ≤ 4 * ((H : ℝ) ^ 2)⁻¹ * C * E := hsum
    _ ≤ 4 * ((H : ℝ) ^ 2)⁻¹ * C *
        (∫ t in A..B, Complex.normSq (F t)) := by
      gcongr
    _ = _ := by dsimp [C, N]; ring

/-- Algebraic form of the source shell weight.  When `X/H ≤ T ≤ X` and
`H ≤ X`, the exact endpoint coefficient is bounded by a constant times
`X² · X/(H T)` (indeed, by the slightly sharper `X²/(H T)` below). -/
theorem perronShellCoefficient_le
    {X H : ℕ} (hX : 0 < X) (hH : 0 < H) (hHX : H ≤ X)
    {T : ℝ} (hT : 0 < T) (hTleX : T ≤ X)
    (hXleHT : (X : ℝ) ≤ (H : ℝ) * T) :
    4 * ((2 * X + H : ℕ) : ℝ) ^ 2 *
        (T + 2 * Real.pi * (2 * X + H : ℕ)) * (T ^ 2)⁻¹ *
        ((H : ℝ) ^ 2)⁻¹ ≤
      36 * (1 + 6 * Real.pi) * (X : ℝ) ^ 2 / ((H : ℝ) * T) := by
  have hx : (0 : ℝ) < X := by exact_mod_cast hX
  have hh : (0 : ℝ) < H := by exact_mod_cast hH
  have hn : ((2 * X + H : ℕ) : ℝ) ≤ 3 * (X : ℝ) := by
    exact_mod_cast (show 2 * X + H ≤ 3 * X by omega)
  have hnsq : ((2 * X + H : ℕ) : ℝ) ^ 2 ≤ 9 * (X : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (((2 * X + H : ℕ) : ℝ) - 3 * X),
      show (0 : ℝ) ≤ (2 * X + H : ℕ) by positivity]
  have hb : T + 2 * Real.pi * ((2 * X + H : ℕ) : ℝ) ≤
      (1 + 6 * Real.pi) * (X : ℝ) := by
    have hp := Real.pi_pos
    nlinarith
  have hq : 0 < (H : ℝ) * T := mul_pos hh hT
  have hratio :
      (X : ℝ) ^ 3 / (((H : ℝ) * T) ^ 2) ≤
        (X : ℝ) ^ 2 / ((H : ℝ) * T) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hq) hq).2
    nlinarith [sq_nonneg (X : ℝ), mul_nonneg (sq_nonneg (X : ℝ))
      (sub_nonneg.mpr hXleHT)]
  have hfactor :
      ((X : ℝ) ^ 3) * (T ^ 2)⁻¹ * (((H : ℝ) ^ 2)⁻¹) =
        (X : ℝ) ^ 3 / (((H : ℝ) * T) ^ 2) := by
    field_simp
  calc
    _ ≤ 4 * (9 * (X : ℝ) ^ 2) *
        ((1 + 6 * Real.pi) * (X : ℝ)) * (T ^ 2)⁻¹ *
          ((H : ℝ) ^ 2)⁻¹ := by
      gcongr
    _ = 36 * (1 + 6 * Real.pi) *
        (((X : ℝ) ^ 3) * (T ^ 2)⁻¹ * (((H : ℝ) ^ 2)⁻¹)) := by ring
    _ ≤ 36 * (1 + 6 * Real.pi) *
        ((X : ℝ) ^ 2 / ((H : ℝ) * T)) := by
      rw [hfactor]
      gcongr
    _ = _ := by ring

/-- Positive dyadic-shell form with the source `X/(HT)` weight.  The
hypothesis `2T ≤ X` records explicitly that every vertical height used is
at most `X`. -/
theorem perronKernelMeanSquareOn_positiveShell_le
    (F : ℝ → ℂ) (hF : Continuous F) {X H : ℕ}
    (hX : 0 < X) (hH : 0 < H) (hHX : H ≤ X)
    {T : ℝ} (hT : 0 < T) (h2TleX : 2 * T ≤ X)
    (hXleHT : (X : ℝ) ≤ (H : ℝ) * T) :
    perronKernelMeanSquareOn F X H T (2 * T) ≤
      (36 * (1 + 6 * Real.pi) * (X : ℝ) ^ 2 / ((H : ℝ) * T)) *
        ∫ t in T..2 * T, Complex.normSq (F t) := by
  have hbase := perronKernelMeanSquareOn_high_le F hF hX hH
    (A := T) (B := 2 * T) (T := T) (by linarith) hT (by
      intro t ht
      rw [abs_of_nonneg (le_trans hT.le ht.1)]
      exact ht.1)
  have hcoeff := perronShellCoefficient_le hX hH hHX hT
    (show T ≤ (X : ℝ) by linarith) hXleHT
  have henergy : 0 ≤ ∫ t in T..2 * T, Complex.normSq (F t) :=
    intervalIntegral.integral_nonneg (by linarith)
      (fun _ _ ↦ Complex.normSq_nonneg _)
  calc
    _ ≤ 4 * ((2 * X + H : ℕ) : ℝ) ^ 2 *
        (T + 2 * Real.pi * (2 * X + H : ℕ)) * (T ^ 2)⁻¹ *
        ((H : ℝ) ^ 2)⁻¹ *
          ∫ t in T..2 * T, Complex.normSq (F t) := by
      simpa only [show 2 * T - T = T by ring] using hbase
    _ ≤ (36 * (1 + 6 * Real.pi) * (X : ℝ) ^ 2 / ((H : ℝ) * T)) *
        ∫ t in T..2 * T, Complex.normSq (F t) :=
      mul_le_mul_of_nonneg_right hcoeff henergy

/-- Negative dyadic-shell form with the same source weight and the same
explicit height cap. -/
theorem perronKernelMeanSquareOn_negativeShell_le
    (F : ℝ → ℂ) (hF : Continuous F) {X H : ℕ}
    (hX : 0 < X) (hH : 0 < H) (hHX : H ≤ X)
    {T : ℝ} (hT : 0 < T) (h2TleX : 2 * T ≤ X)
    (hXleHT : (X : ℝ) ≤ (H : ℝ) * T) :
    perronKernelMeanSquareOn F X H (-2 * T) (-T) ≤
      (36 * (1 + 6 * Real.pi) * (X : ℝ) ^ 2 / ((H : ℝ) * T)) *
        ∫ t in -2 * T..-T, Complex.normSq (F t) := by
  have hbase := perronKernelMeanSquareOn_high_le F hF hX hH
    (A := -2 * T) (B := -T) (T := T) (by linarith) hT (by
      intro t ht
      rw [abs_of_nonpos (le_trans ht.2 (by linarith))]
      linarith [ht.2])
  have hcoeff := perronShellCoefficient_le hX hH hHX hT
    (show T ≤ (X : ℝ) by linarith) hXleHT
  have henergy : 0 ≤ ∫ t in -2 * T..-T, Complex.normSq (F t) :=
    intervalIntegral.integral_nonneg (by linarith)
      (fun _ _ ↦ Complex.normSq_nonneg _)
  calc
    _ ≤ 4 * ((2 * X + H : ℕ) : ℝ) ^ 2 *
        (T + 2 * Real.pi * (2 * X + H : ℕ)) * (T ^ 2)⁻¹ *
        ((H : ℝ) ^ 2)⁻¹ *
          ∫ t in -2 * T..-T, Complex.normSq (F t) := by
      simpa only [show -T - -2 * T = T by ring] using hbase
    _ ≤ (36 * (1 + 6 * Real.pi) * (X : ℝ) ^ 2 / ((H : ℝ) * T)) *
        ∫ t in -2 * T..-T, Complex.normSq (F t) :=
      mul_le_mul_of_nonneg_right hcoeff henergy

/-- The low Perron segment together with its first `J` positive and negative
dyadic shell integrals. -/
def dyadicPerronKernelIntegral
    (F : ℝ → ℂ) (x H : ℕ) (T : ℝ) (J : ℕ) : ℂ :=
  perronKernelIntegralOn F x H (-T) T +
    ∑ j ∈ Finset.range J,
      (perronKernelIntegralOn F x H
          (-(((2 : ℕ) ^ (j + 1) : ℕ) : ℝ) * T)
          (-(((2 : ℕ) ^ j : ℕ) : ℝ) * T) +
        perronKernelIntegralOn F x H
          ((((2 : ℕ) ^ j : ℕ) : ℝ) * T)
          ((((2 : ℕ) ^ (j + 1) : ℕ) : ℝ) * T))

/-- Exact reconstruction of the symmetric outer Perron integral from its
central band and dyadic shells. -/
theorem dyadicPerronKernelIntegral_eq_outer
    (F : ℝ → ℂ) (hF : Continuous F) {x H : ℕ}
    (hx : 0 < x) (hH : 0 < H) (T : ℝ) (J : ℕ) :
    dyadicPerronKernelIntegral F x H T J =
      perronKernelIntegralOn F x H
        (-((((2 : ℕ) ^ J : ℕ) : ℝ) * T))
        ((((2 : ℕ) ^ J : ℕ) : ℝ) * T) := by
  let G : ℝ → ℂ := fun t ↦ F t * perronIncrementKernel x H t
  have hG : Continuous G := continuous_mul_perronIncrementKernel_nat F hF hx hH
  induction J with
  | zero => simp [dyadicPerronKernelIntegral, perronKernelIntegralOn]
  | succ J ih =>
      rw [dyadicPerronKernelIntegral, Finset.sum_range_succ]
      rw [← add_assoc]
      change dyadicPerronKernelIntegral F x H T J + _ = _
      rw [ih]
      unfold perronKernelIntegralOn
      let A : ℝ := (((2 : ℕ) ^ J : ℕ) : ℝ) * T
      let B : ℝ := (((2 : ℕ) ^ (J + 1) : ℕ) : ℝ) * T
      have hneg : IntervalIntegrable G volume (-B) (-A) := hG.intervalIntegrable _ _
      have hmid : IntervalIntegrable G volume (-A) A := hG.intervalIntegrable _ _
      have hpos : IntervalIntegrable G volume A B := hG.intervalIntegrable _ _
      have hleft := intervalIntegral.integral_add_adjacent_intervals hneg hmid
      have hright := intervalIntegral.integral_add_adjacent_intervals
        (hG.intervalIntegrable (-B) A) hpos
      dsimp [G, A, B] at hleft hright
      simp only [← neg_mul] at hleft hright
      simp only [← neg_mul]
      rw [← add_assoc]
      rw [add_comm
        (∫ t in -(((2 : ℕ) ^ J : ℕ) : ℝ) * T..
                    (((2 : ℕ) ^ J : ℕ) : ℝ) * T,
              F t * perronIncrementKernel x H t)
        (∫ t in -(((2 : ℕ) ^ (J + 1) : ℕ) : ℝ) * T..
                    -(((2 : ℕ) ^ J : ℕ) : ℝ) * T,
              F t * perronIncrementKernel x H t)]
      rw [hleft, hright]

/-- Finite Cauchy--Schwarz in the exact square-norm form used to recombine
the dyadic Perron pieces. -/
theorem normSq_finset_sum_le_card_mul_sum_normSq {ι : Type*}
    (s : Finset ι) (f : ι → ℂ) :
    Complex.normSq (∑ i ∈ s, f i) ≤
      (s.card : ℝ) * ∑ i ∈ s, Complex.normSq (f i) := by
  classical
  rw [Complex.normSq_eq_norm_sq]
  calc
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖) ^ 2 := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    _ = _ := by simp only [Complex.normSq_eq_norm_sq]

/-- Mean-square recombination of the central Perron band and dyadic
shells.  The factor `J` is the explicit finite Cauchy--Schwarz cost; no
limit or unrecorded logarithmic loss is hidden here. -/
theorem perronKernelMeanSquareOn_outer_le_low_add_shells
    (F : ℝ → ℂ) (hF : Continuous F) {X H : ℕ}
    (_hX : 0 < X) (hH : 0 < H) (T : ℝ) (J : ℕ) :
    perronKernelMeanSquareOn F X H
        (-((((2 : ℕ) ^ J : ℕ) : ℝ) * T))
        ((((2 : ℕ) ^ J : ℕ) : ℝ) * T) ≤
      2 * perronKernelMeanSquareOn F X H (-T) T +
        4 * (J : ℝ) *
          ∑ j ∈ Finset.range J,
            (perronKernelMeanSquareOn F X H
                (-(((2 : ℕ) ^ (j + 1) : ℕ) : ℝ) * T)
                (-(((2 : ℕ) ^ j : ℕ) : ℝ) * T) +
              perronKernelMeanSquareOn F X H
                ((((2 : ℕ) ^ j : ℕ) : ℝ) * T)
                ((((2 : ℕ) ^ (j + 1) : ℕ) : ℝ) * T)) := by
  classical
  let D : Finset ℕ := Finset.Ioc X (2 * X)
  let L : ℕ → ℂ := fun x ↦ perronKernelIntegralOn F x H (-T) T
  let A : ℕ → ℕ → ℂ := fun x j ↦ perronKernelIntegralOn F x H
    (-(((2 : ℕ) ^ (j + 1) : ℕ) : ℝ) * T)
    (-(((2 : ℕ) ^ j : ℕ) : ℝ) * T)
  let B : ℕ → ℕ → ℂ := fun x j ↦ perronKernelIntegralOn F x H
    ((((2 : ℕ) ^ j : ℕ) : ℝ) * T)
    ((((2 : ℕ) ^ (j + 1) : ℕ) : ℝ) * T)
  have hpoint (x : ℕ) (hxmem : x ∈ D) :
      Complex.normSq (perronKernelIntegralOn F x H
          (-((((2 : ℕ) ^ J : ℕ) : ℝ) * T))
          ((((2 : ℕ) ^ J : ℕ) : ℝ) * T)) ≤
        2 * Complex.normSq (L x) +
          4 * (J : ℝ) * ∑ j ∈ Finset.range J,
            (Complex.normSq (A x j) + Complex.normSq (B x j)) := by
    have hx : 0 < x := by
      dsimp [D] at hxmem
      have := Finset.mem_Ioc.mp hxmem
      omega
    rw [← dyadicPerronKernelIntegral_eq_outer F hF hx hH T J]
    unfold dyadicPerronKernelIntegral
    change Complex.normSq (L x + ∑ j ∈ Finset.range J, (A x j + B x j)) ≤ _
    have hout := normSq_sub_le_two_mul_add (L x)
      (-(∑ j ∈ Finset.range J, (A x j + B x j)))
    simp only [sub_neg_eq_add, Complex.normSq_neg] at hout
    have hsum := normSq_finset_sum_le_card_mul_sum_normSq
      (Finset.range J) (fun j ↦ A x j + B x j)
    simp only [Finset.card_range] at hsum
    have hpairs :
        (∑ j ∈ Finset.range J, Complex.normSq (A x j + B x j)) ≤
          2 * ∑ j ∈ Finset.range J,
            (Complex.normSq (A x j) + Complex.normSq (B x j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      have h := normSq_sub_le_two_mul_add (A x j) (-B x j)
      simpa only [sub_neg_eq_add, Complex.normSq_neg] using h
    have hsum' := hsum.trans
      (mul_le_mul_of_nonneg_left hpairs (by positivity : (0 : ℝ) ≤ J))
    nlinarith
  unfold perronKernelMeanSquareOn
  change (∑ x ∈ D, Complex.normSq (perronKernelIntegralOn F x H
      (-((((2 : ℕ) ^ J : ℕ) : ℝ) * T))
      ((((2 : ℕ) ^ J : ℕ) : ℝ) * T))) ≤ _
  calc
    _ ≤ ∑ x ∈ D, (2 * Complex.normSq (L x) +
          4 * (J : ℝ) * ∑ j ∈ Finset.range J,
            (Complex.normSq (A x j) + Complex.normSq (B x j))) := by
      exact Finset.sum_le_sum (fun x hx ↦ hpoint x hx)
    _ = 2 * (∑ x ∈ D, Complex.normSq (L x)) +
        4 * (J : ℝ) * ∑ j ∈ Finset.range J,
          ((∑ x ∈ D, Complex.normSq (A x j)) +
            ∑ x ∈ D, Complex.normSq (B x j)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_add_distrib]
    _ = _ := by rfl

/-- Quantitative finite source Lemma 14 for one Perron kernel.  The outer
height is at most `X`; the central energy is displayed separately; and every
dyadic shell has the source weight `X²/(H·2^jT)` (hence, in particular,
`X² · X/(H·2^jT)`). -/
theorem perronKernelMeanSquareOn_outer_le_weightedVerticalEnergy
    (F : ℝ → ℂ) (hF : Continuous F) {X H : ℕ}
    (hX : 0 < X) (hH : 0 < H) (hHX : H ≤ X)
    {T : ℝ} (hT : 0 < T) (J : ℕ)
    (houter : ((((2 : ℕ) ^ J : ℕ) : ℝ) * T) ≤ X)
    (hXleHT : (X : ℝ) ≤ (H : ℝ) * T) :
    perronKernelMeanSquareOn F X H
        (-((((2 : ℕ) ^ J : ℕ) : ℝ) * T))
        ((((2 : ℕ) ^ J : ℕ) : ℝ) * T) ≤
      8 * ((2 * X + H : ℕ) : ℝ) ^ 2 *
          (2 * T + 2 * Real.pi * (2 * X + H : ℕ)) *
          ((H : ℝ) ^ 2)⁻¹ *
            (∫ t in -T..T, Complex.normSq (F t)) +
        4 * (J : ℝ) *
          ∑ j ∈ Finset.range J,
            (36 * (1 + 6 * Real.pi) * (X : ℝ) ^ 2 /
                ((H : ℝ) * ((((2 : ℕ) ^ j : ℕ) : ℝ) * T))) *
              ((∫ t in -(((2 : ℕ) ^ (j + 1) : ℕ) : ℝ) * T..
                    -(((2 : ℕ) ^ j : ℕ) : ℝ) * T,
                    Complex.normSq (F t)) +
                ∫ t in (((2 : ℕ) ^ j : ℕ) : ℝ) * T..
                    (((2 : ℕ) ^ (j + 1) : ℕ) : ℝ) * T,
                    Complex.normSq (F t)) := by
  have hdecomp := perronKernelMeanSquareOn_outer_le_low_add_shells
    F hF hX hH T J
  have hlow := perronKernelMeanSquareOn_low_le F hF hX hH
    (A := -T) (B := T) (by linarith)
  have hlow' :
      2 * perronKernelMeanSquareOn F X H (-T) T ≤
        8 * ((2 * X + H : ℕ) : ℝ) ^ 2 *
          (2 * T + 2 * Real.pi * (2 * X + H : ℕ)) *
          ((H : ℝ) ^ 2)⁻¹ *
            ∫ t in -T..T, Complex.normSq (F t) := by
    have := mul_le_mul_of_nonneg_left hlow (by norm_num : (0 : ℝ) ≤ 2)
    convert this using 1 <;> first | ring | rfl
  have hshell (j : ℕ) (hj : j ∈ Finset.range J) :
      perronKernelMeanSquareOn F X H
          (-(((2 : ℕ) ^ (j + 1) : ℕ) : ℝ) * T)
          (-(((2 : ℕ) ^ j : ℕ) : ℝ) * T) +
        perronKernelMeanSquareOn F X H
          ((((2 : ℕ) ^ j : ℕ) : ℝ) * T)
          ((((2 : ℕ) ^ (j + 1) : ℕ) : ℝ) * T) ≤
        (36 * (1 + 6 * Real.pi) * (X : ℝ) ^ 2 /
            ((H : ℝ) * ((((2 : ℕ) ^ j : ℕ) : ℝ) * T))) *
          ((∫ t in -(((2 : ℕ) ^ (j + 1) : ℕ) : ℝ) * T..
                -(((2 : ℕ) ^ j : ℕ) : ℝ) * T,
                Complex.normSq (F t)) +
            ∫ t in (((2 : ℕ) ^ j : ℕ) : ℝ) * T..
                (((2 : ℕ) ^ (j + 1) : ℕ) : ℝ) * T,
                Complex.normSq (F t)) := by
    let U : ℝ := (((2 : ℕ) ^ j : ℕ) : ℝ) * T
    have hjlt : j < J := Finset.mem_range.mp hj
    have hU : 0 < U := by dsimp [U]; positivity
    have hpownat : (2 : ℕ) ^ (j + 1) ≤ 2 ^ J :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h2UleX : 2 * U ≤ (X : ℝ) := by
      calc
        2 * U = (((2 : ℕ) ^ (j + 1) : ℕ) : ℝ) * T := by
          dsimp [U]
          push_cast
          rw [pow_succ]
          ring
        _ ≤ (((2 : ℕ) ^ J : ℕ) : ℝ) * T := by
          gcongr
        _ ≤ X := houter
    have hTleU : T ≤ U := by
      dsimp [U]
      have hpone : (1 : ℕ) ≤ 2 ^ j := Nat.one_le_pow j 2 (by omega)
      have hponeR : (1 : ℝ) ≤ ((2 : ℕ) ^ j : ℕ) := by exact_mod_cast hpone
      nlinarith [mul_nonneg (sub_nonneg.mpr hponeR) hT.le]
    have hXleHU : (X : ℝ) ≤ (H : ℝ) * U := by
      exact hXleHT.trans
        (mul_le_mul_of_nonneg_left hTleU (by positivity))
    have hneg := perronKernelMeanSquareOn_negativeShell_le
      F hF hX hH hHX hU h2UleX hXleHU
    have hpos := perronKernelMeanSquareOn_positiveShell_le
      F hF hX hH hHX hU h2UleX hXleHU
    have hscale : (((2 : ℕ) ^ (j + 1) : ℕ) : ℝ) * T = 2 * U := by
      dsimp [U]
      push_cast
      rw [pow_succ]
      ring
    simp only [neg_mul]
    rw [hscale]
    rw [show (((2 : ℕ) ^ j : ℕ) : ℝ) * T = U by rfl]
    simp only [neg_mul] at hneg
    calc
      _ ≤ (36 * (1 + 6 * Real.pi) * (X : ℝ) ^ 2 / ((H : ℝ) * U)) *
            (∫ t in -(2 * U)..-U, Complex.normSq (F t)) +
          (36 * (1 + 6 * Real.pi) * (X : ℝ) ^ 2 / ((H : ℝ) * U)) *
            (∫ t in U..2 * U, Complex.normSq (F t)) := add_le_add hneg hpos
      _ = (36 * (1 + 6 * Real.pi) * (X : ℝ) ^ 2 / ((H : ℝ) * U)) *
          ((∫ t in -(2 * U)..-U, Complex.normSq (F t)) +
            ∫ t in U..2 * U, Complex.normSq (F t)) := by ring
  have hshellsum := Finset.sum_le_sum hshell
  have hJnonneg : (0 : ℝ) ≤ 4 * J := by positivity
  calc
    _ ≤ 2 * perronKernelMeanSquareOn F X H (-T) T +
        4 * (J : ℝ) *
          ∑ j ∈ Finset.range J,
            (perronKernelMeanSquareOn F X H
                (-(((2 : ℕ) ^ (j + 1) : ℕ) : ℝ) * T)
                (-(((2 : ℕ) ^ j : ℕ) : ℝ) * T) +
              perronKernelMeanSquareOn F X H
                ((((2 : ℕ) ^ j : ℕ) : ℝ) * T)
                ((((2 : ℕ) ^ (j + 1) : ℕ) : ℝ) * T)) := hdecomp
    _ ≤ _ := add_le_add hlow'
      (mul_le_mul_of_nonneg_left hshellsum hJnonneg)

/-- Named right side of the quantitative Lemma-14 bound.  Keeping this as
a definition lets later Ramaré/projector modules replace each displayed
vertical energy independently while retaining the exact constants. -/
def lemma14WeightedVerticalEnergy
    (F : ℝ → ℂ) (X H : ℕ) (T : ℝ) (J : ℕ) : ℝ :=
  8 * ((2 * X + H : ℕ) : ℝ) ^ 2 *
      (2 * T + 2 * Real.pi * (2 * X + H : ℕ)) *
      ((H : ℝ) ^ 2)⁻¹ *
        (∫ t in -T..T, Complex.normSq (F t)) +
    4 * (J : ℝ) *
      ∑ j ∈ Finset.range J,
        (36 * (1 + 6 * Real.pi) * (X : ℝ) ^ 2 /
            ((H : ℝ) * ((((2 : ℕ) ^ j : ℕ) : ℝ) * T))) *
          ((∫ t in -(((2 : ℕ) ^ (j + 1) : ℕ) : ℝ) * T..
                -(((2 : ℕ) ^ j : ℕ) : ℝ) * T,
                Complex.normSq (F t)) +
            ∫ t in (((2 : ℕ) ^ j : ℕ) : ℝ) * T..
                (((2 : ℕ) ^ (j + 1) : ℕ) : ℝ) * T,
                Complex.normSq (F t))

/-- Compact named form of the quantitative vertical reduction. -/
theorem perronKernelMeanSquareOn_outer_le_lemma14WeightedVerticalEnergy
    (F : ℝ → ℂ) (hF : Continuous F) {X H : ℕ}
    (hX : 0 < X) (hH : 0 < H) (hHX : H ≤ X)
    {T : ℝ} (hT : 0 < T) (J : ℕ)
    (houter : ((((2 : ℕ) ^ J : ℕ) : ℝ) * T) ≤ X)
    (hXleHT : (X : ℝ) ≤ (H : ℝ) * T) :
    perronKernelMeanSquareOn F X H
        (-((((2 : ℕ) ^ J : ℕ) : ℝ) * T))
        ((((2 : ℕ) ^ J : ℕ) : ℝ) * T) ≤
      lemma14WeightedVerticalEnergy F X H T J := by
  exact perronKernelMeanSquareOn_outer_le_weightedVerticalEnergy
    F hF hX hH hHX hT J houter hXleHT

/-- The Perron-average square mean is exactly the kernel square mean times
the Perron normalization `|(2π)⁻¹|²`. -/
theorem dyadicRestrictedPerronAverageMeanSquare_eq_kernel
    (S : Finset ℕ) (f : ℕ → ℂ) (X H : ℕ) (T : ℝ) :
    dyadicRestrictedPerronAverageMeanSquare S f X H T =
      Complex.normSq ((((2 * Real.pi : ℝ) : ℂ)⁻¹)) *
        perronKernelMeanSquareOn
          (dyadicVerticalDirichletPolynomial S f X) X H (-T) T := by
  classical
  unfold dyadicRestrictedPerronAverageMeanSquare perronKernelMeanSquareOn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  unfold dyadicRestrictedPerronAverage perronKernelIntegralOn
  rw [Complex.normSq_mul]

/-- Spatially decoupled kernel identity, used for the `(2X,4X]` cover
piece while retaining the original frequency cap `X`. -/
theorem dyadicRestrictedPerronAverageMeanSquareAt_eq_kernel
    (S : Finset ℕ) (f : ℕ → ℂ) (Y X H : ℕ) (T : ℝ) :
    dyadicRestrictedPerronAverageMeanSquareAt S f Y X H T =
      Complex.normSq ((((2 * Real.pi : ℝ) : ℂ)⁻¹)) *
        perronKernelMeanSquareOn
          (dyadicVerticalDirichletPolynomial S f Y) X H (-T) T := by
  classical
  unfold dyadicRestrictedPerronAverageMeanSquareAt perronKernelMeanSquareOn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  unfold dyadicRestrictedPerronAverage perronKernelIntegralOn
  rw [Complex.normSq_mul]

/-- Source-correct finite Lemma 14 for the actual unnormalized dyadically
restricted short-interval UMS.  The first term is the named low-plus-shell
vertical majorant, all at heights at most `X`; the second is precisely the
explicit Perron truncation/endpoint error square mass. -/
theorem uncenteredShortIntervalMeanSquare_dyadicRestricted_le_lemma14
    (S : Finset ℕ) (f : ℕ → ℂ) {X H : ℕ}
    (hX : 0 < X) (hH : 0 < H) (hHX : H ≤ X)
    {T : ℝ} (hT : 0 < T) (J : ℕ)
    (houter : ((((2 : ℕ) ^ J : ℕ) : ℝ) * T) ≤ X)
    (hXleHT : (X : ℝ) ≤ (H : ℝ) * T) :
    uncenteredShortIntervalMeanSquare
        (dyadicRestrictedCoefficient S f X) X H ≤
      2 * (H : ℝ) ^ 2 *
          Complex.normSq ((((2 * Real.pi : ℝ) : ℂ)⁻¹)) *
          lemma14WeightedVerticalEnergy
            (dyadicVerticalDirichletPolynomial S f X) X H T J +
        2 * (H : ℝ) ^ 2 *
          dyadicRestrictedPerronErrorMeanSquare S f X H
            ((((2 : ℕ) ^ J : ℕ) : ℝ) * T) := by
  let U : ℝ := (((2 : ℕ) ^ J : ℕ) : ℝ) * T
  let F : ℝ → ℂ := dyadicVerticalDirichletPolynomial S f X
  let V : ℝ := lemma14WeightedVerticalEnergy F X H T J
  let E : ℝ := dyadicRestrictedPerronErrorMeanSquare S f X H U
  have hU : 0 < U := by dsimp [U]; positivity
  have havg := dyadicRestrictedShortAverageMeanSquare_le_perron
    S f hX hH hU
  have hkernel : perronKernelMeanSquareOn F X H (-U) U ≤ V := by
    exact perronKernelMeanSquareOn_outer_le_lemma14WeightedVerticalEnergy
      F (continuous_dyadicVerticalDirichletPolynomial S f X)
        hX hH hHX hT J houter hXleHT
  have hmodelEq := dyadicRestrictedPerronAverageMeanSquare_eq_kernel
    S f X H U
  have hnormnonneg :
      0 ≤ Complex.normSq ((((2 * Real.pi : ℝ) : ℂ)⁻¹)) :=
    Complex.normSq_nonneg _
  have hmodel :
      dyadicRestrictedPerronAverageMeanSquare S f X H U ≤
        Complex.normSq ((((2 * Real.pi : ℝ) : ℂ)⁻¹)) * V := by
    rw [hmodelEq]
    exact mul_le_mul_of_nonneg_left hkernel hnormnonneg
  have hHsq : 0 ≤ (H : ℝ) ^ 2 := sq_nonneg _
  rw [uncenteredShortIntervalMeanSquare_dyadicRestricted_eq S f X hH]
  change (H : ℝ) ^ 2 * dyadicRestrictedShortAverageMeanSquare S f X H ≤
    2 * (H : ℝ) ^ 2 *
        Complex.normSq ((((2 * Real.pi : ℝ) : ℂ)⁻¹)) * V +
      2 * (H : ℝ) ^ 2 * E
  calc
    _ ≤ (H : ℝ) ^ 2 *
        (2 * dyadicRestrictedPerronAverageMeanSquare S f X H U + 2 * E) :=
      mul_le_mul_of_nonneg_left havg hHsq
    _ ≤ (H : ℝ) ^ 2 *
        (2 * (Complex.normSq ((((2 * Real.pi : ℝ) : ℂ)⁻¹)) * V) +
          2 * E) := by
      gcongr
    _ = _ := by ring

/-- Spatially decoupled final Lemma-14 consumer.  The restriction scale
`Y` may differ from the starting-point scale `X`; consequently this theorem
applies to both exact cover pieces `Y=X` and `Y=2X`, while every frequency
in the conclusion remains bounded by the original `X`. -/
theorem uncenteredShortIntervalMeanSquare_dyadicRestricted_le_lemma14_at
    (S : Finset ℕ) (f : ℕ → ℂ) {Y X H : ℕ}
    (hX : 0 < X) (hH : 0 < H) (hHX : H ≤ X)
    {T : ℝ} (hT : 0 < T) (J : ℕ)
    (houter : ((((2 : ℕ) ^ J : ℕ) : ℝ) * T) ≤ X)
    (hXleHT : (X : ℝ) ≤ (H : ℝ) * T) :
    uncenteredShortIntervalMeanSquare
        (dyadicRestrictedCoefficient S f Y) X H ≤
      2 * (H : ℝ) ^ 2 *
          Complex.normSq ((((2 * Real.pi : ℝ) : ℂ)⁻¹)) *
          lemma14WeightedVerticalEnergy
            (dyadicVerticalDirichletPolynomial S f Y) X H T J +
        2 * (H : ℝ) ^ 2 *
          dyadicRestrictedPerronErrorMeanSquareAt S f Y X H
            ((((2 : ℕ) ^ J : ℕ) : ℝ) * T) := by
  let U : ℝ := (((2 : ℕ) ^ J : ℕ) : ℝ) * T
  let F : ℝ → ℂ := dyadicVerticalDirichletPolynomial S f Y
  let V : ℝ := lemma14WeightedVerticalEnergy F X H T J
  let E : ℝ := dyadicRestrictedPerronErrorMeanSquareAt S f Y X H U
  have hU : 0 < U := by dsimp [U]; positivity
  have havg := dyadicRestrictedShortAverageMeanSquareAt_le_perron
    S f hX hH hU (Y := Y)
  have hkernel : perronKernelMeanSquareOn F X H (-U) U ≤ V := by
    exact perronKernelMeanSquareOn_outer_le_lemma14WeightedVerticalEnergy
      F (continuous_dyadicVerticalDirichletPolynomial S f Y)
        hX hH hHX hT J houter hXleHT
  have hmodelEq := dyadicRestrictedPerronAverageMeanSquareAt_eq_kernel
    S f Y X H U
  have hnormnonneg :
      0 ≤ Complex.normSq ((((2 * Real.pi : ℝ) : ℂ)⁻¹)) :=
    Complex.normSq_nonneg _
  have hmodel :
      dyadicRestrictedPerronAverageMeanSquareAt S f Y X H U ≤
        Complex.normSq ((((2 * Real.pi : ℝ) : ℂ)⁻¹)) * V := by
    rw [hmodelEq]
    exact mul_le_mul_of_nonneg_left hkernel hnormnonneg
  have hHsq : 0 ≤ (H : ℝ) ^ 2 := sq_nonneg _
  rw [uncenteredShortIntervalMeanSquare_dyadicRestricted_eq_at S f Y X hH]
  change (H : ℝ) ^ 2 *
      dyadicRestrictedShortAverageMeanSquareAt S f Y X H ≤
    2 * (H : ℝ) ^ 2 *
        Complex.normSq ((((2 * Real.pi : ℝ) : ℂ)⁻¹)) * V +
      2 * (H : ℝ) ^ 2 * E
  calc
    _ ≤ (H : ℝ) ^ 2 *
        (2 * dyadicRestrictedPerronAverageMeanSquareAt S f Y X H U +
          2 * E) := mul_le_mul_of_nonneg_left havg hHsq
    _ ≤ (H : ℝ) ^ 2 *
        (2 * (Complex.normSq ((((2 * Real.pi : ℝ) : ℂ)⁻¹)) * V) +
          2 * E) := by
      gcongr
    _ = _ := by ring

/-- The square mass of the coefficients of the vertical polynomial. -/
def weightedDirichletEnergy (D : Finset ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ n ∈ D, ‖a n / (n : ℂ)‖ ^ 2

/-- A sufficiently long symmetric vertical mean square dominates its
coefficient square mass.  This is the finite Montgomery--Vaughan/Parseval
input in the Lemma-14 reduction. -/
theorem mul_weightedDirichletEnergy_le_symmetricVerticalEnergy
    {D : Finset ℕ} {a : ℕ → ℂ} {N : ℕ}
    (hN : 0 < N) (hDpos : ∀ n ∈ D, 0 < n)
    (hDN : ∀ n ∈ D, n ≤ N) {T : ℝ}
    (hT : 2 * Real.pi * N ≤ T) :
    T * weightedDirichletEnergy D a ≤
      symmetricVerticalEnergy
        (fun t ↦ logarithmicDirichletPolynomial D
          (fun n ↦ a n / (n : ℂ)) t) T := by
  classical
  let freq : ↥D → ℝ := fun n ↦ Real.log n.1
  let coeff : ↥D → ℂ := fun n ↦ a n.1 / (n.1 : ℂ)
  let E : ℝ := ∑ n : ↥D, ‖coeff n‖ ^ 2
  let P : ℝ → ℂ := finiteFrequencyPolynomial freq coeff
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hdelta : (0 : ℝ) < (N : ℝ)⁻¹ := inv_pos.mpr hNreal
  have hsep : ∀ r s : ↥D, r ≠ s →
      (N : ℝ)⁻¹ ≤ |freq r - freq s| := by
    intro r s hrs
    have hrsval : r.1 ≠ s.1 := by
      intro h
      apply hrs
      exact Subtype.ext h
    exact inv_nat_le_abs_log_sub_log
      (hDpos r.1 r.2) (hDpos s.1 s.2)
      (hDN r.1 r.2) (hDN s.1 s.2) hrsval
  have hoff := norm_logarithmicKernelOffDiagonal_le
    freq coeff T hdelta hsep
  have hoff' :
      ‖logarithmicKernelOffDiagonal freq coeff T‖ ≤ T * E := by
    apply hoff.trans
    have hEnonneg : 0 ≤ E := by
      dsimp [E]
      positivity
    have hconst : 2 * Real.pi * (N : ℝ) ≤ T := by
      simpa only [Nat.cast_ofNat, Nat.cast_mul] using hT
    have hinv : ((N : ℝ)⁻¹)⁻¹ = (N : ℝ) := inv_inv _
    rw [hinv]
    exact mul_le_mul_of_nonneg_right hconst hEnonneg
  have hexact := finiteFrequencyPolynomial_intervalIntegral_diag_offDiag
    freq coeff T
  have hdiag :
      (∑ r : ↥D, ((2 * T : ℝ) : ℂ) * Complex.normSq (coeff r)) =
        ((2 * T * E : ℝ) : ℂ) := by
    push_cast
    simp only [Complex.normSq_eq_norm_sq]
    rw [← Finset.mul_sum]
    dsimp [E]
    push_cast
    rfl
  have hpoly (t : ℝ) :
      P t = logarithmicDirichletPolynomial D
        (fun n ↦ a n / (n : ℂ)) t := by
    exact finiteFrequencyPolynomial_subtype_eq_logarithmic D
      (fun n ↦ a n / (n : ℂ)) t
  have hcast :
      (((symmetricVerticalEnergy
        (fun t ↦ logarithmicDirichletPolynomial D
          (fun n ↦ a n / (n : ℂ)) t) T : ℝ)) : ℂ) =
        ∫ t in -T..T, conj (P t) * P t := by
    unfold symmetricVerticalEnergy
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro t ht
    change ((Complex.normSq
      (logarithmicDirichletPolynomial D
        (fun n ↦ a n / (n : ℂ)) t) : ℝ) : ℂ) = conj (P t) * P t
    rw [← hpoly t]
    exact Complex.normSq_eq_conj_mul_self
  have hTnonneg : 0 ≤ T := by
    have : 0 < 2 * Real.pi * (N : ℝ) := by positivity
    linarith
  have henergyNonneg :
      0 ≤ symmetricVerticalEnergy
        (fun t ↦ logarithmicDirichletPolynomial D
          (fun n ↦ a n / (n : ℂ)) t) T := by
    unfold symmetricVerticalEnergy
    exact intervalIntegral.integral_nonneg (by linarith)
      (fun _ _ ↦ Complex.normSq_nonneg _)
  have hnormIntegral :
      ‖∫ t in -T..T, conj (P t) * P t‖ =
        symmetricVerticalEnergy
          (fun t ↦ logarithmicDirichletPolynomial D
            (fun n ↦ a n / (n : ℂ)) t) T := by
    rw [← hcast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg henergyNonneg]
  have hdiagBound :
      2 * T * E ≤
        symmetricVerticalEnergy
          (fun t ↦ logarithmicDirichletPolynomial D
            (fun n ↦ a n / (n : ℂ)) t) T + T * E := by
    have htriangle :
        ‖((2 * T * E : ℝ) : ℂ)‖ ≤
          ‖∫ t in -T..T, conj (P t) * P t‖ +
            ‖logarithmicKernelOffDiagonal freq coeff T‖ := by
      change (∫ t in -T..T, conj (P t) * P t) = _ at hexact
      rw [← hdiag]
      calc
        ‖∑ r : ↥D, ((2 * T : ℝ) : ℂ) * Complex.normSq (coeff r)‖ =
            ‖(∫ t in -T..T, conj (P t) * P t) -
              logarithmicKernelOffDiagonal freq coeff T‖ := by
                rw [hexact, add_sub_cancel_right]
        _ ≤ _ := norm_sub_le _ _
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hTnonneg)
        (by dsimp [E]; positivity)), hnormIntegral] at htriangle
    exact htriangle.trans (add_le_add_right hoff' _)
  have hEeq : E = weightedDirichletEnergy D a := by
    dsimp [E, coeff, weightedDirichletEnergy]
    exact Finset.sum_attach D (fun n ↦ ‖a n / (n : ℂ)‖ ^ 2)
  rw [← hEeq]
  linarith

/-- Trivial pointwise bound for the reversed interval kernel. -/
theorem norm_reversedIntervalAdditivePolynomial_le
    (H : ℕ) (α : ℝ) :
    ‖reversedIntervalAdditivePolynomial H α‖ ≤ H := by
  unfold reversedIntervalAdditivePolynomial
  calc
    ‖∑ j ∈ Finset.Icc 1 H, additivePhase α (H - j)‖ ≤
        ∑ j ∈ Finset.Icc 1 H, ‖additivePhase α (H - j)‖ :=
      norm_sum_le _ _
    _ = H := by
      simp only [norm_additivePhase, Finset.sum_const, nsmul_eq_mul, mul_one,
        Nat.card_Icc]
      norm_num

/-- The short-interval square mean of a coefficient supported on one dyadic
block is at most `H²` times its coefficient square mass. -/
theorem uncenteredShortIntervalMeanSquare_dyadicRestricted_le
    (S : Finset ℕ) (f : ℕ → ℂ) (X H : ℕ) :
    uncenteredShortIntervalMeanSquare
        (dyadicRestrictedCoefficient S f X) X H ≤
      (H : ℝ) ^ 2 *
        ∑ n ∈ dyadicRestrictedSupport S X, Complex.normSq (f n) := by
  classical
  let g : ℕ → ℂ := dyadicRestrictedCoefficient S f X
  let A : ℝ → ℂ := ambientAdditivePolynomial g X H
  let K : ℝ → ℂ := reversedIntervalAdditivePolynomial H
  have hbase := uncenteredShortIntervalMeanSquare_le_intervalIntegral_product g X H
  have hAcont : Continuous A := by
    unfold A ambientAdditivePolynomial finiteAdditivePolynomial additivePhase
    fun_prop
  have hKcont : Continuous K := by
    unfold K reversedIntervalAdditivePolynomial additivePhase
    fun_prop
  have hpoint : ∀ α : ℝ,
      Complex.normSq (A α * K α) ≤
        (H : ℝ) ^ 2 * Complex.normSq (A α) := by
    intro α
    rw [Complex.normSq_mul]
    simp only [Complex.normSq_eq_norm_sq]
    have hK := norm_reversedIntervalAdditivePolynomial_le H α
    have hK' : ‖K α‖ ≤ (H : ℝ) := by exact_mod_cast hK
    have hKsq : ‖K α‖ ^ 2 ≤ (H : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hK')
        (add_nonneg (Nat.cast_nonneg H) (norm_nonneg (K α)))]
    calc
      ‖A α‖ ^ 2 * ‖K α‖ ^ 2 ≤ ‖A α‖ ^ 2 * (H : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hKsq (sq_nonneg _)
      _ = (H : ℝ) ^ 2 * ‖A α‖ ^ 2 := mul_comm _ _
  have hint :
      (∫ α in (0 : ℝ)..1, Complex.normSq (A α * K α)) ≤
        ∫ α in (0 : ℝ)..1,
          (H : ℝ) ^ 2 * Complex.normSq (A α) := by
    apply intervalIntegral.integral_mono zero_le_one
    · have hc : Continuous (fun α ↦ Complex.normSq (A α * K α)) := by
        simp only [Complex.normSq_eq_norm_sq]
        fun_prop
      exact hc.intervalIntegrable 0 1
    · have hc : Continuous (fun α ↦
          (H : ℝ) ^ 2 * Complex.normSq (A α)) := by
        simp only [Complex.normSq_eq_norm_sq]
        fun_prop
      exact hc.intervalIntegrable 0 1
    · exact hpoint
  have hparseval :
      (∫ α in (0 : ℝ)..1, Complex.normSq (A α)) =
        ∑ n ∈ Finset.Icc 1 (2 * X + H), Complex.normSq (g n) := by
    exact finiteAdditivePolynomial_intervalIntegral_normSq
      (Finset.Icc 1 (2 * X + H)) g
  have hsum :
      (∑ n ∈ Finset.Icc 1 (2 * X + H), Complex.normSq (g n)) =
        ∑ n ∈ dyadicRestrictedSupport S X, Complex.normSq (f n) := by
    unfold g dyadicRestrictedCoefficient
    rw [show (fun n ↦ Complex.normSq
        (if n ∈ dyadicRestrictedSupport S X then f n else 0)) =
          fun n ↦ if n ∈ dyadicRestrictedSupport S X then
            Complex.normSq (f n) else 0 by
      funext n
      split_ifs <;> simp]
    rw [Finset.sum_ite_mem]
    have hinter :
        Finset.Icc 1 (2 * X + H) ∩ dyadicRestrictedSupport S X =
          dyadicRestrictedSupport S X := by
      apply Finset.inter_eq_right.mpr
      intro n hn
      rw [dyadicRestrictedSupport, Finset.mem_inter, Finset.mem_Ioc] at hn
      rw [Finset.mem_Icc]
      omega
    rw [hinter]
  calc
    uncenteredShortIntervalMeanSquare
        (dyadicRestrictedCoefficient S f X) X H =
        uncenteredShortIntervalMeanSquare g X H := by rfl
    _ ≤ ∫ α in (0 : ℝ)..1, Complex.normSq (A α * K α) := hbase
    _ ≤ ∫ α in (0 : ℝ)..1,
          (H : ℝ) ^ 2 * Complex.normSq (A α) := hint
    _ = (H : ℝ) ^ 2 *
          ∫ α in (0 : ℝ)..1, Complex.normSq (A α) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (H : ℝ) ^ 2 *
          ∑ n ∈ dyadicRestrictedSupport S X, Complex.normSq (f n) := by
      rw [hparseval, hsum]

/-- On `(X,2X]`, removing the `n⁻¹` weight costs at most `(2X)²`. -/
theorem sum_normSq_le_two_mul_sq_weightedDirichletEnergy
    (S : Finset ℕ) (f : ℕ → ℂ) (X : ℕ) :
    (∑ n ∈ dyadicRestrictedSupport S X, Complex.normSq (f n)) ≤
      ((2 * X : ℕ) : ℝ) ^ 2 *
        weightedDirichletEnergy (dyadicRestrictedSupport S X) f := by
  classical
  unfold weightedDirichletEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hnmem := hn
  rw [dyadicRestrictedSupport, Finset.mem_inter, Finset.mem_Ioc] at hnmem
  have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le X) hnmem.1.1
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hfactor : f n = (f n / (n : ℂ)) * (n : ℂ) := by
    field_simp
  have hnleR : (n : ℝ) ≤ 2 * X := by exact_mod_cast hnmem.1.2
  have hnsq : (n : ℝ) ^ 2 ≤ ((2 * X : ℕ) : ℝ) ^ 2 := by
    norm_num [Nat.cast_mul]
    have hgap : 0 ≤ (2 * X : ℝ) - n := sub_nonneg.mpr hnleR
    have hsum : 0 ≤ (2 * X : ℝ) + n := by positivity
    nlinarith [mul_nonneg hgap hsum]
  calc
    Complex.normSq (f n) =
        Complex.normSq ((f n / (n : ℂ)) * (n : ℂ)) :=
      congrArg Complex.normSq hfactor
    _ = Complex.normSq (f n / (n : ℂ)) * Complex.normSq (n : ℂ) := by
      rw [Complex.normSq_mul]
    _ = ‖f n / (n : ℂ)‖ ^ 2 * (n : ℝ) ^ 2 := by
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_natCast]
      ring
    _ ≤ ‖f n / (n : ℂ)‖ ^ 2 * (((2 * X : ℕ) : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hnsq (sq_nonneg _)
    _ = (((2 * X : ℕ) : ℝ) ^ 2) * ‖f n / (n : ℂ)‖ ^ 2 := mul_comm _ _

/-- Reversing the vertical parameter does not change a symmetric `L²`
segment. -/
theorem symmetricVerticalEnergy_dyadicVerticalDirichletPolynomial
    (S : Finset ℕ) (f : ℕ → ℂ) (X : ℕ) (T : ℝ) :
    symmetricVerticalEnergy (dyadicVerticalDirichletPolynomial S f X) T =
      symmetricVerticalEnergy
        (fun t ↦ logarithmicDirichletPolynomial
          (dyadicRestrictedSupport S X)
          (fun n ↦ f n / (n : ℂ)) t) T := by
  unfold symmetricVerticalEnergy dyadicVerticalDirichletPolynomial
  simpa only [neg_neg] using
    (intervalIntegral.integral_comp_neg
      (fun t : ℝ ↦ Complex.normSq
        (logarithmicDirichletPolynomial (dyadicRestrictedSupport S X)
          (fun n ↦ f n / (n : ℂ)) t)) (a := -T) (b := T))

/-- Finite Lemma-14 reduction.  After multiplying by the outer height
`2^J T₀`, the dyadically restricted short-interval second moment is bounded
by the central vertical `L²` segment plus the first `J` positive and negative
dyadic shells of `F(1+it)`.

The right side is definitionally the explicit expression in
`dyadicVerticalEnergy`; no limiting Perron integral or asymptotic notation is
used. -/
theorem outerHeight_mul_uncenteredShortIntervalMeanSquare_le_dyadicVerticalEnergy
    (S : Finset ℕ) (f : ℕ → ℂ) {X : ℕ} (H : ℕ)
    (hX : 0 < X) {T₀ : ℝ} (hT₀ : 0 ≤ T₀) (J : ℕ)
    (hheight : 2 * Real.pi * (2 * X : ℕ) ≤
      (((2 : ℕ) ^ J : ℕ) : ℝ) * T₀) :
    ((((2 : ℕ) ^ J : ℕ) : ℝ) * T₀) *
        uncenteredShortIntervalMeanSquare
          (dyadicRestrictedCoefficient S f X) X H ≤
      (H : ℝ) ^ 2 * (((2 * X : ℕ) : ℝ) ^ 2) *
        dyadicVerticalEnergy
          (dyadicVerticalDirichletPolynomial S f X) T₀ J := by
  let T : ℝ := (((2 : ℕ) ^ J : ℕ) : ℝ) * T₀
  let D : Finset ℕ := dyadicRestrictedSupport S X
  let W : ℝ := weightedDirichletEnergy D f
  let U : ℝ := uncenteredShortIntervalMeanSquare
    (dyadicRestrictedCoefficient S f X) X H
  have hTnonneg : 0 ≤ T := by
    dsimp [T]
    positivity
  have hDpos : ∀ n ∈ D, 0 < n := by
    intro n hn
    dsimp [D] at hn
    rw [dyadicRestrictedSupport, Finset.mem_inter, Finset.mem_Ioc] at hn
    omega
  have hDN : ∀ n ∈ D, n ≤ 2 * X := by
    intro n hn
    dsimp [D] at hn
    exact (Finset.mem_Ioc.mp (Finset.mem_inter.mp hn).1).2
  have hWnonneg : 0 ≤ W := by
    dsimp [W, weightedDirichletEnergy]
    positivity
  have hshort : U ≤ (H : ℝ) ^ 2 *
      ∑ n ∈ D, Complex.normSq (f n) := by
    exact uncenteredShortIntervalMeanSquare_dyadicRestricted_le S f X H
  have hunweight :
      (∑ n ∈ D, Complex.normSq (f n)) ≤
        (((2 * X : ℕ) : ℝ) ^ 2) * W := by
    exact sum_normSq_le_two_mul_sq_weightedDirichletEnergy S f X
  have hmean : T * W ≤
      symmetricVerticalEnergy
        (fun t ↦ logarithmicDirichletPolynomial D
          (fun n ↦ f n / (n : ℂ)) t) T := by
    apply mul_weightedDirichletEnergy_le_symmetricVerticalEnergy
      (D := D) (a := f) (N := 2 * X) (by omega) hDpos hDN
    simpa [T] using hheight
  have houter :
      symmetricVerticalEnergy
          (fun t ↦ logarithmicDirichletPolynomial D
            (fun n ↦ f n / (n : ℂ)) t) T =
        dyadicVerticalEnergy
          (dyadicVerticalDirichletPolynomial S f X) T₀ J := by
    rw [← symmetricVerticalEnergy_dyadicVerticalDirichletPolynomial S f X T]
    rw [dyadicVerticalEnergy_eq_symmetric _
      (continuous_dyadicVerticalDirichletPolynomial S f X) T₀ J]
  have hU : U ≤ (H : ℝ) ^ 2 * (((2 * X : ℕ) : ℝ) ^ 2) * W := by
    calc
      U ≤ (H : ℝ) ^ 2 * ∑ n ∈ D, Complex.normSq (f n) := hshort
      _ ≤ (H : ℝ) ^ 2 * ((((2 * X : ℕ) : ℝ) ^ 2) * W) :=
        mul_le_mul_of_nonneg_left hunweight (sq_nonneg _)
      _ = (H : ℝ) ^ 2 * (((2 * X : ℕ) : ℝ) ^ 2) * W := by ring
  calc
    T * U ≤ T * ((H : ℝ) ^ 2 * (((2 * X : ℕ) : ℝ) ^ 2) * W) :=
      mul_le_mul_of_nonneg_left hU hTnonneg
    _ = (H : ℝ) ^ 2 * (((2 * X : ℕ) : ℝ) ^ 2) * (T * W) := by ring
    _ ≤ (H : ℝ) ^ 2 * (((2 * X : ℕ) : ℝ) ^ 2) *
        symmetricVerticalEnergy
          (fun t ↦ logarithmicDirichletPolynomial D
            (fun n ↦ f n / (n : ℂ)) t) T := by
      exact mul_le_mul_of_nonneg_left hmean
        (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = (H : ℝ) ^ 2 * (((2 * X : ℕ) : ℝ) ^ 2) *
        dyadicVerticalEnergy
          (dyadicVerticalDirichletPolynomial S f X) T₀ J := by rw [houter]

/-- Divided, normalized form of the finite Lemma-14 reduction. -/
theorem uncenteredShortIntervalMeanSquare_le_dyadicVerticalEnergy_div_outerHeight
    (S : Finset ℕ) (f : ℕ → ℂ) {X : ℕ} (H : ℕ)
    (hX : 0 < X) {T₀ : ℝ} (hT₀ : 0 ≤ T₀) (J : ℕ)
    (hheight : 2 * Real.pi * (2 * X : ℕ) ≤
      (((2 : ℕ) ^ J : ℕ) : ℝ) * T₀) :
    uncenteredShortIntervalMeanSquare
        (dyadicRestrictedCoefficient S f X) X H ≤
      ((H : ℝ) ^ 2 * (((2 * X : ℕ) : ℝ) ^ 2) *
        dyadicVerticalEnergy
          (dyadicVerticalDirichletPolynomial S f X) T₀ J) /
            ((((2 : ℕ) ^ J : ℕ) : ℝ) * T₀) := by
  let T : ℝ := (((2 : ℕ) ^ J : ℕ) : ℝ) * T₀
  have hTpos : 0 < T := by
    have hleft : 0 < 2 * Real.pi * (2 * X : ℕ) := by positivity
    exact hleft.trans_le (by simpa [T] using hheight)
  apply (le_div_iff₀ hTpos).2
  rw [mul_comm]
  exact outerHeight_mul_uncenteredShortIntervalMeanSquare_le_dyadicVerticalEnergy
    S f H hX hT₀ J hheight

end

end Erdos67b
