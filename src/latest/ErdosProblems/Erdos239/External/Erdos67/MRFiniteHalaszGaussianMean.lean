import ErdosProblems.Erdos239.External.Erdos67.MRFiniteHalaszBandL2
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# A Gaussian local-pair mean square for finite Halasz polynomials

The uniform-spacing Montgomery--Vaughan estimate loses the largest
frequency in the support.  For the positive prime-band factors in the
finite Halasz argument this is too expensive.  The source proof instead
uses a band-limited majorant, which sees only pairs whose logarithms are
close.  A Gaussian gives an equally useful, and completely explicit,
finite version: after expanding the square, the interaction of two
frequencies is suppressed by

`exp (-(freq r - freq s)^2 / (4 b))`.

Everything in this file is a finite sum.  In particular, the theorem does
not pass from a complete `LSeries` to a finite tail.
-/

open scoped BigOperators ComplexConjugate
open Complex MeasureTheory

namespace Erdos67.MRHalaszBands

noncomputable section

open Erdos67

/-- The positive real Gaussian used to localize a vertical mean square. -/
def finiteHalaszGaussianWeight (b t : ℝ) : ℝ :=
  Real.exp (-b * t ^ 2)

/-- The exponentially localized pair kernel produced by Gaussian Fourier
inversion. -/
def finiteHalaszGaussianPairKernel (b x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2) / (4 * b))

/-- The scalar local-pair majorant for a finite frequency polynomial. -/
def finiteHalaszGaussianPairMajorant
    {ι : Type*} [Fintype ι] (freq : ι → ℝ) (a : ι → ℂ) (b : ℝ) : ℝ :=
  Real.sqrt (Real.pi / b) *
    ∑ r, ∑ s, ‖a r‖ * ‖a s‖ *
      finiteHalaszGaussianPairKernel b (freq s - freq r)

theorem finiteHalaszGaussianWeight_nonneg (b t : ℝ) :
    0 ≤ finiteHalaszGaussianWeight b t := by
  unfold finiteHalaszGaussianWeight
  positivity

theorem finiteHalaszGaussianPairKernel_nonneg (b x : ℝ) :
    0 ≤ finiteHalaszGaussianPairKernel b x := by
  unfold finiteHalaszGaussianPairKernel
  positivity

theorem finiteHalaszGaussianPairKernel_le_one {b : ℝ} (hb : 0 < b) (x : ℝ) :
    finiteHalaszGaussianPairKernel b x ≤ 1 := by
  unfold finiteHalaszGaussianPairKernel
  rw [← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  have hden : 0 ≤ 4 * b := by positivity
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg x)) hden

theorem finiteHalaszGaussianPairMajorant_nonneg
    {ι : Type*} [Fintype ι] (freq : ι → ℝ) (a : ι → ℂ) {b : ℝ}
    (_hb : 0 ≤ b) :
    0 ≤ finiteHalaszGaussianPairMajorant freq a b := by
  unfold finiteHalaszGaussianPairMajorant
  apply mul_nonneg (Real.sqrt_nonneg _)
  apply Finset.sum_nonneg
  intro r hr
  apply Finset.sum_nonneg
  intro s hs
  exact mul_nonneg
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (finiteHalaszGaussianPairKernel_nonneg b _)

/-- The Fourier transform of the real Gaussian in the normalization used
by `finiteFrequencyPolynomial`. -/
theorem integral_realExponentialPhase_mul_gaussian
    {b : ℝ} (hb : 0 < b) (x : ℝ) :
    (∫ t : ℝ, realExponentialPhase (t * x) *
        (finiteHalaszGaussianWeight b t : ℂ)) =
      ((Real.pi / b : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
        Complex.exp ((-(x ^ 2) / (4 * b) : ℝ) : ℂ) := by
  have hbc : 0 < ((b : ℝ) : ℂ).re := by simpa using hb
  have hfourier := fourierIntegral_gaussian hbc (x : ℂ)
  calc
    (∫ t : ℝ, realExponentialPhase (t * x) *
        (finiteHalaszGaussianWeight b t : ℂ)) =
        ∫ t : ℝ, Complex.exp (Complex.I * (x : ℂ) * (t : ℂ)) *
          Complex.exp (-(b : ℂ) * (t : ℂ) ^ 2) := by
      apply integral_congr_ae
      filter_upwards with t
      unfold realExponentialPhase finiteHalaszGaussianWeight
      rw [Complex.ofReal_exp]
      congr 2 <;> push_cast <;> ring
    _ = (Real.pi / (b : ℂ)) ^ (1 / 2 : ℂ) *
        Complex.exp (-(x : ℂ) ^ 2 / (4 * (b : ℂ))) := hfourier
    _ = ((Real.pi / b : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
        Complex.exp ((-(x ^ 2) / (4 * b) : ℝ) : ℂ) := by
      congr 2 <;> push_cast <;> ring

/-- Norm of the explicit Gaussian Fourier factor. -/
theorem norm_gaussianFourierFactor
    {b : ℝ} (hb : 0 < b) (x : ℝ) :
    ‖((Real.pi / b : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
        Complex.exp ((-(x ^ 2) / (4 * b) : ℝ) : ℂ)‖ =
      Real.sqrt (Real.pi / b) *
        finiteHalaszGaussianPairKernel b x := by
  have hquot : 0 < Real.pi / b := div_pos Real.pi_pos hb
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hquot]
  rw [Complex.norm_exp, Complex.ofReal_re]
  rw [Real.sqrt_eq_rpow]
  unfold finiteHalaszGaussianPairKernel
  norm_num

/-- Exact Gaussian-weighted square expansion. -/
theorem integral_conj_finiteFrequencyPolynomial_mul_self_mul_gaussian
    {ι : Type*} [Fintype ι]
    (freq : ι → ℝ) (a : ι → ℂ) {b : ℝ} (hb : 0 < b) :
    (∫ t : ℝ,
        conj (finiteFrequencyPolynomial freq a t) *
          finiteFrequencyPolynomial freq a t *
            (finiteHalaszGaussianWeight b t : ℂ)) =
      ∑ r, ∑ s, conj (a r) * a s *
        (((Real.pi / b : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
          Complex.exp
            ((-((freq s - freq r) ^ 2) / (4 * b) : ℝ) : ℂ)) := by
  simp_rw [conj_finiteFrequencyPolynomial_mul_self, Finset.sum_mul]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro r hr
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro s hs
      rw [show (fun t : ℝ ↦
          conj (a r) * a s * realExponentialPhase (t * (freq s - freq r)) *
            (finiteHalaszGaussianWeight b t : ℂ)) =
          fun t ↦ (conj (a r) * a s) *
            (realExponentialPhase (t * (freq s - freq r)) *
              (finiteHalaszGaussianWeight b t : ℂ)) by
            funext t; ring]
      rw [MeasureTheory.integral_const_mul]
      rw [integral_realExponentialPhase_mul_gaussian hb]
    · intro s hs
      have hi := integrable_cexp_quadratic
        (b := (b : ℂ)) (by simpa using hb)
        (Complex.I * ((freq s - freq r : ℝ) : ℂ)) 0
      have hphase : Integrable (fun t : ℝ ↦
          realExponentialPhase (t * (freq s - freq r)) *
            (finiteHalaszGaussianWeight b t : ℂ)) := by
        apply hi.congr
        filter_upwards with t
        unfold realExponentialPhase finiteHalaszGaussianWeight
        rw [Complex.ofReal_exp, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      simpa only [mul_assoc] using
        hphase.const_mul (conj (a r) * a s)
  · intro r hr
    apply MeasureTheory.integrable_finsetSum Finset.univ
    intro s hs
    have hi := integrable_cexp_quadratic
      (b := (b : ℂ)) (by simpa using hb)
      (Complex.I * ((freq s - freq r : ℝ) : ℂ)) 0
    have hphase : Integrable (fun t : ℝ ↦
        realExponentialPhase (t * (freq s - freq r)) *
          (finiteHalaszGaussianWeight b t : ℂ)) := by
      apply hi.congr
      filter_upwards with t
      unfold realExponentialPhase finiteHalaszGaussianWeight
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    simpa only [mul_assoc] using
      hphase.const_mul (conj (a r) * a s)

/-- Gaussian local-pair mean-square bound.  Unlike the ordinary
Montgomery--Vaughan estimate, its right side retains the exponentially
decaying distance between every pair of frequencies. -/
theorem norm_integral_conj_finiteFrequencyPolynomial_mul_self_mul_gaussian_le
    {ι : Type*} [Fintype ι]
    (freq : ι → ℝ) (a : ι → ℂ) {b : ℝ} (hb : 0 < b) :
    ‖∫ t : ℝ,
        conj (finiteFrequencyPolynomial freq a t) *
          finiteFrequencyPolynomial freq a t *
            (finiteHalaszGaussianWeight b t : ℂ)‖ ≤
      finiteHalaszGaussianPairMajorant freq a b := by
  rw [integral_conj_finiteFrequencyPolynomial_mul_self_mul_gaussian
    freq a hb]
  calc
    ‖∑ r, ∑ s, conj (a r) * a s *
        (((Real.pi / b : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
          Complex.exp
            ((-((freq s - freq r) ^ 2) / (4 * b) : ℝ) : ℂ))‖ ≤
        ∑ r, ∑ s, ‖conj (a r) * a s *
          (((Real.pi / b : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
            Complex.exp
              ((-((freq s - freq r) ^ 2) / (4 * b) : ℝ) : ℂ))‖ := by
      exact norm_sum_le _ _ |>.trans <| Finset.sum_le_sum fun r hr ↦ norm_sum_le _ _
    _ = finiteHalaszGaussianPairMajorant freq a b := by
      unfold finiteHalaszGaussianPairMajorant
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      rw [norm_mul, norm_mul, norm_conj,
        norm_gaussianFourierFactor hb (freq s - freq r)]
      ring

/-- Real-valued form of the Gaussian local-pair mean-square bound. -/
theorem integral_normSq_finiteFrequencyPolynomial_mul_gaussian_le
    {ι : Type*} [Fintype ι]
    (freq : ι → ℝ) (a : ι → ℂ) {b : ℝ} (hb : 0 < b) :
    (∫ t : ℝ, Complex.normSq (finiteFrequencyPolynomial freq a t) *
        finiteHalaszGaussianWeight b t) ≤
      finiteHalaszGaussianPairMajorant freq a b := by
  have hident :
      (((∫ t : ℝ, Complex.normSq (finiteFrequencyPolynomial freq a t) *
          finiteHalaszGaussianWeight b t) : ℝ) : ℂ) =
        ∫ t : ℝ,
          conj (finiteFrequencyPolynomial freq a t) *
            finiteFrequencyPolynomial freq a t *
              (finiteHalaszGaussianWeight b t : ℂ) := by
    calc
      (((∫ t : ℝ, Complex.normSq (finiteFrequencyPolynomial freq a t) *
          finiteHalaszGaussianWeight b t) : ℝ) : ℂ) =
          ∫ t : ℝ,
            ((Complex.normSq (finiteFrequencyPolynomial freq a t) *
              finiteHalaszGaussianWeight b t : ℝ) : ℂ) :=
        integral_ofReal.symm
      _ = ∫ t : ℝ,
          conj (finiteFrequencyPolynomial freq a t) *
            finiteFrequencyPolynomial freq a t *
              (finiteHalaszGaussianWeight b t : ℂ) := by
        apply integral_congr_ae
        filter_upwards with t
        rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
  have hnonneg : 0 ≤
      ∫ t : ℝ, Complex.normSq (finiteFrequencyPolynomial freq a t) *
        finiteHalaszGaussianWeight b t := by
    apply integral_nonneg
    intro t
    exact mul_nonneg (Complex.normSq_nonneg _) (finiteHalaszGaussianWeight_nonneg _ _)
  calc
    (∫ t : ℝ, Complex.normSq (finiteFrequencyPolynomial freq a t) *
        finiteHalaszGaussianWeight b t) =
        ‖(((∫ t : ℝ, Complex.normSq (finiteFrequencyPolynomial freq a t) *
          finiteHalaszGaussianWeight b t) : ℝ) : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    _ = ‖∫ t : ℝ,
          conj (finiteFrequencyPolynomial freq a t) *
            finiteFrequencyPolynomial freq a t *
              (finiteHalaszGaussianWeight b t : ℂ)‖ := by rw [hident]
    _ ≤ finiteHalaszGaussianPairMajorant freq a b :=
      norm_integral_conj_finiteFrequencyPolynomial_mul_self_mul_gaussian_le
        freq a hb

/-- The Gaussian-weighted square of a finite frequency polynomial is
integrable.  This is recorded separately so that the global Gaussian
majorant can be used to dominate sharp interval integrals. -/
theorem integrable_normSq_finiteFrequencyPolynomial_mul_gaussian
    {ι : Type*} [Fintype ι]
    (freq : ι → ℝ) (a : ι → ℂ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun t : ℝ ↦
      Complex.normSq (finiteFrequencyPolynomial freq a t) *
        finiteHalaszGaussianWeight b t) := by
  let B : ℝ := ∑ r, ‖a r‖
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hmajorant : Integrable (fun t : ℝ ↦
      B ^ 2 * finiteHalaszGaussianWeight b t) := by
    exact (integrable_exp_neg_mul_sq hb).const_mul (B ^ 2)
  apply hmajorant.mono
  · have hpoly : Continuous (fun t : ℝ ↦
        finiteFrequencyPolynomial freq a t) := by
      unfold finiteFrequencyPolynomial
      fun_prop
    have hweight : Continuous (finiteHalaszGaussianWeight b) := by
      unfold finiteHalaszGaussianWeight
      fun_prop
    exact ((Complex.continuous_normSq.comp hpoly).mul hweight).aestronglyMeasurable
  · filter_upwards with t
    have hpoly : ‖finiteFrequencyPolynomial freq a t‖ ≤ B := by
      unfold finiteFrequencyPolynomial B
      calc
        ‖∑ r, a r * realExponentialPhase (t * freq r)‖ ≤
            ∑ r, ‖a r * realExponentialPhase (t * freq r)‖ :=
          norm_sum_le _ _
        _ = ∑ r, ‖a r‖ := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [norm_mul, norm_realExponentialPhase, mul_one]
    have hsquare :
        Complex.normSq (finiteFrequencyPolynomial freq a t) ≤ B ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) hpoly 2
    have hweight := finiteHalaszGaussianWeight_nonneg b t
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Complex.normSq_nonneg _) hweight),
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg B) hweight)]
    exact mul_le_mul_of_nonneg_right hsquare hweight

/-- A sharp interval is dominated by the Gaussian local-pair majorant
at spatial scale `T`, with only the universal factor `exp 1`. -/
theorem intervalIntegral_normSq_finiteFrequencyPolynomial_le_gaussianPairMajorant
    {ι : Type*} [Fintype ι]
    (freq : ι → ℝ) (a : ι → ℂ) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, Complex.normSq (finiteFrequencyPolynomial freq a t)) ≤
      Real.exp 1 *
        finiteHalaszGaussianPairMajorant freq a (T⁻¹ ^ 2) := by
  have hb : 0 < T⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr hT)
  let q : ℝ → ℝ := fun t ↦ Complex.normSq (finiteFrequencyPolynomial freq a t)
  let w : ℝ → ℝ := finiteHalaszGaussianWeight (T⁻¹ ^ 2)
  have hq_cont : Continuous q := by
    apply Complex.continuous_normSq.comp
    unfold finiteFrequencyPolynomial
    fun_prop
  have hw_int : Integrable (fun t ↦ q t * w t) := by
    exact integrable_normSq_finiteFrequencyPolynomial_mul_gaussian
      freq a hb
  have hpoint : ∀ t ∈ Set.Icc (-T) T,
      q t ≤ Real.exp 1 * (q t * w t) := by
    intro t ht
    have habs : |t| ≤ T := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    have hsq : t ^ 2 ≤ T ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg t) hT.le).mpr habs
    have hscale : T⁻¹ ^ 2 * t ^ 2 ≤ 1 := by
      have hmul := mul_le_mul_of_nonneg_left hsq (sq_nonneg T⁻¹)
      have hne : T ≠ 0 := ne_of_gt hT
      calc
        T⁻¹ ^ 2 * t ^ 2 ≤ T⁻¹ ^ 2 * T ^ 2 := hmul
        _ = 1 := by field_simp
    have hexp : 1 ≤ Real.exp 1 * w t := by
      calc
        1 = Real.exp 0 := by rw [Real.exp_zero]
        _ ≤ Real.exp (1 + (-(T⁻¹ ^ 2 * t ^ 2))) := by
          exact Real.exp_le_exp.mpr (by linarith)
        _ = Real.exp 1 * w t := by
          rw [Real.exp_add]
          unfold w finiteHalaszGaussianWeight
          congr 2
          ring
    have hq0 : 0 ≤ q t := Complex.normSq_nonneg _
    calc
      q t = q t * 1 := by ring
      _ ≤ q t * (Real.exp 1 * w t) :=
        mul_le_mul_of_nonneg_left hexp hq0
      _ = Real.exp 1 * (q t * w t) := by ring
  have hsharp :
      (∫ t in -T..T, q t) ≤
        ∫ t in -T..T, Real.exp 1 * (q t * w t) := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact hq_cont.intervalIntegrable (-T) T
    · exact (hw_int.const_mul (Real.exp 1)).intervalIntegrable
    · exact hpoint
  have hrestricted :
      (∫ t in -T..T, q t * w t) ≤ ∫ t : ℝ, q t * w t := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    apply integral_mono_measure Measure.restrict_le_self
    · filter_upwards with t
      exact mul_nonneg (Complex.normSq_nonneg _)
        (finiteHalaszGaussianWeight_nonneg _ _)
    · exact hw_int
  calc
    (∫ t in -T..T, Complex.normSq (finiteFrequencyPolynomial freq a t)) =
        ∫ t in -T..T, q t := rfl
    _ ≤ ∫ t in -T..T, Real.exp 1 * (q t * w t) := hsharp
    _ = Real.exp 1 * ∫ t in -T..T, q t * w t := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ Real.exp 1 * ∫ t : ℝ, q t * w t :=
      mul_le_mul_of_nonneg_left hrestricted (Real.exp_pos 1).le
    _ ≤ Real.exp 1 *
        finiteHalaszGaussianPairMajorant freq a (T⁻¹ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
      exact integral_normSq_finiteFrequencyPolynomial_mul_gaussian_le
        freq a hb

/-! ## Logarithmic-polynomial specialization -/

/-- The Gaussian pair majorant written as an ordinary double sum over a
finite set of integers.  This is the form to which interval-sieve bounds
apply. -/
def finiteHalaszLogGaussianPairMajorant
    (D : Finset ℕ) (a : ℕ → ℂ) (b : ℝ) : ℝ :=
  Real.sqrt (Real.pi / b) *
    ∑ n ∈ D, ∑ m ∈ D,
      ‖a n‖ * ‖a m‖ *
        finiteHalaszGaussianPairKernel b (Real.log m - Real.log n)

theorem finiteHalaszGaussianPairMajorant_subtype_eq_log
    (D : Finset ℕ) (a : ℕ → ℂ) (b : ℝ) :
    finiteHalaszGaussianPairMajorant
        (fun n : ↥D ↦ Real.log n.1) (fun n : ↥D ↦ a n.1) b =
      finiteHalaszLogGaussianPairMajorant D a b := by
  classical
  unfold finiteHalaszGaussianPairMajorant finiteHalaszLogGaussianPairMajorant
  congr 1
  simp only [Finset.univ_eq_attach]
  calc
    (∑ r ∈ D.attach, ∑ s ∈ D.attach,
        ‖a r.1‖ * ‖a s.1‖ *
          finiteHalaszGaussianPairKernel b
            (Real.log s.1 - Real.log r.1)) =
        ∑ r ∈ D.attach, ∑ m ∈ D,
          ‖a r.1‖ * ‖a m‖ *
            finiteHalaszGaussianPairKernel b
              (Real.log m - Real.log r.1) := by
      apply Finset.sum_congr rfl
      intro r hr
      simpa using Finset.sum_attach D (fun m ↦
        ‖a r.1‖ * ‖a m‖ *
          finiteHalaszGaussianPairKernel b
            (Real.log m - Real.log r.1))
    _ = ∑ n ∈ D, ∑ m ∈ D,
          ‖a n‖ * ‖a m‖ *
            finiteHalaszGaussianPairKernel b
              (Real.log m - Real.log n) := by
      simpa using Finset.sum_attach D (fun n ↦
        ∑ m ∈ D, ‖a n‖ * ‖a m‖ *
          finiteHalaszGaussianPairKernel b (Real.log m - Real.log n))

/-- Forgetting the Gaussian off-diagonal decay still leaves a useful
dyadic-shell estimate: the pair sum is at most the shell cardinality times
the coefficient square mass. -/
theorem finiteHalaszLogGaussianPairMajorant_le_card_mul_sum_normSq
    (D : Finset ℕ) (a : ℕ → ℂ) {b : ℝ} (hb : 0 < b) :
    finiteHalaszLogGaussianPairMajorant D a b ≤
      Real.sqrt (Real.pi / b) *
        ((D.card : ℝ) * ∑ n ∈ D, Complex.normSq (a n)) := by
  unfold finiteHalaszLogGaussianPairMajorant
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  calc
    (∑ n ∈ D, ∑ m ∈ D,
        ‖a n‖ * ‖a m‖ *
          finiteHalaszGaussianPairKernel b (Real.log m - Real.log n)) ≤
        ∑ n ∈ D, ∑ m ∈ D,
          (‖a n‖ ^ 2 + ‖a m‖ ^ 2) / 2 := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro m hm
      calc
        ‖a n‖ * ‖a m‖ *
            finiteHalaszGaussianPairKernel b (Real.log m - Real.log n) ≤
            ‖a n‖ * ‖a m‖ := by
          exact mul_le_of_le_one_right
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
            (finiteHalaszGaussianPairKernel_le_one hb _)
        _ ≤ (‖a n‖ ^ 2 + ‖a m‖ ^ 2) / 2 := by
          nlinarith [sq_nonneg (‖a n‖ - ‖a m‖)]
    _ = (D.card : ℝ) * ∑ n ∈ D, Complex.normSq (a n) := by
      simp_rw [Complex.normSq_eq_norm_sq]
      simp only [div_eq_mul_inv, add_mul, Finset.sum_add_distrib,
        Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      ring

/-- Gaussian local-pair mean square for a finite logarithmic Dirichlet
polynomial. -/
theorem intervalIntegral_normSq_logarithmicDirichletPolynomial_le_gaussianPairMajorant
    (D : Finset ℕ) (a : ℕ → ℂ) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T,
        Complex.normSq (logarithmicDirichletPolynomial D a t)) ≤
      Real.exp 1 *
        finiteHalaszLogGaussianPairMajorant D a (T⁻¹ ^ 2) := by
  classical
  have h := intervalIntegral_normSq_finiteFrequencyPolynomial_le_gaussianPairMajorant
    (fun n : ↥D ↦ Real.log n.1) (fun n : ↥D ↦ a n.1) hT
  simpa only [finiteFrequencyPolynomial_subtype_eq_logarithmic,
    finiteHalaszGaussianPairMajorant_subtype_eq_log] using h

/-- Gaussian local-pair mean square for a positive prime-band factor on
an arbitrary finite coefficient interval. -/
theorem intervalIntegral_normSq_smoothedPrimeBandPolynomial_le_gaussianPairMajorant
    (f : ℕ → ℂ) (Q : ℕ → Prop) [DecidablePred Q]
    (sigma : ℝ) (L U : ℕ) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T,
        Complex.normSq (smoothedPrimeBandPolynomial f Q sigma L U t)) ≤
      Real.exp 1 *
        finiteHalaszLogGaussianPairMajorant (Finset.Ioc L U)
          (smoothedPrimeBandCoefficient f Q sigma) (T⁻¹ ^ 2) := by
  exact intervalIntegral_normSq_logarithmicDirichletPolynomial_le_gaussianPairMajorant
    (Finset.Ioc L U) (smoothedPrimeBandCoefficient f Q sigma) hT

/-- Dyadic-shell form of the Gaussian estimate, expressed only through
the coefficient square mass.  Crucially, the spacing loss is the shell
cardinality rather than the ambient upper endpoint. -/
theorem intervalIntegral_normSq_smoothedPrimeBandPolynomial_le_gaussianCardSquareMass
    (f : ℕ → ℂ) (Q : ℕ → Prop) [DecidablePred Q]
    (sigma : ℝ) (L U : ℕ) {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T,
        Complex.normSq (smoothedPrimeBandPolynomial f Q sigma L U t)) ≤
      Real.exp 1 *
        (Real.sqrt (Real.pi / (T⁻¹ ^ 2)) *
          (((U - L : ℕ) : ℝ) *
            ∑ n ∈ Finset.Ioc L U,
              Complex.normSq (smoothedPrimeBandCoefficient f Q sigma n))) := by
  have hb : 0 < T⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr hT)
  have hgauss :=
    intervalIntegral_normSq_smoothedPrimeBandPolynomial_le_gaussianPairMajorant
      f Q sigma L U hT
  have hpair := finiteHalaszLogGaussianPairMajorant_le_card_mul_sum_normSq
    (Finset.Ioc L U) (smoothedPrimeBandCoefficient f Q sigma) hb
  rw [Nat.card_Ioc] at hpair
  exact hgauss.trans <|
    mul_le_mul_of_nonneg_left hpair (Real.exp_pos 1).le

/-- The Gaussian dyadic-shell estimate with its arithmetic square mass
discharged by one concrete missing-prime block. -/
theorem intervalIntegral_normSq_smoothedPrimeBandPolynomial_le_gaussianMissingBlock
    (I : ℕ × ℕ) (Q : ℕ → Prop) [DecidablePred Q]
    (hdisj : ∀ p ∈ primesInBlock I, ¬ Q p)
    (f : ℕ → ℂ) (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {sigma : ℝ} (hsigma : 1 ≤ sigma)
    {L U : ℕ} (hL : 0 < L) (_hLU : L ≤ U)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T,
        Complex.normSq (smoothedPrimeBandPolynomial f Q sigma L U t)) ≤
      Real.exp 1 *
        (Real.sqrt (Real.pi / (T⁻¹ ^ 2)) *
          (((U - L : ℕ) : ℝ) *
            (((L : ℝ)⁻¹) ^ 2 *
              ((missingPrimeBlockSet I U).card : ℝ)))) := by
  have hgauss :=
    intervalIntegral_normSq_smoothedPrimeBandPolynomial_le_gaussianCardSquareMass
      f Q sigma L U hT
  have hsmooth := sum_normSq_smoothedPrimeBandCoefficient_le_harmonic
    (f := f) Q hsigma (L := L) (U := U) hL
  have hharmonic := sum_normSq_harmonicPrimeBandCoefficient_le
    (f := f) (L := L) (U := U) Q hL
  have hmissing :=
    sum_normSq_primeBandCoefficient_le_card_missingPrimeBlockSet
      I Q hdisj f hbound (L := L) (U := U) hL
  have hmass :
      (∑ n ∈ Finset.Ioc L U,
          Complex.normSq (smoothedPrimeBandCoefficient f Q sigma n)) ≤
        ((L : ℝ)⁻¹) ^ 2 *
          ((missingPrimeBlockSet I U).card : ℝ) :=
    hsmooth.trans <| hharmonic.trans <|
      mul_le_mul_of_nonneg_left hmissing (sq_nonneg _)
  have hfactor : 0 ≤
      Real.exp 1 * Real.sqrt (Real.pi / (T⁻¹ ^ 2)) *
        ((U - L : ℕ) : ℝ) := by positivity
  calc
    (∫ t in -T..T,
        Complex.normSq (smoothedPrimeBandPolynomial f Q sigma L U t)) ≤
      Real.exp 1 *
        (Real.sqrt (Real.pi / (T⁻¹ ^ 2)) *
          (((U - L : ℕ) : ℝ) *
            ∑ n ∈ Finset.Ioc L U,
              Complex.normSq (smoothedPrimeBandCoefficient f Q sigma n))) :=
        hgauss
    _ ≤ Real.exp 1 *
        (Real.sqrt (Real.pi / (T⁻¹ ^ 2)) *
          (((U - L : ℕ) : ℝ) *
            (((L : ℝ)⁻¹) ^ 2 *
              ((missingPrimeBlockSet I U).card : ℝ)))) := by
      gcongr

/-- Fully explicit beta-sieve/Mertens discharge of the Gaussian dyadic
shell energy.  Unlike the earlier global-spacing estimate, the analytic
factor is the shell length `U-L`; for `U ≤ 2L` this cancels the harmonic
square weight up to the beta-sieve density. -/
theorem exists_intervalIntegral_normSq_smoothedPrimeBandPolynomial_gaussian_mertens_beta_bound :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ (I : ℕ × ℕ) (Q : ℕ → Prop) [DecidablePred Q]
        (f : ℕ → ℂ) (L U S : ℕ) {sigma T : ℝ},
        (∀ p ∈ primesInBlock I, ¬ Q p) →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) →
        0 < L → L ≤ U → 1 ≤ sigma → 0 < T →
        3 ≤ I.1 → I.1 ≤ I.2 → 101 ≤ S →
        Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99 →
        (∫ t in -T..T,
            Complex.normSq
              (smoothedPrimeBandPolynomial f Q sigma L U t)) ≤
          Real.exp 1 *
            (Real.sqrt (Real.pi / (T⁻¹ ^ 2)) *
              (((U - L : ℕ) : ℝ) * (((L : ℝ)⁻¹) ^ 2 *
                ((U : ℝ) *
                    ((1 + (4 * Cβ / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
                      (Real.exp (2 * Erdos67.PrimeEstimates.mertensBound) *
                        (Real.log ((I.1 - 1 : ℕ) : ℝ) /
                          Real.log (I.2 : ℝ)))) +
                  ((I.2 ^ S : ℕ) : ℝ) ^ 2)))) := by
  obtain ⟨Cβ, hCβ, hbeta⟩ :=
    exists_card_missingPrimeBlockSet_mertens_beta_bound
  refine ⟨Cβ, hCβ, ?_⟩
  intro I Q _ f L U S sigma T hdisj hbound hL hLU hsigma hT
    hlo hI hS hlog
  have henergy :=
    intervalIntegral_normSq_smoothedPrimeBandPolynomial_le_gaussianMissingBlock
      I Q hdisj f hbound hsigma hL hLU hT
  have hcard := hbeta U I.1 I.2 S hlo hI hS hlog
  calc
    (∫ t in -T..T,
        Complex.normSq (smoothedPrimeBandPolynomial f Q sigma L U t)) ≤
      Real.exp 1 *
        (Real.sqrt (Real.pi / (T⁻¹ ^ 2)) *
          (((U - L : ℕ) : ℝ) *
            (((L : ℝ)⁻¹) ^ 2 *
              ((missingPrimeBlockSet I U).card : ℝ)))) := henergy
    _ ≤ Real.exp 1 *
        (Real.sqrt (Real.pi / (T⁻¹ ^ 2)) *
          (((U - L : ℕ) : ℝ) * (((L : ℝ)⁻¹) ^ 2 *
            ((U : ℝ) *
                ((1 + (4 * Cβ / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
                  (Real.exp (2 * Erdos67.PrimeEstimates.mertensBound) *
                    (Real.log ((I.1 - 1 : ℕ) : ℝ) /
                      Real.log (I.2 : ℝ)))) +
              ((I.2 ^ S : ℕ) : ℝ) ^ 2)))) := by
      gcongr

/-- The explicit right side of the beta-sieve Gaussian estimate for one
coefficient shell. -/
def finiteHalaszGaussianBetaShellBound
    (Cβ : ℝ) (I : ℕ × ℕ) (S : ℕ) (T : ℝ) (L U : ℕ) : ℝ :=
  Real.exp 1 *
    (Real.sqrt (Real.pi / (T⁻¹ ^ 2)) *
      (((U - L : ℕ) : ℝ) * (((L : ℝ)⁻¹) ^ 2 *
        ((U : ℝ) *
            ((1 + (4 * Cβ / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
              (Real.exp (2 * Erdos67.PrimeEstimates.mertensBound) *
                (Real.log ((I.1 - 1 : ℕ) : ℝ) /
                  Real.log (I.2 : ℝ)))) +
          ((I.2 ^ S : ℕ) : ℝ) ^ 2))))

/-- The Mertens density term in the concrete shell bound. -/
def finiteHalaszGaussianBetaDensity
    (Cβ : ℝ) (I : ℕ × ℕ) (S : ℕ) : ℝ :=
  (1 + (4 * Cβ / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
    (Real.exp (2 * Erdos67.PrimeEstimates.mertensBound) *
      (Real.log ((I.1 - 1 : ℕ) : ℝ) / Real.log (I.2 : ℝ)))

/-- The finite beta-sieve level remainder. -/
def finiteHalaszGaussianBetaRemainder (I : ℕ × ℕ) (S : ℕ) : ℝ :=
  ((I.2 ^ S : ℕ) : ℝ) ^ 2

/-- On an exact dyadic shell the length and harmonic square factors
cancel, leaving twice the beta density plus the finite remainder divided
by the lower shell endpoint. -/
theorem finiteHalaszGaussianBetaShellBound_two_mul
    (Cβ : ℝ) (I : ℕ × ℕ) (S : ℕ) (T : ℝ)
    {L : ℕ} (hL : 0 < L) :
    finiteHalaszGaussianBetaShellBound Cβ I S T L (2 * L) =
      Real.exp 1 * Real.sqrt (Real.pi / (T⁻¹ ^ 2)) *
        (2 * finiteHalaszGaussianBetaDensity Cβ I S +
          finiteHalaszGaussianBetaRemainder I S * (L : ℝ)⁻¹) := by
  have hsub : 2 * L - L = L := by omega
  have hLne : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  unfold finiteHalaszGaussianBetaShellBound
    finiteHalaszGaussianBetaDensity finiteHalaszGaussianBetaRemainder
  rw [hsub]
  push_cast
  field_simp

theorem finiteHalaszGaussianBetaShellBound_pow_mul_le_cutoff
    (Cβ : ℝ) (I : ℕ × ℕ) (S : ℕ) (T : ℝ)
    {L : ℕ} (hL : 0 < L) (j : ℕ) :
    finiteHalaszGaussianBetaShellBound Cβ I S T
        (2 ^ j * L) (2 ^ (j + 1) * L) ≤
      Real.exp 1 * Real.sqrt (Real.pi / (T⁻¹ ^ 2)) *
        (2 * finiteHalaszGaussianBetaDensity Cβ I S +
          finiteHalaszGaussianBetaRemainder I S * (L : ℝ)⁻¹) := by
  have hLj : 0 < 2 ^ j * L := mul_pos (pow_pos (by omega) j) hL
  have hU : 2 ^ (j + 1) * L = 2 * (2 ^ j * L) := by
    rw [pow_succ]
    ring
  rw [hU, finiteHalaszGaussianBetaShellBound_two_mul
    Cβ I S T hLj]
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hLjreal : (0 : ℝ) < 2 ^ j * L := by exact_mod_cast hLj
  have hLle : (L : ℝ) ≤ (2 ^ j * L : ℕ) := by
    exact_mod_cast Nat.le_mul_of_pos_left L (pow_pos (by omega) j)
  have hinv : ((2 ^ j * L : ℕ) : ℝ)⁻¹ ≤ (L : ℝ)⁻¹ :=
    inv_anti₀ hLreal hLle
  have hrem : 0 ≤ finiteHalaszGaussianBetaRemainder I S := by
    unfold finiteHalaszGaussianBetaRemainder
    positivity
  have hfactor : 0 ≤
      Real.exp 1 * Real.sqrt (Real.pi / (T⁻¹ ^ 2)) := by positivity
  gcongr

/-! ## Reassembling dyadic coefficient shells -/

/-- A positive prefix ending at a power of two is the exact sum of its
dyadic coefficient shells. -/
theorem smoothedPrimeBandPolynomial_one_twoPow_eq_sum_dyadic
    (f : ℕ → ℂ) (Q : ℕ → Prop) [DecidablePred Q]
    (sigma : ℝ) (J : ℕ) (t : ℝ) :
    smoothedPrimeBandPolynomial f Q sigma 1 (2 ^ J) t =
      ∑ j ∈ Finset.range J,
        smoothedPrimeBandPolynomial f Q sigma
          (2 ^ j) (2 ^ (j + 1)) t := by
  unfold smoothedPrimeBandPolynomial logarithmicDirichletPolynomial
  simpa [Erdos67.dyadicNatWindow, Erdos67.dyadicNatBlock] using
    (Erdos67.sum_dyadicNatWindow_eq_sum_blocks 1 J
      (fun n ↦ smoothedPrimeBandCoefficient f Q sigma n *
        logarithmicPhase n t))

/-- If `Q` contains no prime up to `L`, its band coefficient vanishes on
every nonconstant integer at most `L`. -/
theorem primeBandCoefficient_eq_zero_of_le_primeCutoff
    (f : ℕ → ℂ) (Q : ℕ → Prop) [DecidablePred Q]
    {L n : ℕ} (hQ : ∀ p, p.Prime → p ≤ L → ¬ Q p)
    (hn1 : 1 < n) (hnL : n ≤ L) :
    primeBandCoefficient f Q n = 0 := by
  unfold primeBandCoefficient
  split_ifs with hsupp
  · exfalso
    obtain ⟨p, hpprime, hpn⟩ :=
      Nat.ne_one_iff_exists_prime_dvd.mp hn1.ne'
    have hnpos : 0 < n := by omega
    have hpFactors : p ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpprime, hpn, hnpos.ne'⟩
    have hpL : p ≤ L :=
      (Nat.le_of_dvd hnpos hpn).trans hnL
    exact (hQ p hpprime hpL) (hsupp.2 p hpFactors)
  · rfl

theorem smoothedPrimeBandCoefficient_eq_zero_of_le_primeCutoff
    (f : ℕ → ℂ) (Q : ℕ → Prop) [DecidablePred Q]
    (sigma : ℝ) {L n : ℕ}
    (hQ : ∀ p, p.Prime → p ≤ L → ¬ Q p)
    (hn1 : 1 < n) (hnL : n ≤ L) :
    smoothedPrimeBandCoefficient f Q sigma n = 0 := by
  unfold smoothedPrimeBandCoefficient
  rw [primeBandCoefficient_eq_zero_of_le_primeCutoff f Q hQ hn1 hnL,
    zero_mul]

/-- Exact dyadic-shell decomposition above a prime cutoff.  The band
support hypothesis removes the entire lower prefix `(1,L]`. -/
theorem smoothedPrimeBandPolynomial_one_mul_twoPow_eq_sum_dyadic_of_cutoff
    (f : ℕ → ℂ) (Q : ℕ → Prop) [DecidablePred Q]
    (sigma : ℝ) {L : ℕ} (hL : 0 < L)
    (hQ : ∀ p, p.Prime → p ≤ L → ¬ Q p)
    (J : ℕ) (t : ℝ) :
    smoothedPrimeBandPolynomial f Q sigma 1 (2 ^ J * L) t =
      ∑ j ∈ Finset.range J,
        smoothedPrimeBandPolynomial f Q sigma
          (2 ^ j * L) (2 ^ (j + 1) * L) t := by
  let term : ℕ → ℂ := fun n ↦
    smoothedPrimeBandCoefficient f Q sigma n * logarithmicPhase n t
  have hLtop : L ≤ 2 ^ J * L := by
    exact Nat.le_mul_of_pos_left L (pow_pos (by omega) J)
  have hsubset : Finset.Ioc L (2 ^ J * L) ⊆
      Finset.Ioc 1 (2 ^ J * L) := by
    intro n hn
    exact Finset.mem_Ioc.mpr
      ⟨lt_of_le_of_lt hL (Finset.mem_Ioc.mp hn).1,
        (Finset.mem_Ioc.mp hn).2⟩
  have hsumCut :
      (∑ n ∈ Finset.Ioc 1 (2 ^ J * L), term n) =
        ∑ n ∈ Finset.Ioc L (2 ^ J * L), term n := by
    symm
    apply Finset.sum_subset hsubset
    intro n hnFull hnWindow
    have hn := Finset.mem_Ioc.mp hnFull
    have hnL : n ≤ L := by
      by_contra hnot
      exact hnWindow (Finset.mem_Ioc.mpr
        ⟨Nat.lt_of_not_ge hnot, hn.2⟩)
    unfold term
    rw [smoothedPrimeBandCoefficient_eq_zero_of_le_primeCutoff
      f Q sigma hQ hn.1 hnL, zero_mul]
  unfold smoothedPrimeBandPolynomial logarithmicDirichletPolynomial
  rw [hsumCut]
  simpa [Erdos67.dyadicNatWindow, Erdos67.dyadicNatBlock] using
    (Erdos67.sum_dyadicNatWindow_eq_sum_blocks L J term)

/-- Integrated finite Cauchy--Schwarz for a pointwise finite-sum
decomposition. -/
theorem intervalIntegral_normSq_le_card_mul_sum_of_eq_finset
    {ι : Type*} (s : Finset ι) (F : ℝ → ℂ) (G : ι → ℝ → ℂ)
    {T : ℝ} (hT : 0 ≤ T)
    (hF : Continuous F) (hG : ∀ i ∈ s, Continuous (G i))
    (hEq : ∀ t, F t = ∑ i ∈ s, G i t) :
    (∫ t in -T..T, Complex.normSq (F t)) ≤
      (s.card : ℝ) * ∑ i ∈ s,
        ∫ t in -T..T, Complex.normSq (G i t) := by
  have hpoint : ∀ t,
      Complex.normSq (F t) ≤
        (s.card : ℝ) * ∑ i ∈ s, Complex.normSq (G i t) := by
    intro t
    rw [hEq t]
    exact Erdos67.normSq_finset_sum_le_card_mul_sum_normSq s
      (fun i ↦ G i t)
  have hmono :
      (∫ t in -T..T, Complex.normSq (F t)) ≤
        ∫ t in -T..T,
          (s.card : ℝ) * ∑ i ∈ s, Complex.normSq (G i t) := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (Complex.continuous_normSq.comp hF).intervalIntegrable _ _
    · apply Continuous.intervalIntegrable
      apply Continuous.const_mul
      fun_prop
    · intro t ht
      exact hpoint t
  calc
    (∫ t in -T..T, Complex.normSq (F t)) ≤
        ∫ t in -T..T,
          (s.card : ℝ) * ∑ i ∈ s, Complex.normSq (G i t) := hmono
    _ = (s.card : ℝ) * ∫ t in -T..T,
        ∑ i ∈ s, Complex.normSq (G i t) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (s.card : ℝ) * ∑ i ∈ s,
        ∫ t in -T..T, Complex.normSq (G i t) := by
      congr 1
      rw [intervalIntegral.integral_finsetSum]
      intro i hi
      exact (Complex.continuous_normSq.comp (hG i hi)).intervalIntegrable _ _

/-- Energy reassembly above a prime cutoff. -/
theorem intervalIntegral_normSq_smoothedPrimeBandPolynomial_one_mul_twoPow_le_dyadic_of_cutoff
    (f : ℕ → ℂ) (Q : ℕ → Prop) [DecidablePred Q]
    (sigma : ℝ) {L : ℕ} (hL : 0 < L)
    (hQ : ∀ p, p.Prime → p ≤ L → ¬ Q p)
    (J : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T,
        Complex.normSq
          (smoothedPrimeBandPolynomial f Q sigma 1 (2 ^ J * L) t)) ≤
      (J : ℝ) * ∑ j ∈ Finset.range J,
        ∫ t in -T..T,
          Complex.normSq
            (smoothedPrimeBandPolynomial f Q sigma
              (2 ^ j * L) (2 ^ (j + 1) * L) t) := by
  have henergy := intervalIntegral_normSq_le_card_mul_sum_of_eq_finset
    (Finset.range J)
    (smoothedPrimeBandPolynomial f Q sigma 1 (2 ^ J * L))
    (fun j ↦ smoothedPrimeBandPolynomial f Q sigma
      (2 ^ j * L) (2 ^ (j + 1) * L)) hT
  have hF : Continuous
      (smoothedPrimeBandPolynomial f Q sigma 1 (2 ^ J * L)) := by
    unfold smoothedPrimeBandPolynomial logarithmicDirichletPolynomial
      logarithmicPhase
    fun_prop
  have hG : ∀ j ∈ Finset.range J, Continuous
      (smoothedPrimeBandPolynomial f Q sigma
        (2 ^ j * L) (2 ^ (j + 1) * L)) := by
    intro j hj
    unfold smoothedPrimeBandPolynomial logarithmicDirichletPolynomial
      logarithmicPhase
    fun_prop
  simpa using henergy hF hG
    (smoothedPrimeBandPolynomial_one_mul_twoPow_eq_sum_dyadic_of_cutoff
      f Q sigma hL hQ J)

/-- The final finite form of the cutoff reassembly: every shell is bounded
by the explicit Gaussian beta-sieve quantity, and the lower cutoff `L`
suppresses the finite sieve-level remainder. -/
theorem exists_intervalIntegral_normSq_smoothedPrimeBandPolynomial_cutoff_gaussian_mertens_beta_bound :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ (I : ℕ × ℕ) (Q : ℕ → Prop) [DecidablePred Q]
        (f : ℕ → ℂ) (L J S : ℕ) {sigma T : ℝ},
        (∀ p ∈ primesInBlock I, ¬ Q p) →
        (∀ p, p.Prime → p ≤ L → ¬ Q p) →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) →
        0 < L → 1 ≤ sigma → 0 < T →
        3 ≤ I.1 → I.1 ≤ I.2 → 101 ≤ S →
        Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99 →
        (∫ t in -T..T,
            Complex.normSq
              (smoothedPrimeBandPolynomial f Q sigma 1 (2 ^ J * L) t)) ≤
          (J : ℝ) * ∑ j ∈ Finset.range J,
            finiteHalaszGaussianBetaShellBound Cβ I S T
              (2 ^ j * L) (2 ^ (j + 1) * L) := by
  obtain ⟨Cβ, hCβ, hshell⟩ :=
    exists_intervalIntegral_normSq_smoothedPrimeBandPolynomial_gaussian_mertens_beta_bound
  refine ⟨Cβ, hCβ, ?_⟩
  intro I Q _ f L J S sigma T hdisj hQ hbound hL hsigma hT
    hlo hI hS hlog
  have hdecomp :=
    intervalIntegral_normSq_smoothedPrimeBandPolynomial_one_mul_twoPow_le_dyadic_of_cutoff
      f Q sigma hL hQ J hT.le
  have hsum :
      (∑ j ∈ Finset.range J,
          ∫ t in -T..T,
            Complex.normSq
              (smoothedPrimeBandPolynomial f Q sigma
                (2 ^ j * L) (2 ^ (j + 1) * L) t)) ≤
        ∑ j ∈ Finset.range J,
          finiteHalaszGaussianBetaShellBound Cβ I S T
            (2 ^ j * L) (2 ^ (j + 1) * L) := by
    apply Finset.sum_le_sum
    intro j hj
    have hLj : 0 < 2 ^ j * L := mul_pos (pow_pos (by omega) j) hL
    have hJU : 2 ^ j * L ≤ 2 ^ (j + 1) * L := by
      apply Nat.mul_le_mul_right L
      rw [pow_succ]
      omega
    simpa only [finiteHalaszGaussianBetaShellBound] using
      (hshell I Q f (2 ^ j * L) (2 ^ (j + 1) * L) S hdisj hbound
        hLj hJU hsigma hT hlo hI hS hlog)
  exact hdecomp.trans <|
    mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg J)

/-- Scalar cutoff endpoint.  The only arithmetic losses are the squared
number of coefficient shells, the Mertens density, and the beta-sieve
remainder divided by the lower prime cutoff. -/
theorem exists_intervalIntegral_normSq_smoothedPrimeBandPolynomial_cutoff_gaussian_scalar_bound :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ (I : ℕ × ℕ) (Q : ℕ → Prop) [DecidablePred Q]
        (f : ℕ → ℂ) (L J S : ℕ) {sigma T : ℝ},
        (∀ p ∈ primesInBlock I, ¬ Q p) →
        (∀ p, p.Prime → p ≤ L → ¬ Q p) →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) →
        0 < L → 1 ≤ sigma → 0 < T →
        3 ≤ I.1 → I.1 ≤ I.2 → 101 ≤ S →
        Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99 →
        (∫ t in -T..T,
            Complex.normSq
              (smoothedPrimeBandPolynomial f Q sigma 1 (2 ^ J * L) t)) ≤
          (J : ℝ) ^ 2 *
            (Real.exp 1 * Real.sqrt (Real.pi / (T⁻¹ ^ 2)) *
              (2 * finiteHalaszGaussianBetaDensity Cβ I S +
                finiteHalaszGaussianBetaRemainder I S * (L : ℝ)⁻¹)) := by
  obtain ⟨Cβ, hCβ, hcutoff⟩ :=
    exists_intervalIntegral_normSq_smoothedPrimeBandPolynomial_cutoff_gaussian_mertens_beta_bound
  refine ⟨Cβ, hCβ, ?_⟩
  intro I Q _ f L J S sigma T hdisj hQ hbound hL hsigma hT
    hlo hI hS hlog
  have hbase := hcutoff I Q f L J S hdisj hQ hbound hL hsigma hT
    hlo hI hS hlog
  let B : ℝ :=
    Real.exp 1 * Real.sqrt (Real.pi / (T⁻¹ ^ 2)) *
      (2 * finiteHalaszGaussianBetaDensity Cβ I S +
        finiteHalaszGaussianBetaRemainder I S * (L : ℝ)⁻¹)
  have hsum :
      (∑ j ∈ Finset.range J,
          finiteHalaszGaussianBetaShellBound Cβ I S T
            (2 ^ j * L) (2 ^ (j + 1) * L)) ≤
        (J : ℝ) * B := by
    calc
      (∑ j ∈ Finset.range J,
          finiteHalaszGaussianBetaShellBound Cβ I S T
            (2 ^ j * L) (2 ^ (j + 1) * L)) ≤
          ∑ _j ∈ Finset.range J, B := by
        apply Finset.sum_le_sum
        intro j hj
        exact finiteHalaszGaussianBetaShellBound_pow_mul_le_cutoff
          Cβ I S T hL j
      _ = (J : ℝ) * B := by simp
  calc
    (∫ t in -T..T,
        Complex.normSq
          (smoothedPrimeBandPolynomial f Q sigma 1 (2 ^ J * L) t)) ≤
      (J : ℝ) * ∑ j ∈ Finset.range J,
        finiteHalaszGaussianBetaShellBound Cβ I S T
          (2 ^ j * L) (2 ^ (j + 1) * L) := hbase
    _ ≤ (J : ℝ) * ((J : ℝ) * B) :=
      mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg J)
    _ = (J : ℝ) ^ 2 *
        (Real.exp 1 * Real.sqrt (Real.pi / (T⁻¹ ^ 2)) *
          (2 * finiteHalaszGaussianBetaDensity Cβ I S +
            finiteHalaszGaussianBetaRemainder I S * (L : ℝ)⁻¹)) := by
      dsimp [B]
      ring

/-- The square energy of a power-of-two positive prefix is bounded by the
number of dyadic shells times the sum of their individual square energies.
This is the finite reassembly step needed after the Gaussian shell bound. -/
theorem intervalIntegral_normSq_smoothedPrimeBandPolynomial_one_twoPow_le_dyadic
    (f : ℕ → ℂ) (Q : ℕ → Prop) [DecidablePred Q]
    (sigma : ℝ) (J : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T,
        Complex.normSq
          (smoothedPrimeBandPolynomial f Q sigma 1 (2 ^ J) t)) ≤
      (J : ℝ) * ∑ j ∈ Finset.range J,
        ∫ t in -T..T,
          Complex.normSq
            (smoothedPrimeBandPolynomial f Q sigma
              (2 ^ j) (2 ^ (j + 1)) t) := by
  let P : ℝ → ℂ := fun t ↦
    smoothedPrimeBandPolynomial f Q sigma 1 (2 ^ J) t
  let G : ℕ → ℝ → ℂ := fun j t ↦
    smoothedPrimeBandPolynomial f Q sigma (2 ^ j) (2 ^ (j + 1)) t
  have hP : Continuous P := by
    unfold P smoothedPrimeBandPolynomial logarithmicDirichletPolynomial
      logarithmicPhase
    fun_prop
  have hG : ∀ j, Continuous (G j) := by
    intro j
    unfold G smoothedPrimeBandPolynomial logarithmicDirichletPolynomial
      logarithmicPhase
    fun_prop
  have hpoint : ∀ t,
      Complex.normSq (P t) ≤
        (J : ℝ) * ∑ j ∈ Finset.range J, Complex.normSq (G j t) := by
    intro t
    rw [show P t = ∑ j ∈ Finset.range J, G j t by
      exact smoothedPrimeBandPolynomial_one_twoPow_eq_sum_dyadic
        f Q sigma J t]
    simpa using
      (Erdos67.normSq_finset_sum_le_card_mul_sum_normSq
        (Finset.range J) (fun j ↦ G j t))
  have hmono :
      (∫ t in -T..T, Complex.normSq (P t)) ≤
        ∫ t in -T..T,
          (J : ℝ) * ∑ j ∈ Finset.range J,
            Complex.normSq (G j t) := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (Complex.continuous_normSq.comp hP).intervalIntegrable _ _
    · apply Continuous.intervalIntegrable
      fun_prop
    · intro t ht
      exact hpoint t
  calc
    (∫ t in -T..T,
        Complex.normSq
          (smoothedPrimeBandPolynomial f Q sigma 1 (2 ^ J) t)) =
        ∫ t in -T..T, Complex.normSq (P t) := rfl
    _ ≤ ∫ t in -T..T,
        (J : ℝ) * ∑ j ∈ Finset.range J,
          Complex.normSq (G j t) := hmono
    _ = (J : ℝ) * ∫ t in -T..T,
        ∑ j ∈ Finset.range J, Complex.normSq (G j t) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (J : ℝ) * ∑ j ∈ Finset.range J,
        ∫ t in -T..T, Complex.normSq (G j t) := by
      congr 1
      rw [intervalIntegral.integral_finsetSum]
      intro j hj
      exact (Complex.continuous_normSq.comp (hG j)).intervalIntegrable _ _
    _ = _ := rfl

/-- Power-of-two prefix energy with every dyadic shell discharged by the
same beta-sieve/Mertens constant.  All finite sieve remainders remain
explicit in the shell sum. -/
theorem exists_intervalIntegral_normSq_smoothedPrimeBandPolynomial_one_twoPow_gaussian_mertens_beta_bound :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ (I : ℕ × ℕ) (Q : ℕ → Prop) [DecidablePred Q]
        (f : ℕ → ℂ) (J S : ℕ) {sigma T : ℝ},
        (∀ p ∈ primesInBlock I, ¬ Q p) →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) →
        1 ≤ sigma → 0 < T →
        3 ≤ I.1 → I.1 ≤ I.2 → 101 ≤ S →
        Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99 →
        (∫ t in -T..T,
            Complex.normSq
              (smoothedPrimeBandPolynomial f Q sigma 1 (2 ^ J) t)) ≤
          (J : ℝ) * ∑ j ∈ Finset.range J,
            finiteHalaszGaussianBetaShellBound Cβ I S T
              (2 ^ j) (2 ^ (j + 1)) := by
  obtain ⟨Cβ, hCβ, hshell⟩ :=
    exists_intervalIntegral_normSq_smoothedPrimeBandPolynomial_gaussian_mertens_beta_bound
  refine ⟨Cβ, hCβ, ?_⟩
  intro I Q _ f J S sigma T hdisj hbound hsigma hT hlo hI hS hlog
  have hdecomp :=
    intervalIntegral_normSq_smoothedPrimeBandPolynomial_one_twoPow_le_dyadic
      f Q sigma J hT.le
  have hsum :
      (∑ j ∈ Finset.range J,
          ∫ t in -T..T,
            Complex.normSq
              (smoothedPrimeBandPolynomial f Q sigma
                (2 ^ j) (2 ^ (j + 1)) t)) ≤
        ∑ j ∈ Finset.range J,
          finiteHalaszGaussianBetaShellBound Cβ I S T
            (2 ^ j) (2 ^ (j + 1)) := by
    apply Finset.sum_le_sum
    intro j hj
    simpa only [finiteHalaszGaussianBetaShellBound] using
      (hshell I Q f (2 ^ j) (2 ^ (j + 1)) S hdisj hbound
        (by positivity) (by rw [pow_succ]; omega) hsigma hT
        hlo hI hS hlog)
  exact hdecomp.trans <|
    mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg J)

end

end Erdos67.MRHalaszBands
