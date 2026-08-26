import ErdosProblems.Erdos67b.MRRamarePerronProjection
import ErdosProblems.Erdos67b.MRPowerBlockProductEnergy
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.NumberTheory.LSeries.Deriv

/-!
# L2 bounds for the Ramaré Mellin--Perron projector

This file keeps the exact Perron kernel, including its denominator, while
passing from the pointwise projection in `MRRamarePerronProjection` to a
vertical mean-square estimate.  A finite-cofactor version is then compared
with `ramareTruncationProductEnergy`, the quantity estimated by
`MRPowerBlockProductEnergy`.
-/

open scoped BigOperators ComplexConjugate Interval LSeries.notation
open Finset Complex

namespace Erdos67b

noncomputable section

/-- Cauchy--Schwarz for a complex interval integral, in squared-norm form. -/
theorem normSq_intervalIntegral_le_length_mul_integral_normSq
    {g : ℝ → ℂ} (hg : Continuous g) {a b : ℝ} (hab : a ≤ b) :
    Complex.normSq (∫ x in a..b, g x) ≤
      (b - a) * ∫ x in a..b, Complex.normSq (g x) := by
  let μ : MeasureTheory.Measure ℝ :=
    MeasureTheory.volume.restrict (Set.Ioc a b)
  have hgint : MeasureTheory.Integrable g μ := by
    exact hg.integrableOn_Ioc
  have hnormint : MeasureTheory.Integrable (fun x ↦ ‖g x‖ ^ 2) μ := by
    exact (hg.norm.pow 2).integrableOn_Ioc
  have hmemg : MeasureTheory.MemLp (fun x ↦ ‖g x‖) 2 μ := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq]
    · simpa only [Real.norm_eq_abs, abs_norm] using hnormint
    · exact hg.norm.aestronglyMeasurable
  have hmemone : MeasureTheory.MemLp (fun _ : ℝ ↦ (1 : ℝ)) 2 μ := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq]
    · simpa using (MeasureTheory.integrableOn_const :
          MeasureTheory.IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Set.Ioc a b))
    · fun_prop
  have hmemg' : MeasureTheory.MemLp (fun x ↦ ‖g x‖)
      (ENNReal.ofReal 2) μ := by simpa using hmemg
  have hmemone' : MeasureTheory.MemLp (fun _ : ℝ ↦ (1 : ℝ))
      (ENNReal.ofReal 2) μ := by simpa using hmemone
  have hholder := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two
    (MeasureTheory.ae_of_all μ (fun x ↦ norm_nonneg (g x)))
    (MeasureTheory.ae_of_all μ (fun _ ↦ zero_le_one)) hmemg' hmemone'
  have hholder' :
      (∫ x in Set.Ioc a b, ‖g x‖) ≤
        (∫ x in Set.Ioc a b, ‖g x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∫ _x in Set.Ioc a b, (1 : ℝ) ^ (2 : ℝ)) ^
            (1 / (2 : ℝ)) := by
    simpa only [μ, mul_one] using hholder
  have hnorm : ‖∫ x in a..b, g x‖ ≤ ∫ x in a..b, ‖g x‖ :=
    intervalIntegral.norm_integral_le_integral_norm hab
  have hholder'' :
      (∫ x in a..b, ‖g x‖) ≤
        Real.sqrt (∫ x in a..b, Complex.normSq (g x)) *
          Real.sqrt (b - a) := by
    rw [intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_of_le hab]
    simpa [Complex.normSq_eq_norm_sq, Real.sqrt_eq_rpow,
      Real.rpow_two, one_div, MeasureTheory.measureReal_def,
      Real.volume_Ioc, hab] using hholder'
  have hB : 0 ≤ ∫ x in a..b, Complex.normSq (g x) :=
    intervalIntegral.integral_nonneg_of_forall hab
      (fun x ↦ Complex.normSq_nonneg (g x))
  have hlen : 0 ≤ b - a := sub_nonneg.mpr hab
  rw [Complex.normSq_eq_norm_sq]
  calc
    ‖∫ x in a..b, g x‖ ^ 2 ≤
        (Real.sqrt (∫ x in a..b, Complex.normSq (g x)) *
          Real.sqrt (b - a)) ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2
          (hnorm.trans hholder'')
    _ = (b - a) * ∫ x in a..b, Complex.normSq (g x) := by
      rw [mul_pow, Real.sq_sqrt hB, Real.sq_sqrt hlen]
      ring

/-- The denominator-weighted cofactor series is continuous on every
vertical line strictly to the right of one. -/
theorem continuous_mrCofactorLSeries_vertical
    (P : Finset ℕ) {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Continuous (fun t : ℝ ↦
      mrCofactorLSeries P f
        ((sigma : ℂ) + Complex.I * (t : ℂ))) := by
  let c : ℕ → ℂ := fun n ↦
    f n / (mrCommonDenominator P n : ℂ)
  have hmid : 1 < (sigma + 1) / 2 := by linarith
  have hsum : LSeriesSummable c (((sigma + 1) / 2 : ℝ) : ℂ) := by
    exact mrCofactorLSeriesSummable P hbound (by simpa using hmid)
  have habs : LSeries.abscissaOfAbsConv c < (sigma : ℝ) := by
    calc
      LSeries.abscissaOfAbsConv c ≤ (((sigma + 1) / 2 : ℝ) : EReal) := by
        simpa using hsum.abscissaOfAbsConv_le
      _ < (sigma : ℝ) := by exact_mod_cast (by linarith : (sigma + 1) / 2 < sigma)
  have hline : Continuous (fun t : ℝ ↦
      (sigma : ℂ) + Complex.I * (t : ℂ)) := by fun_prop
  unfold mrCofactorLSeries
  change Continuous (fun t : ℝ ↦
    LSeries c ((sigma : ℂ) + Complex.I * (t : ℂ)))
  exact (LSeries_differentiableOn c).continuousOn.comp_continuous hline
    (fun t ↦ by simpa using habs)

/-- The endpoint kernel in the truncated Perron formula. -/
def mrPerronEndpointKernel (y delta u : ℝ) : ℂ :=
  (y : ℂ) ^ ((delta : ℂ) + u * Complex.I) /
    ((delta : ℂ) + u * Complex.I)

theorem continuous_mrPerronEndpointKernel
    {y delta : ℝ} (hy : 0 < y) (hdelta : 0 < delta) :
    Continuous (mrPerronEndpointKernel y delta) := by
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  letI : NeZero (y : ℂ) := ⟨hyC⟩
  unfold mrPerronEndpointKernel
  apply ((continuous_const_cpow (y : ℂ)).comp (by fun_prop)).div
    (by fun_prop)
  intro u hu
  have hre := congrArg Complex.re hu
  simp at hre
  linarith

/-- The exact complete prime/cofactor product on a vertical line. -/
def mrRamarePerronFullProduct
    (sigma : ℝ) (I : ℕ × ℕ) (f : ℕ → ℂ) (t : ℝ) : ℂ :=
  ramarePrimePerronFactorAt sigma I f t *
    mrCofactorLSeries (primesInBlock I) f
      ((sigma : ℂ) + Complex.I * (t : ℂ))

theorem continuous_mrRamarePerronFullProduct
    (I : ℕ × ℕ) {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Continuous (mrRamarePerronFullProduct sigma I f) := by
  unfold mrRamarePerronFullProduct
  exact (continuous_ramarePrimePerronFactorAt sigma I f).mul
    (continuous_mrCofactorLSeries_vertical (primesInBlock I) hbound hsigma)

/-- A finite cofactor rectangle, with exactly the prime factor used in the
complete projector. -/
def mrRamarePerronFiniteProduct
    (sigma : ℝ) (I : ℕ × ℕ) (S : Finset ℕ)
    (f : ℕ → ℂ) (t : ℝ) : ℂ :=
  ramarePrimePerronFactorAt sigma I f t *
    mrCofactorPerronPolynomial (primesInBlock I) S f sigma t

theorem continuous_mrRamarePerronFiniteProduct
    (sigma : ℝ) (I : ℕ × ℕ) (S : Finset ℕ) (f : ℕ → ℂ) :
    Continuous (mrRamarePerronFiniteProduct sigma I S f) := by
  unfold mrRamarePerronFiniteProduct
  exact (continuous_ramarePrimePerronFactorAt sigma I f).mul
    (continuous_mrCofactorPerronPolynomial
      (primesInBlock I) S f sigma)

/-- One endpoint of a translated Perron product projection. -/
def mrRamarePerronEndpointProjection
    (F : ℝ → ℂ) (y t delta U : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
    ∫ u in -U..U, F (t + u) * mrPerronEndpointKernel y delta u

/-- Squared norm of the Perron normalization constant. -/
def mrPerronNormalizationSq : ℝ :=
  ‖((2 * Real.pi : ℝ) : ℂ)⁻¹‖ ^ 2

/-- Exact weighted translated energy for one Perron endpoint.  In
particular the denominator `delta + iu` has not been discarded. -/
def mrRamarePerronWeightedTranslatedEnergy
    (F : ℝ → ℂ) (T U y delta : ℝ) : ℝ :=
  ∫ t in -T..T, ∫ u in -U..U,
    Complex.normSq (F (t + u) * mrPerronEndpointKernel y delta u)

/-- The exact projector is the difference of its two endpoint operators. -/
theorem mrRamareDyadicPerronProductProjection_eq_endpoints
    (I : ℕ × ℕ) (f : ℕ → ℂ) (X : ℕ)
    (rho t delta U : ℝ) :
    mrRamareDyadicPerronProductProjection I f X rho t delta U =
      mrRamarePerronEndpointProjection
          (mrRamarePerronFullProduct (rho + delta) I f)
          (2 * X) t delta U -
        mrRamarePerronEndpointProjection
          (mrRamarePerronFullProduct (rho + delta) I f)
          X t delta U := by
  unfold mrRamareDyadicPerronProductProjection
    mrRamarePerronEndpointProjection mrRamarePerronFullProduct
    mrPerronEndpointKernel
  dsimp only
  apply congrArg₂ (fun x y : ℂ ↦
    ((((2 * Real.pi : ℝ) : ℂ)⁻¹) * x) -
      ((((2 * Real.pi : ℝ) : ℂ)⁻¹) * y))
  · apply intervalIntegral.integral_congr
    intro u hu
    push_cast
    ring
  · apply intervalIntegral.integral_congr
    intro u hu
    ring

/-- Cauchy--Schwarz for one exact Perron endpoint, retaining the complete
denominator-weighted kernel inside the energy. -/
theorem normSq_mrRamarePerronEndpointProjection_le
    {F : ℝ → ℂ} (hF : Continuous F)
    {y t delta U : ℝ} (hy : 0 < y)
    (hdelta : 0 < delta) (hU : 0 ≤ U) :
    Complex.normSq (mrRamarePerronEndpointProjection F y t delta U) ≤
      mrPerronNormalizationSq *
        (2 * U) *
          (∫ u in -U..U,
            Complex.normSq
              (F (t + u) * mrPerronEndpointKernel y delta u)) := by
  let g : ℝ → ℂ := fun u ↦
    F (t + u) * mrPerronEndpointKernel y delta u
  have hg : Continuous g := by
    exact (hF.comp (by fun_prop)).mul
      (continuous_mrPerronEndpointKernel hy hdelta)
  have hcs := normSq_intervalIntegral_le_length_mul_integral_normSq
    hg (show -U ≤ U by linarith)
  unfold mrRamarePerronEndpointProjection
  change Complex.normSq
      (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ u in -U..U, g u)) ≤ _
  have hnormc :
      Complex.normSq ((((2 * Real.pi : ℝ) : ℂ)⁻¹)) =
        mrPerronNormalizationSq := by
    rw [Complex.normSq_eq_norm_sq]
    rfl
  rw [Complex.normSq_mul, hnormc]
  calc
    mrPerronNormalizationSq *
        Complex.normSq (∫ u in -U..U, g u) ≤
      mrPerronNormalizationSq *
        ((U - -U) * (∫ u in -U..U, Complex.normSq (g u))) := by
      exact mul_le_mul_of_nonneg_left hcs (by
        unfold mrPerronNormalizationSq
        positivity)
    _ = mrPerronNormalizationSq *
        (2 * U) * (∫ u in -U..U,
          Complex.normSq
            (F (t + u) * mrPerronEndpointKernel y delta u)) := by
      dsimp only [g]
      ring

theorem continuous_mrRamarePerronEndpointProjection
    {F : ℝ → ℂ} (hF : Continuous F)
    {y delta U : ℝ} (hy : 0 < y) (hdelta : 0 < delta) :
    Continuous (fun t ↦
      mrRamarePerronEndpointProjection F y t delta U) := by
  unfold mrRamarePerronEndpointProjection
  apply continuous_const.mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (hF.comp (by fun_prop)).mul
    ((continuous_mrPerronEndpointKernel hy hdelta).comp (by fun_prop))

theorem continuous_mrRamarePerronWeightedTranslatedIntegrand
    {F : ℝ → ℂ} (hF : Continuous F)
    {y delta U : ℝ} (hy : 0 < y) (hdelta : 0 < delta) :
    Continuous (fun t ↦ ∫ u in -U..U,
      Complex.normSq (F (t + u) * mrPerronEndpointKernel y delta u)) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact Complex.continuous_normSq.comp
    ((hF.comp (by fun_prop)).mul
      ((continuous_mrPerronEndpointKernel hy hdelta).comp (by fun_prop)))

/-- Pointwise L2 majorant for the full dyadic projector. -/
theorem normSq_sub_le_two_mul_add_projection (z w : ℂ) :
    Complex.normSq (z - w) ≤
      2 * (Complex.normSq z + Complex.normSq w) := by
  simp only [Complex.normSq_eq_norm_sq]
  have htri : ‖z - w‖ ≤ ‖z‖ + ‖w‖ := norm_sub_le z w
  nlinarith [norm_nonneg (z - w), norm_nonneg z, norm_nonneg w,
    sq_nonneg (‖z‖ - ‖w‖)]

theorem normSq_mrRamareDyadicPerronProductProjection_le
    (I : ℕ × ℕ) {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X : ℕ} (hX : 0 < X) {rho t delta U : ℝ}
    (hsigma : 1 < rho + delta) (hdelta : 0 < delta)
    (hU : 0 ≤ U) :
    Complex.normSq
        (mrRamareDyadicPerronProductProjection I f X rho t delta U) ≤
      2 * mrPerronNormalizationSq *
        (2 * U) *
          ((∫ u in -U..U, Complex.normSq
              (mrRamarePerronFullProduct (rho + delta) I f (t + u) *
                mrPerronEndpointKernel (2 * X) delta u)) +
            ∫ u in -U..U, Complex.normSq
              (mrRamarePerronFullProduct (rho + delta) I f (t + u) *
                mrPerronEndpointKernel X delta u)) := by
  let F := mrRamarePerronFullProduct (rho + delta) I f
  have hF : Continuous F :=
    continuous_mrRamarePerronFullProduct I hbound hsigma
  have h2X : (0 : ℝ) < 2 * X := by positivity
  have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
  rw [mrRamareDyadicPerronProductProjection_eq_endpoints]
  calc
    Complex.normSq
        (mrRamarePerronEndpointProjection F (2 * X) t delta U -
          mrRamarePerronEndpointProjection F X t delta U) ≤
      2 * (Complex.normSq
          (mrRamarePerronEndpointProjection F (2 * X) t delta U) +
        Complex.normSq
          (mrRamarePerronEndpointProjection F X t delta U)) :=
      normSq_sub_le_two_mul_add_projection _ _
    _ ≤ 2 * mrPerronNormalizationSq *
            (2 * U) *
              ((∫ u in -U..U, Complex.normSq
                  (F (t + u) * mrPerronEndpointKernel (2 * X) delta u)) +
                ∫ u in -U..U, Complex.normSq
                  (F (t + u) * mrPerronEndpointKernel X delta u)) := by
      have h2 := normSq_mrRamarePerronEndpointProjection_le
        hF (t := t) h2X hdelta hU
      have h1 := normSq_mrRamarePerronEndpointProjection_le
        hF (t := t) hXreal hdelta hU
      nlinarith [Complex.normSq_nonneg
        (mrRamarePerronEndpointProjection F (2 * X) t delta U),
        Complex.normSq_nonneg
          (mrRamarePerronEndpointProjection F X t delta U)]
    _ = _ := by rfl

/-- Outer vertical mean-square bound for the exact complete projector.  The
right side is the sum of the two exact translated Perron energies, so its
denominators are available to subsequent shell estimates. -/
theorem integral_normSq_mrRamareDyadicPerronProductProjection_le
    (I : ℕ × ℕ) {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X : ℕ} (hX : 0 < X) {rho delta T U : ℝ}
    (hsigma : 1 < rho + delta) (hdelta : 0 < delta)
    (hT : 0 ≤ T) (hU : 0 ≤ U) :
    (∫ t in -T..T, Complex.normSq
      (mrRamareDyadicPerronProductProjection I f X rho t delta U)) ≤
      2 * mrPerronNormalizationSq * (2 * U) *
        (mrRamarePerronWeightedTranslatedEnergy
            (mrRamarePerronFullProduct (rho + delta) I f)
            T U (2 * X) delta +
          mrRamarePerronWeightedTranslatedEnergy
            (mrRamarePerronFullProduct (rho + delta) I f)
            T U X delta) := by
  let F := mrRamarePerronFullProduct (rho + delta) I f
  let A : ℝ → ℝ := fun t ↦
    ∫ u in -U..U, Complex.normSq
      (F (t + u) * mrPerronEndpointKernel (2 * X) delta u)
  let B : ℝ → ℝ := fun t ↦
    ∫ u in -U..U, Complex.normSq
      (F (t + u) * mrPerronEndpointKernel X delta u)
  let c : ℝ := 2 * mrPerronNormalizationSq * (2 * U)
  have hF : Continuous F :=
    continuous_mrRamarePerronFullProduct I hbound hsigma
  have h2X : (0 : ℝ) < 2 * X := by positivity
  have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
  have hA : Continuous A :=
    continuous_mrRamarePerronWeightedTranslatedIntegrand
      hF h2X hdelta
  have hB : Continuous B :=
    continuous_mrRamarePerronWeightedTranslatedIntegrand
      hF hXreal hdelta
  have hproj : Continuous (fun t ↦
      mrRamareDyadicPerronProductProjection I f X rho t delta U) := by
    rw [funext (fun t ↦
      mrRamareDyadicPerronProductProjection_eq_endpoints
        I f X rho t delta U)]
    exact (continuous_mrRamarePerronEndpointProjection
      hF h2X hdelta).sub
        (continuous_mrRamarePerronEndpointProjection hF hXreal hdelta)
  have hlhs : IntervalIntegrable (fun t ↦ Complex.normSq
      (mrRamareDyadicPerronProductProjection I f X rho t delta U))
      MeasureTheory.volume (-T) T :=
    (Complex.continuous_normSq.comp hproj).intervalIntegrable _ _
  have hrhs : IntervalIntegrable (fun t ↦ c * (A t + B t))
      MeasureTheory.volume (-T) T :=
    (continuous_const.mul (hA.add hB)).intervalIntegrable _ _
  have hpoint : ∀ t ∈ Set.Icc (-T) T,
      Complex.normSq
          (mrRamareDyadicPerronProductProjection I f X rho t delta U) ≤
        c * (A t + B t) := by
    intro t ht
    exact normSq_mrRamareDyadicPerronProductProjection_le
      I hbound hX hsigma hdelta hU
  have hmono := intervalIntegral.integral_mono_on
    (show -T ≤ T by linarith) hlhs hrhs hpoint
  calc
    (∫ t in -T..T, Complex.normSq
        (mrRamareDyadicPerronProductProjection I f X rho t delta U)) ≤
      ∫ t in -T..T, c * (A t + B t) := hmono
    _ = c * ((∫ t in -T..T, A t) + ∫ t in -T..T, B t) := by
      rw [intervalIntegral.integral_const_mul]
      rw [intervalIntegral.integral_add
        (hA.intervalIntegrable _ _) (hB.intervalIntegrable _ _)]
    _ = _ := by
      rfl

/-- Translation averaging over `[-U,U]` costs only its length after the
outer interval is enlarged from `[-T,T]` to `[-(T+U),T+U]`. -/
theorem intervalIntegral_translated_normSq_le
    {F : ℝ → ℂ} (hF : Continuous F)
    {T U : ℝ} (hT : 0 ≤ T) (hU : 0 ≤ U) :
    (∫ t in -T..T, ∫ u in -U..U,
      Complex.normSq (F (t + u))) ≤
      (2 * U) * ∫ v in -(T + U)..T + U, Complex.normSq (F v) := by
  let H : ℝ → ℝ → ℝ := fun t u ↦ Complex.normSq (F (t + u))
  let E : ℝ := ∫ v in -(T + U)..T + U, Complex.normSq (F v)
  have hH : Continuous H.uncurry := by
    exact Complex.continuous_normSq.comp (hF.comp (by fun_prop))
  have hrect : MeasureTheory.IntegrableOn H.uncurry
      (Set.uIoc (-T) T ×ˢ Set.uIoc (-U) U) :=
    (hH.continuousOn.integrableOn_compact
      (isCompact_uIcc.prod isCompact_uIcc)).mono_set
        (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
  have hswap :
      (∫ t in -T..T, ∫ u in -U..U, H t u) =
        ∫ u in -U..U, ∫ t in -T..T, H t u :=
    MeasureTheory.intervalIntegral_intervalIntegral_swap hrect
  have hbase : Continuous (fun v ↦ Complex.normSq (F v)) :=
    Complex.continuous_normSq.comp hF
  have hEint : IntervalIntegrable (fun v ↦ Complex.normSq (F v))
      MeasureTheory.volume (-(T + U)) (T + U) :=
    hbase.intervalIntegrable _ _
  have hinner : ∀ u ∈ Set.Icc (-U) U,
      (∫ t in -T..T, H t u) ≤ E := by
    intro u hu
    rcases hu with ⟨huLower, huUpper⟩
    rw [show (∫ t in -T..T, H t u) =
        ∫ v in -T + u..T + u, Complex.normSq (F v) by
      exact intervalIntegral.integral_comp_add_right
        (fun v ↦ Complex.normSq (F v)) u]
    exact intervalIntegral.integral_mono_interval
      (by linarith) (by linarith) (by linarith)
      (MeasureTheory.ae_of_all _ (fun v ↦ Complex.normSq_nonneg (F v)))
      hEint
  have hleftCont : Continuous (fun u ↦ ∫ t in -T..T, H t u) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact Complex.continuous_normSq.comp (hF.comp (by fun_prop))
  have hmono := intervalIntegral.integral_mono_on
    (show -U ≤ U by linarith)
    (hleftCont.intervalIntegrable _ _)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ E)
      MeasureTheory.volume (-U) U) hinner
  calc
    (∫ t in -T..T, ∫ u in -U..U,
        Complex.normSq (F (t + u))) =
      ∫ u in -U..U, ∫ t in -T..T, H t u := by
        change (∫ t in -T..T, ∫ u in -U..U, H t u) = _
        exact hswap
    _ ≤ ∫ _u in -U..U, E := hmono
    _ = (2 * U) * E := by
      rw [intervalIntegral.integral_const]
      ring
    _ = _ := by rfl

/-- Uniform bound for the exact Perron endpoint kernel. -/
theorem normSq_mrPerronEndpointKernel_le
    {y delta : ℝ} (hy : 0 < y) (hdelta : 0 < delta) (u : ℝ) :
    Complex.normSq (mrPerronEndpointKernel y delta u) ≤
      (y ^ delta) ^ 2 / delta ^ 2 := by
  have hden : delta ≤ ‖(delta : ℂ) + (u : ℂ) * Complex.I‖ := by
    calc
      delta = (((delta : ℂ) + (u : ℂ) * Complex.I)).re := by simp
      _ ≤ ‖(delta : ℂ) + (u : ℂ) * Complex.I‖ := Complex.re_le_norm _
  have hdenSq : delta ^ 2 ≤
      ‖(delta : ℂ) + (u : ℂ) * Complex.I‖ ^ 2 :=
    (sq_le_sq₀ hdelta.le (norm_nonneg _)).2 hden
  unfold mrPerronEndpointKernel
  rw [Complex.normSq_eq_norm_sq, norm_div,
    Complex.norm_cpow_eq_rpow_re_of_pos hy]
  have hre : (((delta : ℂ) + (u : ℂ) * Complex.I)).re = delta := by
    simp
  rw [hre]
  rw [div_pow]
  exact div_le_div_of_nonneg_left (sq_nonneg (y ^ delta))
    (sq_pos_of_pos hdelta) hdenSq

/-- Cycle-free translated-energy bridge for any continuous vertical
product.  This is the form consumed by the full-cofactor power-block energy
module. -/
theorem mrRamarePerronWeightedTranslatedEnergy_le_verticalEnergy
    {F : ℝ → ℂ} (hF : Continuous F)
    {T U y delta : ℝ} (hT : 0 ≤ T) (hU : 0 ≤ U)
    (hy : 0 < y) (hdelta : 0 < delta) :
    mrRamarePerronWeightedTranslatedEnergy F T U y delta ≤
      ((y ^ delta) ^ 2 / delta ^ 2) * (2 * U) *
        ∫ v in -(T + U)..T + U, Complex.normSq (F v) := by
  let K : ℝ := (y ^ delta) ^ 2 / delta ^ 2
  let A : ℝ → ℝ := fun t ↦ ∫ u in -U..U,
    Complex.normSq (F (t + u) * mrPerronEndpointKernel y delta u)
  let B : ℝ → ℝ := fun t ↦ ∫ u in -U..U,
    Complex.normSq (F (t + u))
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hA : Continuous A :=
    continuous_mrRamarePerronWeightedTranslatedIntegrand
      hF hy hdelta
  have hB : Continuous B := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact Complex.continuous_normSq.comp (hF.comp (by fun_prop))
  have hinner : ∀ t ∈ Set.Icc (-T) T, A t ≤ K * B t := by
    intro t ht
    dsimp only [A, B]
    rw [← intervalIntegral.integral_const_mul]
    have hshift : Continuous (fun u : ℝ ↦ t + u) :=
      continuous_const.add continuous_id
    apply intervalIntegral.integral_mono_on (show -U ≤ U by linarith)
      ((Complex.continuous_normSq.comp
        ((hF.comp hshift).mul
          (continuous_mrPerronEndpointKernel hy hdelta))).intervalIntegrable _ _)
      ((continuous_const.mul
        (Complex.continuous_normSq.comp (hF.comp hshift))).intervalIntegrable _ _)
    intro u hu
    change Complex.normSq
        (F (t + u) * mrPerronEndpointKernel y delta u) ≤
      K * Complex.normSq (F (t + u))
    rw [Complex.normSq_mul]
    simpa only [K, mul_comm] using
      (mul_le_mul_of_nonneg_left
        (normSq_mrPerronEndpointKernel_le hy hdelta u)
        (Complex.normSq_nonneg (F (t + u))))
  have hAint : IntervalIntegrable A MeasureTheory.volume (-T) T :=
    hA.intervalIntegrable _ _
  have hKBint : IntervalIntegrable (fun t ↦ K * B t)
      MeasureTheory.volume (-T) T :=
    (continuous_const.mul hB).intervalIntegrable _ _
  have houter := intervalIntegral.integral_mono_on
    (show -T ≤ T by linarith) hAint hKBint hinner
  have htranslated := intervalIntegral_translated_normSq_le hF hT hU
  change (∫ t in -T..T, A t) ≤
    K * (2 * U) * ∫ v in -(T + U)..T + U, Complex.normSq (F v)
  calc
    (∫ t in -T..T, A t) ≤ ∫ t in -T..T, K * B t := houter
    _ = K * ∫ t in -T..T, B t := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ K * ((2 * U) *
        ∫ v in -(T + U)..T + U, Complex.normSq (F v)) :=
      mul_le_mul_of_nonneg_left htranslated hK
    _ = _ := by ring

/-- The exact translated energy of a finite prime/cofactor rectangle is
controlled by the already-estimated rectangular product energy. -/
theorem mrRamarePerronWeightedTranslatedEnergy_finite_le
    (sigma : ℝ) (I : ℕ × ℕ) (S : Finset ℕ) (f : ℕ → ℂ)
    {T U y delta : ℝ} (hT : 0 ≤ T) (hU : 0 ≤ U)
    (hy : 0 < y) (hdelta : 0 < delta) :
    mrRamarePerronWeightedTranslatedEnergy
        (mrRamarePerronFiniteProduct sigma I S f) T U y delta ≤
      ((y ^ delta) ^ 2 / delta ^ 2) * (2 * U) *
        ramareTruncationProductEnergy sigma I S f (T + U) := by
  let F := mrRamarePerronFiniteProduct sigma I S f
  let K : ℝ := (y ^ delta) ^ 2 / delta ^ 2
  let A : ℝ → ℝ := fun t ↦ ∫ u in -U..U,
    Complex.normSq (F (t + u) * mrPerronEndpointKernel y delta u)
  let B : ℝ → ℝ := fun t ↦ ∫ u in -U..U,
    Complex.normSq (F (t + u))
  have hF : Continuous F :=
    continuous_mrRamarePerronFiniteProduct sigma I S f
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hA : Continuous A :=
    continuous_mrRamarePerronWeightedTranslatedIntegrand
      hF hy hdelta
  have hB : Continuous B := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact Complex.continuous_normSq.comp (hF.comp (by fun_prop))
  have hinner : ∀ t ∈ Set.Icc (-T) T, A t ≤ K * B t := by
    intro t ht
    dsimp only [A, B]
    rw [← intervalIntegral.integral_const_mul]
    have hshift : Continuous (fun u : ℝ ↦ t + u) :=
      continuous_const.add continuous_id
    apply intervalIntegral.integral_mono_on (show -U ≤ U by linarith)
      (by
        exact ((Complex.continuous_normSq.comp
          ((hF.comp hshift).mul
            (continuous_mrPerronEndpointKernel hy hdelta))).intervalIntegrable _ _))
      (by
        exact (continuous_const.mul
          (Complex.continuous_normSq.comp (hF.comp hshift))).intervalIntegrable _ _)
    intro u hu
    rw [Complex.normSq_mul]
    simpa only [K, mul_comm] using
      (mul_le_mul_of_nonneg_left
        (normSq_mrPerronEndpointKernel_le hy hdelta u)
        (Complex.normSq_nonneg (F (t + u))))
  have hAint : IntervalIntegrable A MeasureTheory.volume (-T) T :=
    hA.intervalIntegrable _ _
  have hKBint : IntervalIntegrable (fun t ↦ K * B t)
      MeasureTheory.volume (-T) T :=
    (continuous_const.mul hB).intervalIntegrable _ _
  have houter := intervalIntegral.integral_mono_on
    (show -T ≤ T by linarith)
    hAint hKBint hinner
  have htranslated := intervalIntegral_translated_normSq_le
    hF hT hU
  change (∫ t in -T..T, A t) ≤
    K * (2 * U) * ∫ v in -(T + U)..T + U, Complex.normSq (F v)
  calc
    (∫ t in -T..T, A t) ≤ ∫ t in -T..T, K * B t := houter
    _ = K * ∫ t in -T..T, B t := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ K * ((2 * U) *
        ∫ v in -(T + U)..T + U, Complex.normSq (F v)) :=
      mul_le_mul_of_nonneg_left htranslated hK
    _ = _ := by ring

/-- Generic outer L2 bound for the difference of two exact Perron endpoint
operators. -/
theorem integral_normSq_mrRamarePerronEndpointDifference_le
    {F : ℝ → ℂ} (hF : Continuous F)
    {T U y₁ y₂ delta : ℝ}
    (hT : 0 ≤ T) (hU : 0 ≤ U)
    (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) (hdelta : 0 < delta) :
    (∫ t in -T..T, Complex.normSq
      (mrRamarePerronEndpointProjection F y₂ t delta U -
        mrRamarePerronEndpointProjection F y₁ t delta U)) ≤
      2 * mrPerronNormalizationSq * (2 * U) *
        (mrRamarePerronWeightedTranslatedEnergy F T U y₂ delta +
          mrRamarePerronWeightedTranslatedEnergy F T U y₁ delta) := by
  let A : ℝ → ℝ := fun t ↦ ∫ u in -U..U,
    Complex.normSq (F (t + u) * mrPerronEndpointKernel y₂ delta u)
  let B : ℝ → ℝ := fun t ↦ ∫ u in -U..U,
    Complex.normSq (F (t + u) * mrPerronEndpointKernel y₁ delta u)
  let c : ℝ := 2 * mrPerronNormalizationSq * (2 * U)
  have hA : Continuous A :=
    continuous_mrRamarePerronWeightedTranslatedIntegrand hF hy₂ hdelta
  have hB : Continuous B :=
    continuous_mrRamarePerronWeightedTranslatedIntegrand hF hy₁ hdelta
  have hP₂ : Continuous (fun t ↦
      mrRamarePerronEndpointProjection F y₂ t delta U) :=
    continuous_mrRamarePerronEndpointProjection hF hy₂ hdelta
  have hP₁ : Continuous (fun t ↦
      mrRamarePerronEndpointProjection F y₁ t delta U) :=
    continuous_mrRamarePerronEndpointProjection hF hy₁ hdelta
  have hlhs : IntervalIntegrable (fun t ↦ Complex.normSq
      (mrRamarePerronEndpointProjection F y₂ t delta U -
        mrRamarePerronEndpointProjection F y₁ t delta U))
      MeasureTheory.volume (-T) T :=
    (Complex.continuous_normSq.comp (hP₂.sub hP₁)).intervalIntegrable _ _
  have hrhs : IntervalIntegrable (fun t ↦ c * (A t + B t))
      MeasureTheory.volume (-T) T :=
    (continuous_const.mul (hA.add hB)).intervalIntegrable _ _
  have hpoint : ∀ t ∈ Set.Icc (-T) T,
      Complex.normSq
          (mrRamarePerronEndpointProjection F y₂ t delta U -
            mrRamarePerronEndpointProjection F y₁ t delta U) ≤
        c * (A t + B t) := by
    intro t ht
    have hsub := normSq_sub_le_two_mul_add_projection
      (mrRamarePerronEndpointProjection F y₂ t delta U)
      (mrRamarePerronEndpointProjection F y₁ t delta U)
    have h₂ := normSq_mrRamarePerronEndpointProjection_le
      hF (t := t) hy₂ hdelta hU
    have h₁ := normSq_mrRamarePerronEndpointProjection_le
      hF (t := t) hy₁ hdelta hU
    dsimp only [c, A, B]
    nlinarith [hsub, h₂, h₁]
  have hmono := intervalIntegral.integral_mono_on
    (show -T ≤ T by linarith) hlhs hrhs hpoint
  calc
    (∫ t in -T..T, Complex.normSq
        (mrRamarePerronEndpointProjection F y₂ t delta U -
          mrRamarePerronEndpointProjection F y₁ t delta U)) ≤
      ∫ t in -T..T, c * (A t + B t) := hmono
    _ = c * ((∫ t in -T..T, A t) + ∫ t in -T..T, B t) := by
      rw [intervalIntegral.integral_const_mul]
      rw [intervalIntegral.integral_add
        (hA.intervalIntegrable _ _) (hB.intervalIntegrable _ _)]
    _ = _ := by rfl

/-- Finite-cofactor analogue of the dyadic product projector. -/
def mrRamareDyadicPerronFiniteProductProjection
    (sigma : ℝ) (I : ℕ × ℕ) (S : Finset ℕ) (f : ℕ → ℂ)
    (X : ℕ) (t delta U : ℝ) : ℂ :=
  mrRamarePerronEndpointProjection
      (mrRamarePerronFiniteProduct sigma I S f)
        ((2 * X : ℕ) : ℝ) t delta U -
    mrRamarePerronEndpointProjection
      (mrRamarePerronFiniteProduct sigma I S f) X t delta U

/-- The finite dyadic projector is controlled directly by the product
energy already bounded in `MRPowerBlockProductEnergy`. -/
theorem integral_normSq_mrRamareDyadicPerronFiniteProductProjection_le
    (sigma : ℝ) (I : ℕ × ℕ) (S : Finset ℕ) (f : ℕ → ℂ)
    {X : ℕ} (hX : 0 < X) {T U delta : ℝ}
    (hT : 0 ≤ T) (hU : 0 ≤ U) (hdelta : 0 < delta) :
    (∫ t in -T..T, Complex.normSq
      (mrRamareDyadicPerronFiniteProductProjection
        sigma I S f X t delta U)) ≤
      2 * mrPerronNormalizationSq * (2 * U) ^ 2 *
        (((((2 * X : ℕ) : ℝ) ^ delta) ^ 2 / delta ^ 2) +
          (((X : ℝ) ^ delta) ^ 2 / delta ^ 2)) *
        ramareTruncationProductEnergy sigma I S f (T + U) := by
  let F := mrRamarePerronFiniteProduct sigma I S f
  let E := ramareTruncationProductEnergy sigma I S f (T + U)
  let K₂ : ℝ := ((((2 * X : ℕ) : ℝ) ^ delta) ^ 2 / delta ^ 2)
  let K₁ : ℝ := (((X : ℝ) ^ delta) ^ 2 / delta ^ 2)
  have hF : Continuous F :=
    continuous_mrRamarePerronFiniteProduct sigma I S f
  have h2X : (0 : ℝ) < (2 * X : ℕ) := by exact_mod_cast (by omega : 0 < 2 * X)
  have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
  have hgeneric := integral_normSq_mrRamarePerronEndpointDifference_le
    hF hT hU hXreal h2X hdelta
  have hweighted₂ := mrRamarePerronWeightedTranslatedEnergy_finite_le
    sigma I S f hT hU h2X hdelta
  have hweighted₁ := mrRamarePerronWeightedTranslatedEnergy_finite_le
    sigma I S f hT hU hXreal hdelta
  have hc : 0 ≤ 2 * mrPerronNormalizationSq * (2 * U) := by
    unfold mrPerronNormalizationSq
    positivity
  unfold mrRamareDyadicPerronFiniteProductProjection
  change (∫ t in -T..T, Complex.normSq
      (mrRamarePerronEndpointProjection F ((2 * X : ℕ) : ℝ) t delta U -
        mrRamarePerronEndpointProjection F X t delta U)) ≤
    2 * mrPerronNormalizationSq * (2 * U) ^ 2 * (K₂ + K₁) * E
  calc
    _ ≤ 2 * mrPerronNormalizationSq * (2 * U) *
        (mrRamarePerronWeightedTranslatedEnergy F T U
            ((2 * X : ℕ) : ℝ) delta +
          mrRamarePerronWeightedTranslatedEnergy F T U X delta) := hgeneric
    _ ≤ 2 * mrPerronNormalizationSq * (2 * U) *
        (K₂ * (2 * U) * E + K₁ * (2 * U) * E) := by
      apply mul_le_mul_of_nonneg_left _ hc
      exact add_le_add hweighted₂ hweighted₁
    _ = _ := by ring

/-- Uniform power-block endpoint: the finite dyadic Perron projector is
bounded by the complete good/bad product-energy expression, whose cofactor
term contains the Halász exponential decay. -/
theorem exists_uniform_integral_normSq_mrRamareDyadicPerronFiniteProductProjection_le :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {I : ℕ × ℕ} {K : ℕ},
        3 ≤ I.1 → I.1 ≤ I.2 → 0 < K →
        I.2 ≤ (I.1 - 1) ^ K →
      ∀ {S : Finset ℕ} {f : ℕ → ℂ} {A X Y k : ℕ}
        {T U V delta : ℝ},
        IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) →
        (∀ n ∈ S, 0 < n) →
        2 ≤ Y → Y < X →
        MRArchimedeanNonpretentious f A X →
        0 < k → 0 ≤ T → 0 ≤ U → T + U ≤ X →
        0 < V → 0 < delta →
        (∫ t in -T..T, Complex.normSq
          (mrRamareDyadicPerronFiniteProductProjection
            (EulerResidue.taoExponent Y) I S f X t delta U)) ≤
          2 * mrPerronNormalizationSq * (2 * U) ^ 2 *
            (((((2 * X : ℕ) : ℝ) ^ delta) ^ 2 / delta ^ 2) +
              (((X : ℝ) ^ delta) ^ 2 / delta ^ 2)) *
            mrPowerBlockProductEnergyBound
              C K A X Y k I S f (T + U) V := by
  obtain ⟨C, hC, henergy⟩ :=
    exists_uniform_ramareTruncationProductEnergy_powerBlock_le
  refine ⟨C, hC, ?_⟩
  intro I K hlo hI hK hpow S f A X Y k T U V delta
    hmul hbound hSpos hY hYX hnonpret hk hT hU hTUX hV hdelta
  have hX : 0 < X := by omega
  have hprojection :=
    integral_normSq_mrRamareDyadicPerronFiniteProductProjection_le
      (EulerResidue.taoExponent Y) I S f hX hT hU hdelta
  have hproduct := henergy hlo hI hK hpow hmul hbound hSpos
    hY hYX hnonpret hk (by linarith) hTUX hV
  let D : ℝ := 2 * mrPerronNormalizationSq * (2 * U) ^ 2 *
    (((((2 * X : ℕ) : ℝ) ^ delta) ^ 2 / delta ^ 2) +
      (((X : ℝ) ^ delta) ^ 2 / delta ^ 2))
  have hD : 0 ≤ D := by
    dsimp only [D]
    unfold mrPerronNormalizationSq
    positivity
  exact hprojection.trans (mul_le_mul_of_nonneg_left hproduct hD)

end

end Erdos67b
