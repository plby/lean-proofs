import ErdosProblems.Erdos520.HarperFejer
import ErdosProblems.Erdos520.HarperGaussianCDF
import ErdosProblems.Erdos520.HarperQuarticBudget

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators Interval

namespace Erdos
namespace Problem520

/-!
# The Fejér--Esseen smoothed-CDF bridge

This file packages the last analytic step of the one-block Gaussian
replacement.  The exact inversion identity is isolated as a named proposition;
everything after that identity, including the norm estimate, the scheduled
block specialization, the Fejér tail loss, and Gaussian CDF regularity, is
proved here with explicit constants.
-/

/-- The Fourier integrand in the Fejér-smoothed CDF inversion formula.  Its
value at zero fills the removable singularity; only its integral matters. -/
noncomputable def harperFejerCDFInversionIntegrand
    (phi psi : ℝ → ℂ) (T x t : ℝ) : ℂ :=
  if t = 0 then 0 else
    Complex.exp (((-t * x : ℝ) : ℂ) * Complex.I) *
      (phi t - psi t) * (harperFejerTriangle (T⁻¹ * t) : ℂ) /
        (-((t : ℂ) * Complex.I))

/-- The precise inversion statement needed by the smoothing argument.  This
is deliberately a proposition rather than an opaque numerical hypothesis:
it records the complete identity, including normalization and Fourier
orientation, that remains to be discharged analytically. -/
def HarperFejerSmoothedCDFIdentity
    (mu nu : Measure ℝ) (T : ℝ) : Prop :=
  ∀ x : ℝ,
    (((harperSmooth (harperFejerMeasureScaled T) (cdf mu) x -
        harperSmooth (harperFejerMeasureScaled T) (cdf nu) x : ℝ) : ℂ)) =
      (((2 * Real.pi : ℝ)⁻¹ : ℝ) : ℂ) *
        ∫ t in Icc (-T) T,
          harperFejerCDFInversionIntegrand (charFun mu) (charFun nu) T x t

theorem norm_harperFejerCDFInversionIntegrand_le
    (phi psi : ℝ → ℂ) (T x t : ℝ) :
    ‖harperFejerCDFInversionIntegrand phi psi T x t‖ ≤
      harperEsseenIntegrand phi psi t := by
  by_cases ht : t = 0
  · subst t
    simp [harperFejerCDFInversionIntegrand, harperEsseenIntegrand]
  · have htAbs : 0 < |t| := abs_pos.mpr ht
    have htri0 : 0 ≤ harperFejerTriangle (T⁻¹ * t) :=
      harperFejerTriangle_nonneg _
    have htri1 : harperFejerTriangle (T⁻¹ * t) ≤ 1 :=
      harperFejerTriangle_le_one _
    rw [harperFejerCDFInversionIntegrand, if_neg ht,
      harperEsseenIntegrand, if_neg ht, norm_div, norm_mul, norm_mul,
      Complex.norm_exp_ofReal_mul_I, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg htri0, norm_neg, norm_mul,
      Complex.norm_real, Complex.norm_I, Real.norm_eq_abs, mul_one]
    rw [div_le_div_iff_of_pos_right htAbs]
    calc
      1 * ‖phi t - psi t‖ * harperFejerTriangle (T⁻¹ * t) ≤
          ‖phi t - psi t‖ * 1 := by
        simpa only [one_mul] using!
          mul_le_mul_of_nonneg_left htri1 (norm_nonneg (phi t - psi t))
      _ = ‖phi t - psi t‖ := by ring

/-- Local integrability of the Esseen quotient under the cubic--quartic
estimate used for Harper blocks. -/
theorem integrableOn_harperEsseenIntegrand_of_cubic_quartic
    {phi psi : ℝ → ℂ} {A B T : ℝ}
    (hphi : Continuous phi) (hpsi : Continuous psi)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hphipsi : ∀ t, |t| ≤ T →
      ‖phi t - psi t‖ ≤ A * |t| ^ 3 + B * |t| ^ 4) :
    IntegrableOn (harperEsseenIntegrand phi psi) (Icc (-T) T) := by
  let C : ℝ := A * T ^ 2 + B * T ^ 3
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hpoint : ∀ t ∈ Icc (-T) T,
      harperEsseenIntegrand phi psi t ≤ C := by
    intro t ht
    have htAbs : |t| ≤ T := by
      rw [abs_le]
      exact ⟨by linarith [ht.1], ht.2⟩
    calc
      harperEsseenIntegrand phi psi t ≤
          A * |t| ^ 2 + B * |t| ^ 3 :=
        harperEsseenIntegrand_le_of_cubic_quartic htAbs
          (hphipsi t htAbs)
      _ ≤ A * T ^ 2 + B * T ^ 3 := by gcongr
      _ = C := rfl
  rw [IntegrableOn]
  exact (integrable_const (μ := volume.restrict (Icc (-T) T)) C).mono'
    (measurable_harperEsseenIntegrand hphi.measurable hpsi.measurable).aestronglyMeasurable.restrict
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [Real.norm_eq_abs,
        abs_of_nonneg (harperEsseenIntegrand_nonneg phi psi t)]
      exact hpoint t ht)

/-- The exact inversion identity implies the usual low-frequency Esseen
bound for the Fejér-smoothed CDFs. -/
theorem abs_harperSmooth_fejer_sub_le_of_identity
    (mu nu : Measure ℝ) (T : ℝ)
    (hidentity : HarperFejerSmoothedCDFIdentity mu nu T)
    (hInt : IntegrableOn
      (harperEsseenIntegrand (charFun mu) (charFun nu)) (Icc (-T) T))
    (x : ℝ) :
    |harperSmooth (harperFejerMeasureScaled T) (cdf mu) x -
        harperSmooth (harperFejerMeasureScaled T) (cdf nu) x| ≤
      (2 * Real.pi)⁻¹ *
        harperEsseenIntegral (charFun mu) (charFun nu) T := by
  have hnorm :
      ‖∫ t in Icc (-T) T,
          harperFejerCDFInversionIntegrand
            (charFun mu) (charFun nu) T x t‖ ≤
        ∫ t in Icc (-T) T,
          harperEsseenIntegrand (charFun mu) (charFun nu) t := by
    apply norm_integral_le_of_norm_le hInt
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact norm_harperFejerCDFInversionIntegrand_le
      (charFun mu) (charFun nu) T x t
  have hcoef : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  have hid := hidentity x
  rw [← Real.norm_eq_abs, ← Complex.norm_real]
  rw [hid,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcoef]
  unfold harperEsseenIntegral
  exact mul_le_mul_of_nonneg_left hnorm hcoef

/-! ## Scheduled Harper-block specialization -/

/-- Pointwise law-level characteristic estimate with the summable quartic
coefficient already absorbed into the lower block scale. -/
theorem norm_charFun_harperScheduledBlockLaw_sub_gaussian_le_explicit
    (y j : ℕ) (t u T v : ℝ) (hv : |v| ≤ T)
    (hfrequency : 2 * T ≤ Real.sqrt (harperBlockEndpoint j : ℝ)) :
    ‖charFun (harperCenteredLinearBlockLaw y
          (harperScheduledPrimeBlock y j) t u) v -
        charFun (harperGaussianBlockLaw y
          (harperScheduledPrimeBlock y j) t u) v‖ ≤
      (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹ *
        (16 * |v| ^ 3 + (1 / 2 : ℝ) * |v| ^ 4) := by
  have hsmall : ∀ p ∈ harperScheduledPrimeBlock y j,
      |v| * (2 * (Real.sqrt (p.1 : ℝ))⁻¹) ≤ 1 := by
    intro p hp
    have hpA := (mem_harperScheduledPrimeBlock p).mp hp |>.1
    have hp0 : 0 < p.1 := by
      have := sixteen_le_prime_of_mem_harperScheduledPrimeBlock hp
      omega
    have hpR : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast hp0
    have hsqrtp : 0 < Real.sqrt (p.1 : ℝ) := Real.sqrt_pos.2 hpR
    have hsqrtMono : Real.sqrt (harperBlockEndpoint j : ℝ) ≤
        Real.sqrt (p.1 : ℝ) := by
      exact Real.sqrt_le_sqrt (by exact_mod_cast hpA.le)
    have htwo : 2 * |v| ≤ Real.sqrt (p.1 : ℝ) := by
      calc
        2 * |v| ≤ 2 * T := mul_le_mul_of_nonneg_left hv (by norm_num)
        _ ≤ Real.sqrt (harperBlockEndpoint j : ℝ) := hfrequency
        _ ≤ Real.sqrt (p.1 : ℝ) := hsqrtMono
    rw [show |v| * (2 * (Real.sqrt (p.1 : ℝ))⁻¹) =
        (2 * |v|) / Real.sqrt (p.1 : ℝ) by ring]
    exact (div_le_one hsqrtp).2 htwo
  have hquad : ∀ p ∈ harperScheduledPrimeBlock y j,
      harperPrimeGaussianQuadratic p.1 t u v ≤ 1 / 2 := by
    intro p hp
    have hpA := (mem_harperScheduledPrimeBlock p).mp hp |>.1
    have hp0 : 0 < p.1 := by
      have := sixteen_le_prime_of_mem_harperScheduledPrimeBlock hp
      omega
    have hpR : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast hp0
    have hsqrtp : 0 < Real.sqrt (p.1 : ℝ) := Real.sqrt_pos.2 hpR
    have hsqrtMono : Real.sqrt (harperBlockEndpoint j : ℝ) ≤
        Real.sqrt (p.1 : ℝ) := by
      exact Real.sqrt_le_sqrt (by exact_mod_cast hpA.le)
    have hvroot : |v| ≤ Real.sqrt (p.1 : ℝ) := by
      calc
        |v| ≤ T := hv
        _ ≤ 2 * T := by
          have : 0 ≤ T := (abs_nonneg v).trans hv
          linarith
        _ ≤ Real.sqrt (harperBlockEndpoint j : ℝ) := hfrequency
        _ ≤ Real.sqrt (p.1 : ℝ) := hsqrtMono
    have hvSq : v ^ 2 ≤ (p.1 : ℝ) := by
      rw [← Real.sq_sqrt hpR.le, ← sq_abs v]
      exact pow_le_pow_left₀ (abs_nonneg v) hvroot 2
    have hvar := harperCenteredLinearPrimeVariance_le_inv hp0 t u
    unfold harperPrimeGaussianQuadratic
    calc
      v ^ 2 * harperCenteredLinearPrimeVariance p.1 t u / 2 ≤
          v ^ 2 * (p.1 : ℝ)⁻¹ / 2 := by gcongr
      _ ≤ 1 / 2 := by
        rw [div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)]
        rw [mul_inv_le_iff₀ hpR]
        simpa using! hvSq
  have hbase :=
    norm_charFun_harperScheduledBlockLaw_sub_gaussian_le
      y j t u v hsmall hquad
  have hbudget := harperBlockGaussianQuarticBudget_scheduled_le y j t u
  calc
    ‖charFun (harperCenteredLinearBlockLaw y
          (harperScheduledPrimeBlock y j) t u) v -
        charFun (harperGaussianBlockLaw y
          (harperScheduledPrimeBlock y j) t u) v‖ ≤
      (16 * (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹) * |v| ^ 3 +
        harperBlockGaussianQuarticBudget y
          (harperScheduledPrimeBlock y j) t u * |v| ^ 4 := hbase
    _ ≤ (16 * (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹) * |v| ^ 3 +
        ((1 / 2 : ℝ) *
          (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹) * |v| ^ 4 := by
      gcongr
    _ = (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹ *
        (16 * |v| ^ 3 + (1 / 2 : ℝ) * |v| ^ 4) := by ring

theorem integrableOn_harperScheduledBlockLawEsseenIntegrand
    (y j : ℕ) (t u T : ℝ) (hT : 0 ≤ T)
    (hfrequency : 2 * T ≤ Real.sqrt (harperBlockEndpoint j : ℝ)) :
    IntegrableOn
      (harperEsseenIntegrand
        (charFun (harperCenteredLinearBlockLaw y
          (harperScheduledPrimeBlock y j) t u))
        (charFun (harperGaussianBlockLaw y
          (harperScheduledPrimeBlock y j) t u)))
      (Icc (-T) T) := by
  refine integrableOn_harperEsseenIntegrand_of_cubic_quartic
      continuous_charFun continuous_charFun
      (A := 16 * (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹)
      (B := (1 / 2 : ℝ) *
        (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹) ?_ ?_ hT ?_
  · exact mul_nonneg (by norm_num)
      (inv_nonneg.mpr (Real.sqrt_nonneg _))
  · exact mul_nonneg (by norm_num)
      (inv_nonneg.mpr (Real.sqrt_nonneg _))
  · intro v hv
    have h := norm_charFun_harperScheduledBlockLaw_sub_gaussian_le_explicit
      y j t u T v hv hfrequency
    calc
      ‖charFun (harperCenteredLinearBlockLaw y
            (harperScheduledPrimeBlock y j) t u) v -
          charFun (harperGaussianBlockLaw y
            (harperScheduledPrimeBlock y j) t u) v‖ ≤
        (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹ *
          (16 * |v| ^ 3 + (1 / 2 : ℝ) * |v| ^ 4) := h
      _ = (16 * (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹) * |v| ^ 3 +
          ((1 / 2 : ℝ) *
            (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹) * |v| ^ 4 := by ring

/-- Fully explicit smoothed-CDF estimate for one scheduled block, conditional
only on the exact Fejér inversion identity. -/
theorem abs_harperScheduledBlockSmooth_sub_gaussian_le_of_identity
    (y j : ℕ) (t u T : ℝ) (hT : 0 ≤ T)
    (hfrequency : 2 * T ≤ Real.sqrt (harperBlockEndpoint j : ℝ))
    (hidentity : HarperFejerSmoothedCDFIdentity
      (harperCenteredLinearBlockLaw y
        (harperScheduledPrimeBlock y j) t u)
      (harperGaussianBlockLaw y
        (harperScheduledPrimeBlock y j) t u) T)
    (x : ℝ) :
    |harperSmooth (harperFejerMeasureScaled T)
          (cdf (harperCenteredLinearBlockLaw y
            (harperScheduledPrimeBlock y j) t u)) x -
        harperSmooth (harperFejerMeasureScaled T)
          (cdf (harperGaussianBlockLaw y
            (harperScheduledPrimeBlock y j) t u)) x| ≤
      (2 * Real.pi)⁻¹ *
        (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹ *
          (32 * T ^ 3 + T ^ 4) := by
  let mu := harperCenteredLinearBlockLaw y
    (harperScheduledPrimeBlock y j) t u
  let nu := harperGaussianBlockLaw y
    (harperScheduledPrimeBlock y j) t u
  have hInt : IntegrableOn
      (harperEsseenIntegrand (charFun mu) (charFun nu))
      (Icc (-T) T) := by
    dsimp [mu, nu]
    exact integrableOn_harperScheduledBlockLawEsseenIntegrand
      y j t u T hT hfrequency
  have hsmooth := abs_harperSmooth_fejer_sub_le_of_identity
    mu nu T (by simpa [mu, nu] using! hidentity) hInt x
  have hEsseen :
      harperEsseenIntegral (charFun mu) (charFun nu) T ≤
        (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹ *
          (32 * T ^ 3 + T ^ 4) := by
    dsimp [mu, nu]
    have hphi : charFun (harperCenteredLinearBlockLaw y
        (harperScheduledPrimeBlock y j) t u) =
        fun v ↦ harperTiltedLinearPrimeBlockCharacteristic y
          (harperScheduledPrimeBlock y j) t u v := by
      funext v
      exact charFun_harperCenteredLinearBlockLaw y
        (harperScheduledPrimeBlock y j) t u v
    have hpsi : charFun (harperGaussianBlockLaw y
        (harperScheduledPrimeBlock y j) t u) =
        fun v ↦ Complex.exp
          (-((v ^ 2 * harperLinearBlockVariance y
            (harperScheduledPrimeBlock y j) t u / 2 : ℝ) : ℂ)) := by
      funext v
      exact charFun_harperGaussianBlockLaw y
        (harperScheduledPrimeBlock y j) t u v
    rw [hphi, hpsi]
    exact harperScheduledBlockEsseenIntegral_le_explicit
      y j t u T hT hfrequency
  change |harperSmooth (harperFejerMeasureScaled T) (cdf mu) x -
      harperSmooth (harperFejerMeasureScaled T) (cdf nu) x| ≤ _
  exact hsmooth.trans (by
    simpa only [mul_assoc] using!
      mul_le_mul_of_nonneg_left hEsseen (by positivity : 0 ≤ (2 * Real.pi)⁻¹))

/-- The complete deterministic one-block CDF replacement bound after Fejér
smoothing.  The sole analytic input is the named exact inversion identity. -/
theorem harperCDFDistance_scheduledBlock_le_of_fejer_identity
    (y j : ℕ) (t u T : ℝ) (hT : 0 < T)
    (hfrequency : 2 * T ≤ Real.sqrt (harperBlockEndpoint j : ℝ))
    (hvariance : harperLinearBlockVarianceNNReal y
      (harperScheduledPrimeBlock y j) t u ≠ 0)
    (hidentity : HarperFejerSmoothedCDFIdentity
      (harperCenteredLinearBlockLaw y
        (harperScheduledPrimeBlock y j) t u)
      (harperGaussianBlockLaw y
        (harperScheduledPrimeBlock y j) t u) T) :
    harperCDFDistance
        (harperCenteredLinearBlockLaw y
          (harperScheduledPrimeBlock y j) t u)
        (harperGaussianBlockLaw y
          (harperScheduledPrimeBlock y j) t u) ≤
      2 * ((2 * Real.pi)⁻¹ *
          (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹ *
            (32 * T ^ 3 + T ^ 4) +
        16 * (Real.sqrt
          (harperLinearBlockVarianceNNReal y
            (harperScheduledPrimeBlock y j) t u : ℝ))⁻¹ / T) := by
  let mu := harperCenteredLinearBlockLaw y
    (harperScheduledPrimeBlock y j) t u
  let nu := harperGaussianBlockLaw y
    (harperScheduledPrimeBlock y j) t u
  let M : ℝ := (Real.sqrt
    (harperLinearBlockVarianceNNReal y
      (harperScheduledPrimeBlock y j) t u : ℝ))⁻¹
  let epsilon : ℝ := (2 * Real.pi)⁻¹ *
    (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹ *
      (32 * T ^ 3 + T ^ 4)
  have hLip : ∀ x z, |cdf nu x - cdf nu z| ≤ M * |x - z| := by
    intro x z
    dsimp [nu, M, harperGaussianBlockLaw]
    exact abs_cdf_gaussianReal_sub_le_inv_sqrt 0 hvariance x z
  have hsmooth : ∀ x,
      |harperSmooth (harperFejerMeasureScaled T) (cdf mu) x -
        harperSmooth (harperFejerMeasureScaled T) (cdf nu) x| ≤ epsilon := by
    intro x
    dsimp [mu, nu, epsilon]
    exact abs_harperScheduledBlockSmooth_sub_gaussian_le_of_identity
      y j t u T hT.le hfrequency hidentity x
  have hbase := harperCDFDistance_le_of_smooth_le
    mu nu (harperFejerMeasureScaled T)
    (M := M) (δ := 8 / T) (α := (1 / 4 : ℝ)) (ε := epsilon)
    hLip (by dsimp [M]; positivity) (by positivity) (by norm_num)
    (harperFejerMeasureScaled_tail_le_quarter hT) hsmooth
  change harperCDFDistance mu nu ≤ _
  calc
    harperCDFDistance mu nu ≤
        (epsilon + 2 * M * (8 / T)) / (1 - 2 * (1 / 4 : ℝ)) := hbase
    _ = 2 * (epsilon + 16 * M / T) := by ring
    _ = 2 * ((2 * Real.pi)⁻¹ *
          (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹ *
            (32 * T ^ 3 + T ^ 4) +
        16 * (Real.sqrt
          (harperLinearBlockVarianceNNReal y
            (harperScheduledPrimeBlock y j) t u : ℝ))⁻¹ / T) := rfl

end Problem520
end Erdos
