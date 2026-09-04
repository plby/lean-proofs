import ErdosProblems.Erdos525.Exceptional

open scoped BigOperators ENNReal NNReal Topology Real ComplexConjugate
open MeasureTheory Filter Set

namespace Erdos525

/-!
## A quantitative one-point local central limit estimate

The qualitative local CLT in `Core` is sufficient when all phase-space
cutoffs are fixed.  Removing the upper velocity cutoff requires a cutoff that
grows with `n`; for that purpose we retain the explicit error terms occurring
in the Fourier proof.
-/

noncomputable def phaseCovarianceFourierIntegral (m : ℕ) : ℝ :=
  ∫ u : PhaseEuclidean m,
    ‖u‖ ^ 2 * Real.exp (- (‖u‖ ^ 2 / 24))

lemma phaseCovarianceFourierIntegral_nonneg (m : ℕ) :
    0 ≤ phaseCovarianceFourierIntegral m := by
  unfold phaseCovarianceFourierIntegral
  exact integral_nonneg fun u ↦
    mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

noncomputable def quantitativePhaseDensityError (m n : ℕ) : ℝ :=
  (localCLTFourierErrorBoundTest m n +
      phaseCovarianceApproxBound m n / 2 *
        phaseCovarianceFourierIntegral m +
      phaseLimitingSmoothingError (m := m)
        (localCLTSmoothingScaleTest n)) /
    (2 * Real.pi) ^ (4 * m)

lemma quantitativePhaseDensityError_nonneg (m n : ℕ) :
    0 ≤ quantitativePhaseDensityError m n := by
  unfold quantitativePhaseDensityError
  have hfourier : 0 ≤ localCLTFourierErrorBoundTest m n := by
    have hmajor : 0 ≤ localCLTMajorBound m n := by
      unfold localCLTMajorBound
      exact mul_nonneg
        (div_nonneg (pow_nonneg
          (mul_nonneg (by positivity) (rigidityPower_nonneg n _)) _)
          (by positivity))
        (mul_nonneg (pow_nonneg (rigidityPower_nonneg n _) _)
          (div_nonneg (pow_nonneg Real.pi_pos.le _)
            (Nat.cast_nonneg _)))
    have hnowrap : 0 ≤ localCLTNoWrapBoundTest m n := by
      unfold localCLTNoWrapBoundTest
      exact add_nonneg (integral_nonneg fun _ ↦ (Real.exp_pos _).le)
        (integral_nonneg fun _ ↦ (Real.exp_pos _).le)
    have hhigh : 0 ≤ localCLTHighAnnulusBoundTest m n := by
      unfold localCLTHighAnnulusBoundTest
      exact add_nonneg
        (mul_nonneg (Real.exp_pos _).le
          (mul_nonneg (pow_nonneg
              (mul_nonneg (Real.sqrt_nonneg _)
                (rigidityPower_nonneg n _)) _)
            (div_nonneg (pow_nonneg Real.pi_pos.le _)
              (Nat.cast_nonneg _))))
        (integral_nonneg fun _ ↦ (Real.exp_pos _).le)
    have htail : 0 ≤ localCLTSmoothingTailBoundTest m n := by
      unfold localCLTSmoothingTailBoundTest
      positivity
    exact add_nonneg (add_nonneg (add_nonneg hmajor hnowrap) hhigh) htail
  have hsmoothing : 0 ≤ phaseLimitingSmoothingError
      (m := m) (localCLTSmoothingScaleTest n) := by
    unfold phaseLimitingSmoothingError
    exact integral_nonneg fun u ↦
      mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  exact div_nonneg
    (add_nonneg
      (add_nonneg hfourier
        (mul_nonneg (div_nonneg (phaseCovarianceApproxBound_nonneg m n)
          (by norm_num)) (phaseCovarianceFourierIntegral_nonneg m)))
      hsmoothing)
    (pow_nonneg (by positivity) _)

theorem eventually_uniform_phaseCovarianceFourier_le_explicit
    {m : ℕ} :
    ∀ᶠ n : ℕ in atTop, ∀ (points : Fin m → ℝ),
      (∀ r, IsSmooth n (rigiditySmoothScale n) (points r)) →
      IsSpread n (rigiditySmoothScale n) points →
      ∀ y : PhaseEuclidean m,
        ‖phaseFourierIntegral (localCLTSmoothingScaleTest n) y
              (normalizedPhaseCovarianceGaussian n points) -
            phaseFourierIntegral (localCLTSmoothingScaleTest n) y
              normalizedPhaseLimitingGaussian‖ ≤
          phaseCovarianceApproxBound m n / 2 *
            phaseCovarianceFourierIntegral m := by
  filter_upwards [Nat.eventually_pos,
      eventually_hasPhaseCovarianceLower_rigidity m]
    with n hn hcov
  intro points hsmooth hspread y
  have hscale : 0 < rigiditySmoothScale n := by
    unfold rigiditySmoothScale
    exact rigidityPower_pos hn _
  have hrho : 0 < rigiditySmoothScale n / n := by positivity
  have hform : ∀ u : PhaseEuclidean m,
      |normalizedPhaseCovarianceForm n points (euclideanToPhase u) -
          phaseLimitingCovarianceForm (euclideanToPhase u)| ≤
        phaseCovarianceApproxBound m n * ‖u‖ ^ 2 := by
    intro u
    have hraw := abs_normalizedPhaseCovarianceForm_sub_limiting_le
      n hn (rigiditySmoothScale n) (rigiditySmoothScale n) points
      hsmooth hspread (rigiditySmoothScale n / n) (by simp) hrho
      (euclideanToPhase u)
    simpa [phaseCovarianceApproxBound, phaseNormSq_euclideanToPhase] using hraw
  have hpoint : ∀ u : PhaseEuclidean m,
      ‖normalizedPhaseCovarianceGaussian n points u -
          normalizedPhaseLimitingGaussian u‖ ≤
        phaseCovarianceApproxBound m n / 2 * ‖u‖ ^ 2 *
          Real.exp (- (‖u‖ ^ 2 / 24)) := by
    intro u
    let a := normalizedPhaseCovarianceForm n points (euclideanToPhase u)
    let b := phaseLimitingCovarianceForm (euclideanToPhase u)
    let c := (1 / 12 : ℝ) * ‖u‖ ^ 2
    have hca : c ≤ a := by
      dsimp [a, c]
      simpa [phaseNormSq_euclideanToPhase] using
        normalizedPhaseCovarianceForm_lower n points (1 / 12)
          (hcov points hsmooth hspread) (euclideanToPhase u)
    have hcb : c ≤ b := by
      dsimp [b, c]
      have hlow := phaseLimitingCovarianceForm_lower (euclideanToPhase u)
      rw [phaseNormSq_euclideanToPhase] at hlow
      nlinarith [sq_nonneg ‖u‖]
    have hexp := abs_exp_neg_half_sub_exp_neg_half_le_with_lower hca hcb
    change ‖(Real.exp (-a / 2) : ℂ) - (Real.exp (-b / 2) : ℂ)‖ ≤ _
    rw [show (Real.exp (-a / 2) : ℂ) - (Real.exp (-b / 2) : ℂ) =
        ((Real.exp (-a / 2) - Real.exp (-b / 2) : ℝ) : ℂ) by
          push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs]
    calc
      |Real.exp (-a / 2) - Real.exp (-b / 2)| ≤
          |a - b| / 2 * Real.exp (-c / 2) := hexp
      _ ≤ (phaseCovarianceApproxBound m n * ‖u‖ ^ 2) / 2 *
          Real.exp (-c / 2) := by
        gcongr
        simpa [a, b] using hform u
      _ = phaseCovarianceApproxBound m n / 2 * ‖u‖ ^ 2 *
          Real.exp (- (‖u‖ ^ 2 / 24)) := by
        dsimp [c]
        congr 2 <;> ring
  have hcovInt : Integrable (fun u : PhaseEuclidean m ↦
      phaseFourierMultiplier (localCLTSmoothingScaleTest n) y u *
        normalizedPhaseCovarianceGaussian n points u) := by
    apply (integrable_phaseFixedGaussian (m := m)).mono'
    · exact ((continuous_phaseFourierMultiplier
        (localCLTSmoothingScaleTest n) y).mul
          (continuous_normalizedPhaseCovarianceGaussian n points)).aestronglyMeasurable
    · filter_upwards [] with u
      rw [norm_mul, norm_phaseFourierMultiplier]
      calc
        Real.exp (-(localCLTSmoothingScaleTest n ^ 2 / 2) * ‖u‖ ^ 2) *
            ‖normalizedPhaseCovarianceGaussian n points u‖ ≤
            1 * Real.exp (- (‖u‖ ^ 2 / 24)) := by
          gcongr
          · rw [Real.exp_le_one_iff]
            exact mul_nonpos_of_nonpos_of_nonneg
              (neg_nonpos.mpr (div_nonneg (sq_nonneg _) (by norm_num)))
              (sq_nonneg _)
          · exact norm_normalizedPhaseCovarianceGaussian_le_fixedGaussian
              n points (hcov points hsmooth hspread) u
        _ ≤ Real.exp (- (‖u‖ ^ 2 / 48)) := by
          rw [one_mul]
          apply Real.exp_le_exp.mpr
          nlinarith [sq_nonneg ‖u‖]
  have hlimInt := integrable_phaseFourier_limitingGaussian
    (m := m) (localCLTSmoothingScaleTest n) y
  unfold phaseFourierIntegral
  rw [← integral_sub hcovInt hlimInt]
  calc
    ‖∫ u : PhaseEuclidean m,
        phaseFourierMultiplier (localCLTSmoothingScaleTest n) y u *
            normalizedPhaseCovarianceGaussian n points u -
          phaseFourierMultiplier (localCLTSmoothingScaleTest n) y u *
            normalizedPhaseLimitingGaussian u‖ ≤
        ∫ u : PhaseEuclidean m,
          phaseCovarianceApproxBound m n / 2 *
            (‖u‖ ^ 2 * Real.exp (- (‖u‖ ^ 2 / 24))) := by
      apply norm_integral_le_of_norm_le
        ((integrable_phaseNormSq_mul_fixedGaussian (m := m)).const_mul
          (phaseCovarianceApproxBound m n / 2))
      filter_upwards [] with u
      rw [← mul_sub, norm_mul, norm_phaseFourierMultiplier]
      have hweight : Real.exp
          (-(localCLTSmoothingScaleTest n ^ 2 / 2) * ‖u‖ ^ 2) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact mul_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (div_nonneg (sq_nonneg _) (by norm_num)))
          (sq_nonneg _)
      calc
        Real.exp (-(localCLTSmoothingScaleTest n ^ 2 / 2) * ‖u‖ ^ 2) *
            ‖normalizedPhaseCovarianceGaussian n points u -
              normalizedPhaseLimitingGaussian u‖ ≤
            1 * ‖normalizedPhaseCovarianceGaussian n points u -
              normalizedPhaseLimitingGaussian u‖ :=
          mul_le_mul_of_nonneg_right hweight (norm_nonneg _)
        _ ≤ 1 * (phaseCovarianceApproxBound m n / 2 * ‖u‖ ^ 2 *
              Real.exp (- (‖u‖ ^ 2 / 24))) := by
          exact mul_le_mul_of_nonneg_left (hpoint u) zero_le_one
        _ = phaseCovarianceApproxBound m n / 2 *
            (‖u‖ ^ 2 * Real.exp (- (‖u‖ ^ 2 / 24))) := by ring
    _ = phaseCovarianceApproxBound m n / 2 *
          phaseCovarianceFourierIntegral m := by
      rw [integral_const_mul]
      rfl

theorem eventually_uniform_phaseSmoothedDensity_le_explicit
    {m : ℕ} (hm : 0 < m) :
    ∀ᶠ n : ℕ in atTop, ∀ (points : Fin m → ℝ)
        (y : PhaseEuclidean m),
      (∀ r, IsSmooth n (rigiditySmoothScale n) (points r)) →
      IsSpread n (rigiditySmoothScale n) points →
      |phaseSmoothedDensity n points (localCLTSmoothingScaleTest n) y -
        phaseLimitingDensity y| ≤ quantitativePhaseDensityError m n := by
  filter_upwards [Nat.eventually_pos,
      eventually_smoothedLocalCLT_le_test hm,
      eventually_uniform_phaseCovarianceFourier_le_explicit (m := m)]
    with n hn hwalk hcov
  intro points y hsmooth hspread
  have hsigma : 0 < localCLTSmoothingScaleTest n := by
    unfold localCLTSmoothingScaleTest
    exact rigidityPower_pos hn _
  let sigma := localCLTSmoothingScaleTest n
  let A : ℂ := ((Real.pi : ℂ) / ((sigma ^ 2 / 2 : ℝ) : ℂ)) ^
      ((Module.finrank ℝ (PhaseEuclidean m) : ℂ) / 2) *
        phaseGaussianSmoothedMass n points sigma y
  let B : ℂ := phaseFourierIntegral sigma y
      (normalizedPhaseCovarianceGaussian n points)
  let C : ℂ := phaseFourierIntegral sigma y
      normalizedPhaseLimitingGaussian
  let D : ℂ := (2 * Real.pi : ℂ) ^ (4 * m) * phaseLimitingDensity y
  have hAB : ‖A - B‖ ≤ localCLTFourierErrorBoundTest m n := by
    exact hwalk points y hsmooth hspread
  have hBC : ‖B - C‖ ≤ phaseCovarianceApproxBound m n / 2 *
      phaseCovarianceFourierIntegral m := by
    simpa [B, C, sigma] using hcov points hsmooth hspread y
  have hCD : ‖C - D‖ ≤ phaseLimitingSmoothingError (m := m) sigma := by
    dsimp [C, D]
    rw [← phaseLimitingFourierValue_zero_eq_density,
      ← phaseFourierIntegral_limitingGaussian 0 y]
    exact norm_phaseFourierIntegral_limiting_sub_zero_le sigma y
  have hAD : ‖A - D‖ ≤
      localCLTFourierErrorBoundTest m n +
        phaseCovarianceApproxBound m n / 2 *
          phaseCovarianceFourierIntegral m +
        phaseLimitingSmoothingError (m := m) sigma := by
    calc
      ‖A - D‖ ≤ ‖A - B‖ + ‖B - C‖ + ‖C - D‖ := by
        rw [show A - D = (A - B) + (B - C) + (C - D) by abel]
        exact (norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ _ := add_le_add (add_le_add hAB hBC) hCD
  let K : ℝ := (2 * Real.pi) ^ (4 * m)
  have hK : 0 < K := by positivity
  dsimp [A, D, sigma] at hAD
  rw [phaseFourierNormalization_eq_real m sigma hsigma,
    phaseGaussianSmoothedMass_eq_real] at hAD
  norm_cast at hAD
  change |(((2 * Real.pi / sigma ^ 2) ^ (2 * m) *
      phaseGaussianSmoothedMassReal n points sigma y) / K) -
      phaseLimitingDensity y| ≤ _
  rw [show
      ((2 * Real.pi / sigma ^ 2) ^ (2 * m) *
          phaseGaussianSmoothedMassReal n points sigma y) / K -
          phaseLimitingDensity y =
        (((2 * Real.pi / sigma ^ 2) ^ (2 * m) *
          phaseGaussianSmoothedMassReal n points sigma y) -
            K * phaseLimitingDensity y) / K by field_simp]
  rw [abs_div, abs_of_pos hK]
  unfold quantitativePhaseDensityError
  rw [div_le_div_iff_of_pos_right hK]
  simpa only [K, sigma, Complex.norm_real, Real.norm_eq_abs] using hAD

/-! ### Polynomially weighted decay of the explicit error -/

lemma gaussianTail_le_exp_mul_integral
    (m : ℕ) (c R : ℝ) (hc : 0 < c) (hR : 0 ≤ R) :
    (∫ u : PhaseEuclidean m in {u | R ≤ ‖u‖},
        Real.exp (-c * ‖u‖ ^ 2)) ≤
      Real.exp (-(c / 2) * R ^ 2) *
        ∫ u : PhaseEuclidean m, Real.exp (-(c / 2) * ‖u‖ ^ 2) := by
  let S : Set (PhaseEuclidean m) := {u | R ≤ ‖u‖}
  let g : PhaseEuclidean m → ℝ := fun u ↦
    Real.exp (-(c / 2) * ‖u‖ ^ 2)
  have hc2 : 0 < c / 2 := by positivity
  have hg : Integrable g := by
    simpa [g] using integrable_rexp_neg_mul_norm_sq m (c / 2) hc2
  have hS : MeasurableSet S :=
    measurableSet_le measurable_const continuous_norm.measurable
  have hpoint : ∀ u ∈ S,
      Real.exp (-c * ‖u‖ ^ 2) ≤
        Real.exp (-(c / 2) * R ^ 2) * g u := by
    intro u hu
    have hsq : R ^ 2 ≤ ‖u‖ ^ 2 :=
      (sq_le_sq₀ hR (norm_nonneg u)).2 hu
    rw [show -c * ‖u‖ ^ 2 =
        (-(c / 2) * ‖u‖ ^ 2) + (-(c / 2) * ‖u‖ ^ 2) by ring,
      Real.exp_add]
    dsimp [g]
    have hexp : Real.exp (-(c / 2) * ‖u‖ ^ 2) ≤
        Real.exp (-(c / 2) * R ^ 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    exact mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
  calc
    (∫ u : PhaseEuclidean m in S, Real.exp (-c * ‖u‖ ^ 2)) ≤
        ∫ u : PhaseEuclidean m in S,
          Real.exp (-(c / 2) * R ^ 2) * g u := by
      apply setIntegral_mono_on
      · exact (integrable_rexp_neg_mul_norm_sq m c hc).integrableOn
      · exact hg.const_mul _ |>.integrableOn
      · exact hS
      · exact hpoint
    _ ≤ ∫ u : PhaseEuclidean m,
          Real.exp (-(c / 2) * R ^ 2) * g u := by
      apply setIntegral_le_integral (hg.const_mul _)
      exact Eventually.of_forall fun u ↦ by
        dsimp [g]
        positivity
    _ = Real.exp (-(c / 2) * R ^ 2) *
          ∫ u : PhaseEuclidean m, Real.exp (-(c / 2) * ‖u‖ ^ 2) := by
      rw [integral_const_mul]

lemma rigidityPower_mul_majorGaussianTail_tendsto_zero
    (m : ℕ) (p c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦
      rigidityPower n p *
        (∫ u : PhaseEuclidean m in
          {u | localCLTMajorRadius m n ≤ ‖u‖},
          Real.exp (-c * ‖u‖ ^ 2))) atTop (𝓝 0) := by
  let I : ℝ := ∫ u : PhaseEuclidean m,
    Real.exp (-(c / 2) * ‖u‖ ^ 2)
  let q : ℝ := 2 * localCLTMajorExponent m
  have hq : 0 < q := by
    dsimp [q]
    linarith [localCLTMajorExponent_pos m]
  have hc2 : 0 < c / 2 := by positivity
  have hcore := (tendsto_rigidityPower_mul_exp_neg_power_test
    p q (c / 2) hq hc2).const_mul I
  let upper : ℕ → ℝ := fun n ↦
    I * (rigidityPower n p *
      Real.exp (-(c / 2) * rigidityPower n q))
  have hupper : Tendsto upper atTop (𝓝 0) := by
    simpa [upper] using hcore
  apply squeeze_zero' (g := upper)
  · exact Eventually.of_forall fun n ↦
      mul_nonneg (rigidityPower_nonneg n p)
        (integral_nonneg fun _ ↦ (Real.exp_pos _).le)
  · filter_upwards [Nat.eventually_pos] with n hn
    have hR0 : 0 ≤ localCLTMajorRadius m n :=
      rigidityPower_nonneg n _
    have htail := gaussianTail_le_exp_mul_integral m c
      (localCLTMajorRadius m n) hc hR0
    have hp0 := rigidityPower_nonneg n p
    have hmul := mul_le_mul_of_nonneg_left htail hp0
    have hsq : localCLTMajorRadius m n ^ 2 = rigidityPower n q := by
      have hpow := rigidityPower_nat_pow hn (localCLTMajorExponent m) 2
      rw [show localCLTMajorExponent m * (2 : ℕ) =
          2 * localCLTMajorExponent m by push_cast; ring] at hpow
      simpa [localCLTMajorRadius, q] using hpow
    rw [hsq] at hmul
    change _ ≤ I * (rigidityPower n p *
      Real.exp (-(c / 2) * rigidityPower n q))
    simpa [I, mul_assoc, mul_comm, mul_left_comm] using hmul
  · exact hupper

lemma rigidityPower_mul_localCLTNoWrapBound_tendsto_zero
    (m : ℕ) (p : ℝ) :
    Tendsto (fun n : ℕ ↦ rigidityPower n p *
      localCLTNoWrapBoundTest m n) atTop (𝓝 0) := by
  have h1 := rigidityPower_mul_majorGaussianTail_tendsto_zero
    m p (1 / (12 * Real.pi ^ 2)) (by positivity)
  have h2 := rigidityPower_mul_majorGaussianTail_tendsto_zero
    m p (1 / 24) (by norm_num)
  simpa [localCLTNoWrapBoundTest, mul_add] using h1.add h2

lemma phaseLimitingSmoothingError_le_quadratic
    {m : ℕ} (sigma : ℝ) :
    phaseLimitingSmoothingError (m := m) sigma ≤
      sigma ^ 2 / 2 * phaseCovarianceFourierIntegral m := by
  unfold phaseLimitingSmoothingError phaseCovarianceFourierIntegral
  have hdom := (integrable_phaseNormSq_mul_fixedGaussian (m := m)).const_mul
    (sigma ^ 2 / 2)
  rw [← integral_const_mul]
  apply integral_mono
  · apply (integrable_phaseLimitingEnvelope (m := m)).mono'
    · fun_prop
    · filter_upwards [] with u
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)]
      exact mul_le_of_le_one_left (Real.exp_nonneg _)
        (abs_exp_neg_sq_mul_sub_one_le_one sigma ‖u‖)
  · exact hdom
  · intro u
    let a : ℝ := sigma ^ 2 / 2 * ‖u‖ ^ 2
    have ha : 0 ≤ a := by dsimp [a]; positivity
    have hexpLe : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ha)
    have hone : 1 - Real.exp (-a) ≤ a := by
      have h := Real.add_one_le_exp (-a)
      linarith
    have habs : |Real.exp (-a) - 1| ≤ a := by
      rw [abs_of_nonpos (sub_nonpos.mpr hexpLe)]
      linarith
    have hgauss : Real.exp (- (‖u‖ ^ 2 / 12)) ≤
        Real.exp (- (‖u‖ ^ 2 / 24)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg ‖u‖]
    calc
      |Real.exp (-(sigma ^ 2 / 2) * ‖u‖ ^ 2) - 1| *
          Real.exp (- (‖u‖ ^ 2 / 12)) =
          |Real.exp (-a) - 1| * Real.exp (- (‖u‖ ^ 2 / 12)) := by
            dsimp [a]
            congr 3 <;> ring_nf
      _ ≤ a * Real.exp (- (‖u‖ ^ 2 / 12)) :=
        mul_le_mul_of_nonneg_right habs (Real.exp_pos _).le
      _ ≤ a * Real.exp (- (‖u‖ ^ 2 / 24)) :=
        mul_le_mul_of_nonneg_left hgauss ha
      _ = sigma ^ 2 / 2 *
          (‖u‖ ^ 2 * Real.exp (- (‖u‖ ^ 2 / 24))) := by
        dsimp [a]
        ring

lemma rigidityPower_mul_localCLTMajorBound_tendsto_zero
    (m : ℕ) (p : ℝ) (hp : p < 3 / 4) :
    Tendsto (fun n : ℕ ↦ rigidityPower n p *
      localCLTMajorBound m n) atTop (𝓝 0) := by
  let C : ℝ := (4 * m : ℝ) ^ 4 *
    (Real.pi ^ (2 * m) / (2 * m).factorial)
  have hneg : 0 < 3 / 4 - p := by linarith
  have hupper : Tendsto (fun n : ℕ ↦
      C * rigidityPower n (-(3 / 4 - p))) atTop (𝓝 0) := by
    simpa using (tendsto_rigidityPower_neg_zero hneg).const_mul C
  apply squeeze_zero' (g := fun n : ℕ ↦
      C * rigidityPower n (-(3 / 4 - p)))
  · exact Eventually.of_forall fun n ↦ mul_nonneg
      (rigidityPower_nonneg n p) (by
        unfold localCLTMajorBound
        exact mul_nonneg
          (div_nonneg (pow_nonneg
            (mul_nonneg (by positivity) (rigidityPower_nonneg n _)) _)
            (by positivity))
          (mul_nonneg (pow_nonneg (rigidityPower_nonneg n _) _)
            (div_nonneg (pow_nonneg Real.pi_pos.le _)
              (Nat.cast_nonneg _))))
  · filter_upwards [Nat.eventually_pos] with n hn
    have hbound := localCLTMajorBound_le_power m n hn
    have hmul := mul_le_mul_of_nonneg_left hbound
      (rigidityPower_nonneg n p)
    have hpow : rigidityPower n p * rigidityPower n (-3 / 4) =
        rigidityPower n (-(3 / 4 - p)) := by
      rw [← rigidityPower_add hn]
      congr 1
      ring
    calc
      rigidityPower n p * localCLTMajorBound m n ≤
          rigidityPower n p *
            (((4 * m : ℝ) ^ 4 *
              (Real.pi ^ (2 * m) / (2 * m).factorial)) *
                rigidityPower n (-3 / 4)) := hmul
      _ = C * (rigidityPower n p * rigidityPower n (-3 / 4)) := by
        dsimp [C]
        ring
      _ = C * rigidityPower n (-(3 / 4 - p)) := by rw [hpow]
  · exact hupper

lemma rigidityPower_mul_phaseCovarianceApproxBound_tendsto_zero
    (m : ℕ) (p : ℝ) (hp : p < 1 / 16) :
    Tendsto (fun n : ℕ ↦ rigidityPower n p *
      phaseCovarianceApproxBound m n) atTop (𝓝 0) := by
  let C : ℝ := 24 * (m : ℝ) ^ 2
  have hnegSixteenth : 0 < 1 / 16 - p := by linarith
  have hnegOne : 0 < 1 - p := by linarith
  have hfirst : Tendsto (fun n : ℕ ↦
      C * rigidityPower n (-(1 / 16 - p))) atTop (𝓝 0) := by
    simpa using
      (tendsto_rigidityPower_neg_zero hnegSixteenth).const_mul C
  have hsecond : Tendsto (fun n : ℕ ↦
      (1 / 6 : ℝ) * rigidityPower n (-(1 - p))) atTop (𝓝 0) := by
    simpa using
      (tendsto_rigidityPower_neg_zero hnegOne).const_mul (1 / 6 : ℝ)
  let upper : ℕ → ℝ := fun n ↦
    C * rigidityPower n (-(1 / 16 - p)) +
      (1 / 6 : ℝ) * rigidityPower n (-(1 - p))
  have hupper : Tendsto upper atTop (𝓝 0) := by
    simpa [upper] using hfirst.add hsecond
  apply squeeze_zero' (g := upper)
  · exact Eventually.of_forall fun n ↦ mul_nonneg
      (rigidityPower_nonneg n p)
      (phaseCovarianceApproxBound_nonneg m n)
  · filter_upwards [Nat.eventually_pos] with n hn
    have hbound := phaseCovarianceApproxBound_le_power m n hn
    have hmul := mul_le_mul_of_nonneg_left hbound
      (rigidityPower_nonneg n p)
    have hpSixteenth : rigidityPower n p * rigidityPower n (-1 / 16) =
        rigidityPower n (-(1 / 16 - p)) := by
      rw [← rigidityPower_add hn]
      congr 1
      ring
    have hnPow : (n : ℝ) = rigidityPower n 1 := by
      simp [rigidityPower]
    have hpOne : rigidityPower n p / (6 * (n : ℝ)) =
        (1 / 6 : ℝ) * rigidityPower n (-(1 - p)) := by
      rw [hnPow, show rigidityPower n (-(1 - p)) =
          rigidityPower n (p - 1) by congr 1 <;> ring]
      rw [show rigidityPower n (p - 1) =
          rigidityPower n p * rigidityPower n (-1) by
            rw [← rigidityPower_add hn]
            congr 1 <;> ring]
      rw [show rigidityPower n (-1) = (rigidityPower n 1)⁻¹ by
        unfold rigidityPower
        rw [Real.rpow_neg (by exact_mod_cast hn.le)]]
      field_simp [(rigidityPower_pos hn 1).ne']
    change rigidityPower n p * phaseCovarianceApproxBound m n ≤ upper n
    calc
      rigidityPower n p * phaseCovarianceApproxBound m n ≤
          rigidityPower n p *
            (24 * (m : ℝ) ^ 2 * rigidityPower n (-1 / 16) +
              1 / (6 * (n : ℝ))) := hmul
      _ = 24 * (m : ℝ) ^ 2 *
            (rigidityPower n p * rigidityPower n (-1 / 16)) +
          rigidityPower n p / (6 * (n : ℝ)) := by ring
      _ = 24 * (m : ℝ) ^ 2 * rigidityPower n (-(1 / 16 - p)) +
          (1 / 6 : ℝ) * rigidityPower n (-(1 - p)) := by
        rw [hpSixteenth, hpOne]
      _ = upper n := by rfl
  · exact hupper

lemma rigidityPower_mul_phaseLimitingSmoothingError_tendsto_zero
    (m : ℕ) (p : ℝ) (hp : p < 4) :
    Tendsto (fun n : ℕ ↦ rigidityPower n p *
      phaseLimitingSmoothingError (m := m)
        (localCLTSmoothingScaleTest n)) atTop (𝓝 0) := by
  let I := phaseCovarianceFourierIntegral m
  have hneg : 0 < 4 - p := by linarith
  have hupper : Tendsto (fun n : ℕ ↦
      (I / 2) * rigidityPower n (-(4 - p))) atTop (𝓝 0) := by
    simpa using
      (tendsto_rigidityPower_neg_zero hneg).const_mul (I / 2)
  apply squeeze_zero' (g := fun n : ℕ ↦
      (I / 2) * rigidityPower n (-(4 - p)))
  · exact Eventually.of_forall fun n ↦ mul_nonneg
      (rigidityPower_nonneg n p) (by
        unfold phaseLimitingSmoothingError
        exact integral_nonneg fun _ ↦
          mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
  · filter_upwards [Nat.eventually_pos] with n hn
    have hbound := phaseLimitingSmoothingError_le_quadratic
      (m := m) (localCLTSmoothingScaleTest n)
    have hmul := mul_le_mul_of_nonneg_left hbound
      (rigidityPower_nonneg n p)
    have hscaleSq : localCLTSmoothingScaleTest n ^ 2 =
        rigidityPower n (-4) := by
      have hpow := rigidityPower_nat_pow hn (-2) 2
      rw [show (-2 : ℝ) * (2 : ℕ) = -4 by norm_num] at hpow
      simpa [localCLTSmoothingScaleTest] using hpow
    have hpow : rigidityPower n p * rigidityPower n (-4) =
        rigidityPower n (-(4 - p)) := by
      rw [← rigidityPower_add hn]
      congr 1
      ring
    dsimp [I]
    rw [hscaleSq, show rigidityPower n p *
        (rigidityPower n (-4) / 2 * phaseCovarianceFourierIntegral m) =
      (phaseCovarianceFourierIntegral m / 2) *
        (rigidityPower n p * rigidityPower n (-4)) by ring,
      hpow] at hmul
    exact hmul
  · exact hupper

lemma rigidityPower_mul_localCLTHighAnnulusPolynomial_tendsto_zero
    (m : ℕ) (p : ℝ) :
    Tendsto (fun n : ℕ ↦ rigidityPower n p *
      (Real.exp (-rigidityEnergyScale n) *
        ((2 * rigidityPower n (rigidityFourierExponent m + 1)) ^ (4 * m) *
          (Real.pi ^ (2 * m) / (2 * m).factorial)))) atTop (𝓝 0) := by
  let r : ℝ := (rigidityFourierExponent m + 1) * (4 * m : ℕ)
  let C : ℝ := (2 : ℝ) ^ (4 * m) *
    (Real.pi ^ (2 * m) / (2 * m).factorial)
  have hcore : Tendsto (fun n : ℕ ↦
      C * (rigidityPower n (p + r) *
        Real.exp (-rigidityEnergyScale n))) atTop (𝓝 0) := by
    simpa using
      (tendsto_rigidityPower_mul_exp_neg_energy_test (p + r)).const_mul C
  apply hcore.congr'
  filter_upwards [Nat.eventually_pos] with n hn
  have hr : rigidityPower n (rigidityFourierExponent m + 1) ^ (4 * m) =
      rigidityPower n r := by
    simpa [r] using rigidityPower_nat_pow hn
      (rigidityFourierExponent m + 1) (4 * m)
  have hpr : rigidityPower n p * rigidityPower n r =
      rigidityPower n (p + r) := (rigidityPower_add hn _ _).symm
  rw [mul_pow, hr]
  dsimp [C]
  rw [← hpr]
  ring

lemma rigidityPower_mul_highStartGaussianTail_tendsto_zero
    (m : ℕ) (p c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ rigidityPower n p *
      (∫ u : PhaseEuclidean m in
        {u | localCLTHighStartTest n ≤ ‖u‖},
        Real.exp (-c * ‖u‖ ^ 2))) atTop (𝓝 0) := by
  let I : ℝ := ∫ u : PhaseEuclidean m,
    Real.exp (-(c / 2) * ‖u‖ ^ 2)
  have hc2 : 0 < c / 2 := by positivity
  have hcore := (tendsto_rigidityPower_mul_exp_neg_power_test
    p (3 / 4) (c / 2) (by norm_num) hc2).const_mul I
  let upper : ℕ → ℝ := fun n ↦
    I * (rigidityPower n p *
      Real.exp (-(c / 2) * rigidityPower n (3 / 4)))
  have hupper : Tendsto upper atTop (𝓝 0) := by
    simpa [upper] using hcore
  apply squeeze_zero' (g := upper)
  · exact Eventually.of_forall fun n ↦ mul_nonneg
      (rigidityPower_nonneg n p)
      (integral_nonneg fun _ ↦ (Real.exp_pos _).le)
  · filter_upwards [Nat.eventually_pos] with n hn
    have hstart0 : 0 ≤ localCLTHighStartTest n := by
      unfold localCLTHighStartTest
      exact mul_nonneg (Real.sqrt_nonneg _) (rigidityPower_nonneg n _)
    have htail := gaussianTail_le_exp_mul_integral m c
      (localCLTHighStartTest n) hc hstart0
    have hmul := mul_le_mul_of_nonneg_left htail
      (rigidityPower_nonneg n p)
    have hstart := rigidityPower_three_eighths_le_highStart_test n hn
    have hsq : rigidityPower n (3 / 8) ^ 2 =
        rigidityPower n (3 / 4) := by
      have hpow := rigidityPower_nat_pow hn (3 / 8) 2
      rw [show (3 / 8 : ℝ) * (2 : ℕ) = 3 / 4 by norm_num] at hpow
      exact hpow
    have hstartSq : rigidityPower n (3 / 4) ≤
        localCLTHighStartTest n ^ 2 := by
      rw [← hsq]
      exact (sq_le_sq₀ (rigidityPower_nonneg n _)
        hstart0).2 hstart
    have hexp : Real.exp (-(c / 2) * localCLTHighStartTest n ^ 2) ≤
        Real.exp (-(c / 2) * rigidityPower n (3 / 4)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hp0 := rigidityPower_nonneg n p
    have hI0 : 0 ≤ I := by
      dsimp [I]
      exact integral_nonneg fun _ ↦ (Real.exp_pos _).le
    calc
      rigidityPower n p *
          (∫ u : PhaseEuclidean m in
            {u | localCLTHighStartTest n ≤ ‖u‖},
            Real.exp (-c * ‖u‖ ^ 2)) ≤
        rigidityPower n p *
          (Real.exp (-(c / 2) * localCLTHighStartTest n ^ 2) * I) := hmul
      _ ≤ rigidityPower n p *
          (Real.exp (-(c / 2) * rigidityPower n (3 / 4)) * I) := by
        gcongr
      _ = upper n := by
        dsimp [upper]
        ring
  · exact hupper

lemma rigidityPower_mul_localCLTHighAnnulusBound_tendsto_zero
    (m : ℕ) (p : ℝ) :
    Tendsto (fun n : ℕ ↦ rigidityPower n p *
      localCLTHighAnnulusBoundTest m n) atTop (𝓝 0) := by
  have hpoly :=
    rigidityPower_mul_localCLTHighAnnulusPolynomial_tendsto_zero m p
  have htail := rigidityPower_mul_highStartGaussianTail_tendsto_zero
    m p (1 / 24) (by norm_num)
  let upper : ℕ → ℝ := fun n ↦ rigidityPower n p *
    (Real.exp (-rigidityEnergyScale n) *
        ((2 * rigidityPower n (rigidityFourierExponent m + 1)) ^ (4 * m) *
          (Real.pi ^ (2 * m) / (2 * m).factorial))) +
      rigidityPower n p *
        (∫ u : PhaseEuclidean m in
          {u | localCLTHighStartTest n ≤ ‖u‖},
          Real.exp (-(1 / 24) * ‖u‖ ^ 2))
  have hupper : Tendsto upper atTop (𝓝 0) := by
    simpa [upper] using hpoly.add htail
  apply squeeze_zero' (g := upper)
  · exact Eventually.of_forall fun n ↦ mul_nonneg
      (rigidityPower_nonneg n p) (by
        unfold localCLTHighAnnulusBoundTest
        have hrad0 : 0 ≤ localCLTHighRadiusTest m n := by
          unfold localCLTHighRadiusTest
          exact mul_nonneg (Real.sqrt_nonneg _) (rigidityPower_nonneg n _)
        exact add_nonneg
          (mul_nonneg (Real.exp_pos _).le
            (mul_nonneg (pow_nonneg hrad0 _)
              (div_nonneg (pow_nonneg Real.pi_pos.le _)
                (Nat.cast_nonneg _))))
          (integral_nonneg fun _ ↦ (Real.exp_pos _).le))
  · filter_upwards [Nat.eventually_pos] with n hn
    have hrad0 : 0 ≤ localCLTHighRadiusTest m n := by
      unfold localCLTHighRadiusTest
      exact mul_nonneg (Real.sqrt_nonneg _) (rigidityPower_nonneg n _)
    have hpowle := pow_le_pow_left₀ hrad0
      (localCLTHighRadius_le_polynomial_test m n hn) (4 * m)
    have hG0 : 0 ≤ Real.pi ^ (2 * m) / (2 * m).factorial := by positivity
    have hinside := mul_le_mul_of_nonneg_right hpowle hG0
    have hfirst := mul_le_mul_of_nonneg_left hinside
      (Real.exp_pos (-rigidityEnergyScale n)).le
    unfold localCLTHighAnnulusBoundTest
    dsimp [upper]
    rw [mul_add]
    exact add_le_add
      (mul_le_mul_of_nonneg_left hfirst (rigidityPower_nonneg n p)) le_rfl
  · exact hupper

lemma rigidityPower_mul_localCLTSmoothingTailBound_tendsto_zero
    (m : ℕ) (p : ℝ) :
    Tendsto (fun n : ℕ ↦ rigidityPower n p *
      localCLTSmoothingTailBoundTest m n) atTop (𝓝 0) := by
  let q : ℝ := 2 * rigidityFourierExponent m - 3
  let C : ℝ := 2 * (4 * Real.pi) ^ (2 * m)
  let r : ℝ := p + 8 * m
  have hq : 0 < q := localCLTSmoothingExponent_pos_test m
  have hcore := (tendsto_rigidityPower_mul_exp_neg_power_test
    r q (1 / 4) hq (by norm_num)).const_mul C
  let upper : ℕ → ℝ := fun n ↦ C *
    (rigidityPower n r *
      Real.exp (-(1 / 4) * rigidityPower n q))
  have hupper : Tendsto upper atTop (𝓝 0) := by
    simpa [upper] using hcore
  apply squeeze_zero' (g := upper)
  · exact Eventually.of_forall fun n ↦ mul_nonneg
      (rigidityPower_nonneg n p) (by
        unfold localCLTSmoothingTailBoundTest
        positivity)
  · filter_upwards [Nat.eventually_pos] with n hn
    have hbound := localCLTSmoothingTailBound_le_polynomial_test m n hn
    have hmul := mul_le_mul_of_nonneg_left hbound
      (rigidityPower_nonneg n p)
    have hpr : rigidityPower n p * rigidityPower n (8 * m) =
        rigidityPower n r := by
      simpa [r] using (rigidityPower_add hn p (8 * m)).symm
    calc
      rigidityPower n p * localCLTSmoothingTailBoundTest m n ≤
          rigidityPower n p * localCLTSmoothingTailPolynomialBoundTest m n := hmul
      _ = upper n := by
        unfold localCLTSmoothingTailPolynomialBoundTest
        dsimp [upper, C, q, r]
        rw [← hpr]
        ring
  · exact hupper

lemma rigidityPower_mul_localCLTFourierErrorBound_tendsto_zero
    (m : ℕ) (p : ℝ) (hp : p < 3 / 4) :
    Tendsto (fun n : ℕ ↦ rigidityPower n p *
      localCLTFourierErrorBoundTest m n) atTop (𝓝 0) := by
  have hmajor := rigidityPower_mul_localCLTMajorBound_tendsto_zero m p hp
  have hnowrap := rigidityPower_mul_localCLTNoWrapBound_tendsto_zero m p
  have hhigh := rigidityPower_mul_localCLTHighAnnulusBound_tendsto_zero m p
  have hsmooth := rigidityPower_mul_localCLTSmoothingTailBound_tendsto_zero m p
  simpa [localCLTFourierErrorBoundTest, mul_add] using
    ((hmajor.add hnowrap).add hhigh).add hsmooth

lemma rigidityPower_mul_quantitativePhaseDensityError_tendsto_zero
    (m : ℕ) (p : ℝ) (hp : p < 1 / 16) :
    Tendsto (fun n : ℕ ↦ rigidityPower n p *
      quantitativePhaseDensityError m n) atTop (nhds 0) := by
  have hfourier := rigidityPower_mul_localCLTFourierErrorBound_tendsto_zero
    m p (by linarith)
  have hcov := rigidityPower_mul_phaseCovarianceApproxBound_tendsto_zero
    m p hp
  have hsmooth := rigidityPower_mul_phaseLimitingSmoothingError_tendsto_zero
    m p (by linarith)
  have hsum := (hfourier.add
    (hcov.const_mul (phaseCovarianceFourierIntegral m / 2))).add hsmooth
  have hscaled := hsum.const_mul (((2 * Real.pi) ^ (4 * m))⁻¹)
  have hscaled0 : Tendsto (fun n : ℕ ↦ ((2 * Real.pi) ^ (4 * m))⁻¹ *
      (rigidityPower n p * localCLTFourierErrorBoundTest m n +
        phaseCovarianceFourierIntegral m / 2 *
          (rigidityPower n p * phaseCovarianceApproxBound m n) +
        rigidityPower n p * phaseLimitingSmoothingError
          (m := m) (localCLTSmoothingScaleTest n))) atTop (nhds 0) := by
    simpa using hscaled
  apply hscaled0.congr'
  filter_upwards [] with n
  unfold quantitativePhaseDensityError
  ring

noncomputable def growingVelocityCutoff (n : ℕ) : ℝ :=
  rigidityPower n (1 / 128)

lemma growingVelocityCutoff_nonneg (n : ℕ) :
    0 ≤ growingVelocityCutoff n :=
  rigidityPower_nonneg n _

lemma growingVelocityCutoff_tendsto_atTop :
    Tendsto growingVelocityCutoff atTop atTop := by
  change Tendsto (fun n : ℕ ↦ rigidityPower n (1 / 128)) atTop atTop
  exact tendsto_rigidityPower_atTop (by norm_num : (0 : ℝ) < 1 / 128)

lemma rigidityPower_three_over_128_mul_quantitativePhaseDensityError_one_tendsto_zero :
    Tendsto (fun n : ℕ ↦ rigidityPower n (3 / 128) *
      quantitativePhaseDensityError 1 n) atTop (nhds 0) := by
  exact rigidityPower_mul_quantitativePhaseDensityError_tendsto_zero
    1 (3 / 128) (by norm_num)

end Erdos525
