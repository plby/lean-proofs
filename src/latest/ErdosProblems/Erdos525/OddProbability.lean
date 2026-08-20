import ErdosProblems.Erdos525.OddLocal

open scoped BigOperators Topology ComplexConjugate RealInnerProductSpace

namespace Erdos525

open Classical Filter Finset Set MeasureTheory

namespace Odd

lemma phaseSmoothedDensity_nonneg
    (m n : ℕ) (points : Fin m → ℝ) (sigma : ℝ)
    (y : PhaseEuclidean m) :
    0 ≤ phaseSmoothedDensity n points sigma y := by
  unfold phaseSmoothedDensity uniformExpectation
  apply div_nonneg
  · exact Finset.sum_nonneg fun e _ ↦ phaseGaussianKernel_nonneg m sigma _
  · positivity

lemma integrable_phaseSmoothedDensity
    (m n : ℕ) (points : Fin m → ℝ) (sigma : ℝ) (hsigma : 0 < sigma) :
    Integrable (phaseSmoothedDensity n points sigma) := by
  unfold phaseSmoothedDensity uniformExpectation
  apply Integrable.div_const
  classical
  have hsum : ∀ s : Finset (SignVector (2 * n + 1)),
      Integrable (fun y : PhaseEuclidean m ↦
        ∑ e ∈ s, phaseGaussianKernel m sigma
          (normalizedPhaseEuclideanWalk n e points - y)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert e s he ih =>
        simp only [Finset.sum_insert he]
        exact (integrable_phaseGaussianKernel_sub_left m sigma hsigma
          (normalizedPhaseEuclideanWalk n e points)).add ih
  simpa using hsum Finset.univ

lemma continuous_phaseSmoothedDensity
    (m n : ℕ) (points : Fin m → ℝ) (sigma : ℝ) :
    Continuous (phaseSmoothedDensity n points sigma) := by
  unfold phaseSmoothedDensity uniformExpectation
  apply Continuous.div_const
  apply continuous_finset_sum
  intro e _he
  exact (continuous_phaseGaussianKernel m sigma).comp
    (continuous_const.sub continuous_id)

/-- Integrating the odd smoothed density is the expectation of the translated
Gaussian mass. -/
lemma integral_phaseSmoothedDensity
    (n : ℕ) (points : Fin m → ℝ) (sigma : ℝ) (hsigma : 0 < sigma)
    (s : Set (PhaseEuclidean m)) :
    (∫ y : PhaseEuclidean m in s, phaseSmoothedDensity n points sigma y) =
      uniformExpectation (fun e : SignVector (2 * n + 1) ↦
        ∫ y : PhaseEuclidean m in s,
          phaseGaussianKernel m sigma
            (normalizedPhaseEuclideanWalk n e points - y)) := by
  unfold phaseSmoothedDensity uniformExpectation
  rw [integral_div, integral_finsetSum]
  intro e _he
  exact (integrable_phaseGaussianKernel_sub_left m sigma hsigma
    (normalizedPhaseEuclideanWalk n e points)).integrableOn

lemma abs_setIntegral_phaseSmoothedDensity_sub_limiting_le
    (m n : ℕ) (hm : 0 < m) (points : Fin m → ℝ) (sigma delta : ℝ)
    (s : Set (PhaseEuclidean m)) (hsfinite : volume s ≠ ⊤)
    (hdelta : 0 ≤ delta)
    (hclose : ∀ y : PhaseEuclidean m,
      |phaseSmoothedDensity n points sigma y - phaseLimitingDensity y| ≤ delta) :
    |(∫ y in s, phaseSmoothedDensity n points sigma y) -
        ∫ y in s, phaseLimitingDensity y| ≤ delta * volume.real s := by
  let d : PhaseEuclidean m → ℝ := fun y ↦
    phaseSmoothedDensity n points sigma y - phaseLimitingDensity y
  have hdcont : Continuous d :=
    (continuous_phaseSmoothedDensity m n points sigma).sub
      (continuous_phaseLimitingDensity m)
  have hd : IntegrableOn d s :=
    Measure.integrableOn_of_bounded hsfinite hdcont.aestronglyMeasurable
      (Eventually.of_forall fun y ↦ by
        rw [Real.norm_eq_abs]
        exact hclose y)
  have hlim : IntegrableOn (phaseLimitingDensity : PhaseEuclidean m → ℝ) s :=
    (integrable_phaseLimitingDensity m hm).integrableOn
  have hsmooth : IntegrableOn (phaseSmoothedDensity n points sigma) s := by
    apply (hd.add hlim).congr
    filter_upwards [] with y
    dsimp [d]
    ring
  rw [← integral_sub hsmooth hlim]
  simpa only [d, Real.norm_eq_abs] using
    (norm_setIntegral_le_of_norm_le_const (f := d) (C := delta)
      hsfinite.lt_top fun y _hy ↦ by
        simpa only [d, Real.norm_eq_abs] using hclose y)

theorem eventually_uniform_scaled_truncatedPhaseDensity_error
    (m : ℕ) (hm : 0 < m)
    (widthFactor u velocityLower velocityUpper : ℝ)
    (hfactor : 0 ≤ widthFactor) (hu : 0 ≤ u)
    (hvelLower : 0 < velocityLower) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, ∀ points : Fin m → ℝ,
      (∀ r, IsSmooth n (rigiditySmoothScale n) (points r)) →
      IsSpread n (rigiditySmoothScale n) points →
      |(localMeshSize n : ℝ) ^ m *
          (∫ y in truncatedPhaseRegion (m := m) n u
            (widthFactor * localMeshHalfWidth n) velocityLower velocityUpper,
            phaseSmoothedDensity n points
              (prefixScale n * localCLTSmoothingScaleTest n) y) -
        (localMeshSize n : ℝ) ^ m *
          (∫ y in truncatedPhaseRegion (m := m) n u
            (widthFactor * localMeshHalfWidth n) velocityLower velocityUpper,
            phaseLimitingDensity y)| < eps := by
  let C : ℝ := (4 * Real.pi * widthFactor * u *
    ∫ b : ℂ in blockVelocityAnnulus velocityLower velocityUpper, ‖b‖) ^ m
  have hV : 0 ≤ ∫ b : ℂ in blockVelocityAnnulus velocityLower velocityUpper, ‖b‖ :=
    integral_nonneg fun _ ↦ norm_nonneg _
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  let delta : ℝ := eps / (C + 1)
  have hdelta : 0 < delta := div_pos heps (by linarith)
  filter_upwards [Nat.eventually_pos,
      eventually_uniform_phaseSmoothedDensity hm hdelta]
    with n hn hclt
  intro points hsmooth hspread
  let s := truncatedPhaseRegion (m := m) n u
    (widthFactor * localMeshHalfWidth n) velocityLower velocityUpper
  have hsfinite : volume s ≠ ⊤ :=
    volume_truncatedPhaseRegion_ne_top m n hm hn u
      (widthFactor * localMeshHalfWidth n) velocityLower velocityUpper hu
      (mul_nonneg hfactor (by unfold localMeshHalfWidth; positivity)) hvelLower
  have hclose : ∀ y : PhaseEuclidean m,
      |phaseSmoothedDensity n points
          (prefixScale n * localCLTSmoothingScaleTest n) y -
        phaseLimitingDensity y| ≤ delta := fun y ↦
    (hclt points y hsmooth hspread).le
  have hbound := abs_setIntegral_phaseSmoothedDensity_sub_limiting_le
    m n hm points (prefixScale n * localCLTSmoothingScaleTest n)
      delta s hsfinite hdelta.le hclose
  have hmesh : 0 ≤ (localMeshSize n : ℝ) ^ m := by positivity
  have hvol : (localMeshSize n : ℝ) ^ m * volume.real s = C := by
    simpa only [s, C] using
      scaled_volumeReal_truncatedPhaseFactorRegion m n hm hn widthFactor u
        velocityLower velocityUpper hfactor hu hvelLower
  rw [show
      (localMeshSize n : ℝ) ^ m * (∫ y in s,
          phaseSmoothedDensity n points
            (prefixScale n * localCLTSmoothingScaleTest n) y) -
        (localMeshSize n : ℝ) ^ m * (∫ y in s, phaseLimitingDensity y) =
      (localMeshSize n : ℝ) ^ m *
        ((∫ y in s, phaseSmoothedDensity n points
            (prefixScale n * localCLTSmoothingScaleTest n) y) -
          ∫ y in s, phaseLimitingDensity y) by ring,
    abs_mul, abs_of_nonneg hmesh]
  calc
    (localMeshSize n : ℝ) ^ m *
        |(∫ y in s, phaseSmoothedDensity n points
            (prefixScale n * localCLTSmoothingScaleTest n) y) -
          ∫ y in s, phaseLimitingDensity y| ≤
        (localMeshSize n : ℝ) ^ m * (delta * volume.real s) :=
      mul_le_mul_of_nonneg_left hbound hmesh
    _ = delta * C := by rw [← hvol]; ring
    _ < eps := by
      dsimp [delta]
      rw [show eps / (C + 1) * C = eps * (C / (C + 1)) by ring]
      have hfrac : C / (C + 1) < 1 :=
        (div_lt_one (by linarith)).2 (by linarith)
      simpa using mul_lt_mul_of_pos_left hfrac heps

theorem eventually_uniform_scaled_smoothed_truncatedPhaseFactorMass
    (m : ℕ) (hm : 0 < m)
    (widthFactor u velocityLower velocityUpper : ℝ)
    (hfactor : 0 ≤ widthFactor) (hu : 0 ≤ u)
    (hvelLower : 0 < velocityLower) (hvelUpper : 0 ≤ velocityUpper)
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, ∀ points : Fin m → ℝ,
      (∀ r, IsSmooth n (rigiditySmoothScale n) (points r)) →
      IsSpread n (rigiditySmoothScale n) points →
      |(localMeshSize n : ℝ) ^ m *
          (∫ y in truncatedPhaseRegion (m := m) n u
            (widthFactor * localMeshHalfWidth n) velocityLower velocityUpper,
            phaseSmoothedDensity n points
              (prefixScale n * localCLTSmoothingScaleTest n) y) -
        (widthFactor * ((12 * u / Real.pi) *
          blockVelocityMass velocityLower velocityUpper)) ^ m| < eps := by
  let A : ℝ := (widthFactor * ((12 * u / Real.pi) *
    blockVelocityMass velocityLower velocityUpper)) ^ m
  have hhalf : 0 < eps / 2 := by linarith
  have herr := eventually_uniform_scaled_truncatedPhaseDensity_error
    m hm widthFactor u velocityLower velocityUpper hfactor hu hvelLower hhalf
  have hlimit := scaled_truncatedPhaseFactorMass_tendsto m hm widthFactor u
    velocityLower velocityUpper hfactor hu hvelLower hvelUpper
  have hlim : ∀ᶠ n : ℕ in atTop,
      |(localMeshSize n : ℝ) ^ m *
          (∫ y in truncatedPhaseRegion (m := m) n u
            (widthFactor * localMeshHalfWidth n) velocityLower velocityUpper,
            phaseLimitingDensity y) - A| < eps / 2 := by
    have hball := hlimit.eventually (Metric.ball_mem_nhds A hhalf)
    filter_upwards [hball] with n hn
    simpa only [Metric.mem_ball, Real.dist_eq, A] using hn
  filter_upwards [herr, hlim] with n hnerr hnlim
  intro points hsmooth hspread
  have h₁ := hnerr points hsmooth hspread
  change |(localMeshSize n : ℝ) ^ m *
      (∫ y in truncatedPhaseRegion (m := m) n u
        (widthFactor * localMeshHalfWidth n) velocityLower velocityUpper,
        phaseSmoothedDensity n points
          (prefixScale n * localCLTSmoothingScaleTest n) y) - A| < eps
  calc
    _ = |((localMeshSize n : ℝ) ^ m *
          (∫ y in truncatedPhaseRegion (m := m) n u
            (widthFactor * localMeshHalfWidth n) velocityLower velocityUpper,
            phaseSmoothedDensity n points
              (prefixScale n * localCLTSmoothingScaleTest n) y) -
        (localMeshSize n : ℝ) ^ m *
          (∫ y in truncatedPhaseRegion (m := m) n u
            (widthFactor * localMeshHalfWidth n) velocityLower velocityUpper,
            phaseLimitingDensity y)) +
        ((localMeshSize n : ℝ) ^ m *
          (∫ y in truncatedPhaseRegion (m := m) n u
            (widthFactor * localMeshHalfWidth n) velocityLower velocityUpper,
            phaseLimitingDensity y) - A)| := by congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ < eps / 2 + eps / 2 := add_lt_add h₁ hnlim
    _ = eps := by ring

lemma uniformProbability_mul_ballMass_le_integral_thickening
    (n : ℕ) (points : Fin m → ℝ) (sigma r : ℝ) (hsigma : 0 < sigma)
    (s : Set (PhaseEuclidean m)) :
    uniformProbability (fun e : SignVector (2 * n + 1) ↦
        normalizedPhaseEuclideanWalk n e points ∈ s) *
        (∫ x : PhaseEuclidean m in Metric.ball 0 r,
          phaseGaussianKernel m sigma x) ≤
      ∫ y : PhaseEuclidean m in Metric.thickening r s,
        phaseSmoothedDensity n points sigma y := by
  rw [integral_phaseSmoothedDensity n points sigma hsigma]
  rw [uniformProbability_mul_eq_expectation_indicator]
  apply uniformExpectation_mono
  intro e
  by_cases he : normalizedPhaseEuclideanWalk n e points ∈ s
  · rw [if_pos he]
    rw [← integral_ball_phaseGaussianKernel_sub_left m sigma hsigma
      (normalizedPhaseEuclideanWalk n e points) r]
    apply setIntegral_mono_set
    · exact (integrable_phaseGaussianKernel_sub_left m sigma hsigma
        (normalizedPhaseEuclideanWalk n e points)).integrableOn
    · exact Eventually.of_forall fun y ↦
        phaseGaussianKernel_nonneg m sigma
          (normalizedPhaseEuclideanWalk n e points - y)
    · exact Eventually.of_forall fun y hy ↦ by
        change y ∈ Metric.thickening r s
        rw [Metric.mem_thickening_iff]
        exact ⟨normalizedPhaseEuclideanWalk n e points, he, hy⟩
  · rw [if_neg he]
    exact integral_nonneg fun y ↦ phaseGaussianKernel_nonneg m sigma _

lemma uniformProbability_mul_gaussianLower_le_integral_thickening
    (n : ℕ) (points : Fin m → ℝ) (sigma r : ℝ)
    (hsigma : 0 < sigma) (hr : 0 ≤ r) (s : Set (PhaseEuclidean m)) :
    uniformProbability (fun e : SignVector (2 * n + 1) ↦
        normalizedPhaseEuclideanWalk n e points ∈ s) *
        (1 - 2 ^ (2 * m) * Real.exp (-(r ^ 2 / (4 * sigma ^ 2)))) ≤
      ∫ y : PhaseEuclidean m in Metric.thickening r s,
        phaseSmoothedDensity n points sigma y := by
  calc
    _ ≤ uniformProbability (fun e : SignVector (2 * n + 1) ↦
          normalizedPhaseEuclideanWalk n e points ∈ s) *
        (∫ x : PhaseEuclidean m in Metric.ball 0 r,
          phaseGaussianKernel m sigma x) :=
      mul_le_mul_of_nonneg_left
        (phaseGaussianKernel_ball_lower m sigma r hsigma hr)
        (uniformProbability_nonneg _)
    _ ≤ _ := uniformProbability_mul_ballMass_le_integral_thickening
      n points sigma r hsigma s

lemma integral_innerErosion_phaseSmoothedDensity_le
    (n : ℕ) (points : Fin m → ℝ) (sigma r : ℝ)
    (hsigma : 0 < sigma) (hr : 0 ≤ r) (s : Set (PhaseEuclidean m)) :
    (∫ y : PhaseEuclidean m in (Metric.thickening r sᶜ)ᶜ,
        phaseSmoothedDensity n points sigma y) ≤
      uniformProbability (fun e : SignVector (2 * n + 1) ↦
          normalizedPhaseEuclideanWalk n e points ∈ s) +
        2 ^ (2 * m) * Real.exp (-(r ^ 2 / (4 * sigma ^ 2))) := by
  rw [integral_phaseSmoothedDensity n points sigma hsigma]
  let tail : ℝ := 2 ^ (2 * m) * Real.exp (-(r ^ 2 / (4 * sigma ^ 2)))
  calc
    uniformExpectation (fun e : SignVector (2 * n + 1) ↦
        ∫ y : PhaseEuclidean m in (Metric.thickening r sᶜ)ᶜ,
          phaseGaussianKernel m sigma
            (normalizedPhaseEuclideanWalk n e points - y)) ≤
      uniformExpectation (fun e : SignVector (2 * n + 1) ↦
        (if normalizedPhaseEuclideanWalk n e points ∈ s then (1 : ℝ) else 0) +
          tail) := by
      apply uniformExpectation_mono
      intro e
      by_cases he : normalizedPhaseEuclideanWalk n e points ∈ s
      · rw [if_pos he]
        calc
          _ ≤ ∫ y : PhaseEuclidean m,
              phaseGaussianKernel m sigma
                (normalizedPhaseEuclideanWalk n e points - y) :=
            setIntegral_le_integral
              (integrable_phaseGaussianKernel_sub_left m sigma hsigma _)
              (Eventually.of_forall fun y ↦ phaseGaussianKernel_nonneg m sigma _)
          _ = 1 := integral_phaseGaussianKernel_sub_left m sigma hsigma _
          _ ≤ 1 + tail := by
            dsimp [tail]
            exact le_add_of_nonneg_right
              (mul_nonneg (by positivity) (Real.exp_pos _).le)
      · rw [if_neg he, zero_add]
        exact integral_gaussianKernel_innerErosion_le_of_not_mem
          m sigma r hsigma hr s _ he
    _ = uniformProbability (fun e : SignVector (2 * n + 1) ↦
          normalizedPhaseEuclideanWalk n e points ∈ s) + tail := by
      rw [uniformExpectation_add_real]
      rw [uniformExpectation_indicator, uniformExpectation_const_real]
    _ = _ := rfl

noncomputable def phaseBoundaryGaussianTail (m n : ℕ) : ℝ :=
  2 ^ (2 * m) * Real.exp (-(phaseBoundaryRadius n ^ 2 /
    (4 * (prefixScale n * localCLTSmoothingScaleTest n) ^ 2)))

lemma phaseBoundaryGaussianTail_nonneg (m n : ℕ) :
    0 ≤ phaseBoundaryGaussianTail m n := by
  unfold phaseBoundaryGaussianTail
  positivity

lemma phaseBoundaryGaussianTail_le (m n : ℕ) :
    phaseBoundaryGaussianTail m n ≤ Erdos525.phaseBoundaryGaussianTail m n := by
  by_cases hn : n = 0
  · subst n
    simp [phaseBoundaryGaussianTail, Erdos525.phaseBoundaryGaussianTail,
      phaseBoundaryRadius, localCLTSmoothingScaleTest, rigidityPower]
  unfold phaseBoundaryGaussianTail Erdos525.phaseBoundaryGaussianTail
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have ha : 0 < prefixScale n := prefixScale_pos n
  have hs : 0 < localCLTSmoothingScaleTest n := by
    unfold localCLTSmoothingScaleTest
    exact rigidityPower_pos hnpos _
  have hscale : 0 ≤ prefixScale n * localCLTSmoothingScaleTest n ∧
      prefixScale n * localCLTSmoothingScaleTest n ≤
        localCLTSmoothingScaleTest n := by
    constructor
    · exact mul_nonneg ha.le hs.le
    · exact mul_le_of_le_one_left hs.le (prefixScale_le_one n)
  have hsq : (prefixScale n * localCLTSmoothingScaleTest n) ^ 2 ≤
      localCLTSmoothingScaleTest n ^ 2 := by
    exact (sq_le_sq₀ hscale.1 hs.le).2 hscale.2
  have hden : 4 * (prefixScale n * localCLTSmoothingScaleTest n) ^ 2 ≤
      4 * localCLTSmoothingScaleTest n ^ 2 := by nlinarith
  have hquot : phaseBoundaryRadius n ^ 2 /
        (4 * localCLTSmoothingScaleTest n ^ 2) ≤
      phaseBoundaryRadius n ^ 2 /
        (4 * (prefixScale n * localCLTSmoothingScaleTest n) ^ 2) :=
    div_le_div_of_nonneg_left (sq_nonneg (phaseBoundaryRadius n))
      (by positivity) hden
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.exp_le_exp.mpr (neg_le_neg hquot)

lemma scaled_phaseBoundaryGaussianTail_tendsto_zero (m : ℕ) :
    Tendsto (fun n : ℕ ↦
      (localMeshSize n : ℝ) ^ m * phaseBoundaryGaussianTail m n)
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦
      mul_nonneg (by positivity) (phaseBoundaryGaussianTail_nonneg m n)
  · exact Eventually.of_forall fun n ↦
      mul_le_mul_of_nonneg_left (phaseBoundaryGaussianTail_le m n) (by positivity)
  · exact Erdos525.scaled_phaseBoundaryGaussianTail_tendsto_zero m

noncomputable def factoredTruncatedPhaseProbability
    (m n : ℕ) (points : Fin m → ℝ)
    (widthFactor u velocityLower velocityUpper : ℝ) : ℝ :=
  uniformProbability (fun e : SignVector (2 * n + 1) ↦
    normalizedPhaseEuclideanWalk n e points ∈
      truncatedPhaseRegion (m := m) n u
        (widthFactor * localMeshHalfWidth n)
        velocityLower velocityUpper)

theorem eventually_uniform_scaled_factoredTruncatedPhaseProbability_bracket
    (m : ℕ) (hm : 0 < m)
    (widthFactor u velocityLower velocityUpper eta tol : ℝ)
    (hu : 0 ≤ u) (hvelLower : 0 < velocityLower)
    (heta : 0 < eta) (hetaFactor : eta < widthFactor)
    (hetaU : eta < u) (hetaLower : eta < velocityLower)
    (hetaUpper : eta < velocityUpper) (htol : 0 < tol) :
    ∀ᶠ n : ℕ in atTop, ∀ points : Fin m → ℝ,
      (∀ r, IsSmooth n (rigiditySmoothScale n) (points r)) →
      IsSpread n (rigiditySmoothScale n) points →
      ((widthFactor - eta) * ((12 * (u - eta) / Real.pi) *
          blockVelocityMass (velocityLower + eta) (velocityUpper - eta))) ^ m - tol <
        (localMeshSize n : ℝ) ^ m *
          factoredTruncatedPhaseProbability m n points widthFactor u
            velocityLower velocityUpper ∧
      (localMeshSize n : ℝ) ^ m *
          factoredTruncatedPhaseProbability m n points widthFactor u
            velocityLower velocityUpper <
        ((widthFactor + eta) * ((12 * (u + eta) / Real.pi) *
          blockVelocityMass (velocityLower - eta) (velocityUpper + eta))) ^ m + tol := by
  let Aminus : ℝ := ((widthFactor - eta) * ((12 * (u - eta) / Real.pi) *
    blockVelocityMass (velocityLower + eta) (velocityUpper - eta))) ^ m
  let Aplus : ℝ := ((widthFactor + eta) * ((12 * (u + eta) / Real.pi) *
    blockVelocityMass (velocityLower - eta) (velocityUpper + eta))) ^ m
  have htolHalf : 0 < tol / 2 := by linarith
  have hmassMinus :=
    eventually_uniform_scaled_smoothed_truncatedPhaseFactorMass
      m hm (widthFactor - eta) (u - eta) (velocityLower + eta)
      (velocityUpper - eta) (sub_nonneg.mpr hetaFactor.le)
      (sub_nonneg.mpr hetaU.le) (by linarith) (by linarith) htolHalf
  have hmassPlus :=
    eventually_uniform_scaled_smoothed_truncatedPhaseFactorMass
      m hm (widthFactor + eta) (u + eta) (velocityLower - eta)
      (velocityUpper + eta) (by linarith) (by linarith) (by linarith)
      (by linarith) htolHalf
  have htail : ∀ᶠ n : ℕ in atTop,
      (localMeshSize n : ℝ) ^ m * phaseBoundaryGaussianTail m n < tol / 2 :=
    (scaled_phaseBoundaryGaussianTail_tendsto_zero m).eventually
      (Iio_mem_nhds htolHalf)
  filter_upwards [Nat.eventually_pos,
      eventually_thickening_factoredTruncatedMeshRegion_subset_expanded
        m widthFactor u velocityLower velocityUpper eta
        (le_trans heta.le hetaFactor.le) hu hvelLower heta,
      eventually_factoredShrunkMeshRegion_subset_innerErosion
        m widthFactor u velocityLower velocityUpper eta heta hetaFactor hetaU
          hvelLower hetaUpper,
      hmassMinus, hmassPlus, htail]
    with n hn houter hinner hmassMinusN hmassPlusN htailN
  intro points hsmooth hspread
  let q : ℝ := (localMeshSize n : ℝ) ^ m
  let p : ℝ := factoredTruncatedPhaseProbability m n points widthFactor u
    velocityLower velocityUpper
  let tail : ℝ := phaseBoundaryGaussianTail m n
  let sigma : ℝ := prefixScale n * localCLTSmoothingScaleTest n
  let target := truncatedPhaseRegion (m := m) n u
    (widthFactor * localMeshHalfWidth n) velocityLower velocityUpper
  let expanded := truncatedPhaseRegion (m := m) n (u + eta)
    ((widthFactor + eta) * localMeshHalfWidth n)
    (velocityLower - eta) (velocityUpper + eta)
  let shrunk := truncatedPhaseRegion (m := m) n (u - eta)
    ((widthFactor - eta) * localMeshHalfWidth n)
    (velocityLower + eta) (velocityUpper - eta)
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    exact mul_pos (prefixScale_pos n) (by
      unfold localCLTSmoothingScaleTest
      exact rigidityPower_pos hn _)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htail0 : 0 ≤ tail := by
    dsimp [tail]
    exact phaseBoundaryGaussianTail_nonneg m n
  have hp0 : 0 ≤ p := by
    dsimp [p, factoredTruncatedPhaseProbability]
    exact uniformProbability_nonneg _
  have hp1 : p ≤ 1 := by
    dsimp [p, factoredTruncatedPhaseProbability]
    exact uniformProbability_le_one _
  have hInt := integrable_phaseSmoothedDensity m n points sigma hsigma
  have hnonneg : ∀ y : PhaseEuclidean m,
      0 ≤ phaseSmoothedDensity n points sigma y :=
    phaseSmoothedDensity_nonneg m n points sigma
  have houterIntegral :
      (∫ y in Metric.thickening (phaseBoundaryRadius n) target,
          phaseSmoothedDensity n points sigma y) ≤
        ∫ y in expanded, phaseSmoothedDensity n points sigma y := by
    exact setIntegral_mono_set hInt.integrableOn (Eventually.of_forall hnonneg)
      (Eventually.of_forall fun x hx ↦ by
        change x ∈ expanded
        apply houter
        change x ∈ Metric.thickening (phaseBoundaryRadius n) target
        exact hx)
  have hupperSandwich :=
    uniformProbability_mul_gaussianLower_le_integral_thickening
      n points sigma (phaseBoundaryRadius n) hsigma
      (phaseBoundaryRadius_nonneg n) target
  have hupperRaw : p * (1 - tail) ≤
      ∫ y in expanded, phaseSmoothedDensity n points sigma y := by
    apply hupperSandwich.trans houterIntegral
  have hupperScaled : q * p ≤
      q * (∫ y in expanded, phaseSmoothedDensity n points sigma y) + q * tail := by
    have hmain := mul_le_mul_of_nonneg_left hupperRaw hq
    have hpt : q * p * tail ≤ q * tail := by
      have hpTail := mul_le_mul_of_nonneg_right hp1 htail0
      nlinarith
    nlinarith
  have hinnerIntegral :
      (∫ y in shrunk, phaseSmoothedDensity n points sigma y) ≤
        ∫ y in (Metric.thickening (phaseBoundaryRadius n) targetᶜ)ᶜ,
          phaseSmoothedDensity n points sigma y := by
    exact setIntegral_mono_set hInt.integrableOn (Eventually.of_forall hnonneg)
      (Eventually.of_forall fun x hx ↦ by
        change x ∈ (Metric.thickening (phaseBoundaryRadius n) targetᶜ)ᶜ
        apply hinner
        change x ∈ shrunk
        exact hx)
  have hlowerSandwich := integral_innerErosion_phaseSmoothedDensity_le
    n points sigma (phaseBoundaryRadius n) hsigma
    (phaseBoundaryRadius_nonneg n) target
  have hlowerRaw :
      (∫ y in shrunk, phaseSmoothedDensity n points sigma y) ≤ p + tail := by
    exact hinnerIntegral.trans (by
      simpa only [p, tail, sigma, target, factoredTruncatedPhaseProbability,
        phaseBoundaryGaussianTail] using hlowerSandwich)
  have hlowerScaled :
      q * (∫ y in shrunk, phaseSmoothedDensity n points sigma y) ≤
        q * p + q * tail := by
    have := mul_le_mul_of_nonneg_left hlowerRaw hq
    nlinarith
  have hminus := hmassMinusN points hsmooth hspread
  have hplus := hmassPlusN points hsmooth hspread
  have hminusBounds := abs_lt.mp (by
    simpa only [q, sigma, shrunk, Aminus] using hminus)
  have hplusBounds := abs_lt.mp (by
    simpa only [q, sigma, expanded, Aplus] using hplus)
  have htailBound : q * tail < tol / 2 := by
    simpa only [q, tail] using htailN
  constructor
  · change Aminus - tol < q * p
    nlinarith [hminusBounds.1, hlowerScaled]
  · change q * p < Aplus + tol
    nlinarith [hplusBounds.2, hupperScaled]

theorem eventually_uniform_scaled_factoredTruncatedPhaseProbability
    (m : ℕ) (hm : 0 < m)
    (widthFactor u velocityLower velocityUpper : ℝ)
    (hfactor : 0 < widthFactor) (hu : 0 < u)
    (hvelLower : 0 < velocityLower) (hvelUpper : 0 < velocityUpper)
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, ∀ points : Fin m → ℝ,
      (∀ r, IsSmooth n (rigiditySmoothScale n) (points r)) →
      IsSpread n (rigiditySmoothScale n) points →
      |(localMeshSize n : ℝ) ^ m *
          factoredTruncatedPhaseProbability m n points widthFactor u
            velocityLower velocityUpper -
        ((widthFactor * ((12 * u / Real.pi) *
          blockVelocityMass velocityLower velocityUpper)) ^ m)| < eps := by
  let A : ℝ := (widthFactor * ((12 * u / Real.pi) *
    blockVelocityMass velocityLower velocityUpper)) ^ m
  let etaSeq : ℕ → ℝ := fun k ↦ 1 / (k + 1 : ℝ)
  have hetaZero : Tendsto etaSeq atTop (nhds 0) := by
    simpa only [etaSeq] using tendsto_one_div_add_atTop_nhds_zero_nat
  have hplus := (Erdos525.continuousAt_expandedFactoredTruncatedPhaseIntensity
    m widthFactor u velocityLower velocityUpper).tendsto.comp hetaZero
  have hminus := (Erdos525.continuousAt_shrunkFactoredTruncatedPhaseIntensity
    m widthFactor u velocityLower velocityUpper).tendsto.comp hetaZero
  have hplus' : Tendsto (fun k : ℕ ↦
      ((widthFactor + etaSeq k) * ((12 * (u + etaSeq k) / Real.pi) *
        blockVelocityMass (velocityLower - etaSeq k)
          (velocityUpper + etaSeq k))) ^ m) atTop (nhds A) := by
    simpa [Function.comp_def, A] using hplus
  have hminus' : Tendsto (fun k : ℕ ↦
      ((widthFactor - etaSeq k) * ((12 * (u - etaSeq k) / Real.pi) *
        blockVelocityMass (velocityLower + etaSeq k)
          (velocityUpper - etaSeq k))) ^ m) atTop (nhds A) := by
    simpa [Function.comp_def, A] using hminus
  have hhalf : 0 < eps / 2 := by linarith
  have hplusClose : ∀ᶠ k : ℕ in atTop,
      ((widthFactor + etaSeq k) * ((12 * (u + etaSeq k) / Real.pi) *
        blockVelocityMass (velocityLower - etaSeq k)
          (velocityUpper + etaSeq k))) ^ m < A + eps / 2 :=
    hplus'.eventually (Iio_mem_nhds (lt_add_of_pos_right A hhalf))
  have hminusClose : ∀ᶠ k : ℕ in atTop,
      A - eps / 2 <
        ((widthFactor - etaSeq k) * ((12 * (u - etaSeq k) / Real.pi) *
          blockVelocityMass (velocityLower + etaSeq k)
            (velocityUpper - etaSeq k))) ^ m :=
    hminus'.eventually (Ioi_mem_nhds (sub_lt_self A hhalf))
  have hetaFactor : ∀ᶠ k : ℕ in atTop, etaSeq k < widthFactor :=
    hetaZero.eventually (Iio_mem_nhds hfactor)
  have hetaU : ∀ᶠ k : ℕ in atTop, etaSeq k < u :=
    hetaZero.eventually (Iio_mem_nhds hu)
  have hetaLower : ∀ᶠ k : ℕ in atTop, etaSeq k < velocityLower :=
    hetaZero.eventually (Iio_mem_nhds hvelLower)
  have hetaUpper : ∀ᶠ k : ℕ in atTop, etaSeq k < velocityUpper :=
    hetaZero.eventually (Iio_mem_nhds hvelUpper)
  rcases (hplusClose.and (hminusClose.and
      (hetaFactor.and (hetaU.and (hetaLower.and hetaUpper))))).exists with
    ⟨k, hplusK, hminusK, hetaFactorK, hetaUK, hetaLowerK, hetaUpperK⟩
  have hetaPos : 0 < etaSeq k := by
    dsimp [etaSeq]
    positivity
  have hbracket :=
    eventually_uniform_scaled_factoredTruncatedPhaseProbability_bracket
      m hm widthFactor u velocityLower velocityUpper (etaSeq k) (eps / 2)
      hu.le hvelLower hetaPos hetaFactorK hetaUK hetaLowerK hetaUpperK hhalf
  filter_upwards [hbracket] with n hn
  intro points hsmooth hspread
  have h := hn points hsmooth hspread
  rw [abs_lt]
  dsimp only [A] at hminusK hplusK ⊢
  constructor
  · nlinarith [h.1, hminusK]
  · nlinarith [h.2, hplusK]

end Odd

end Erdos525
