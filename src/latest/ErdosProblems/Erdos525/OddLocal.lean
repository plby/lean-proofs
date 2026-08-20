import ErdosProblems.Erdos525.OddCore

open scoped BigOperators Topology ComplexConjugate RealInnerProductSpace

namespace Erdos525

open Classical Filter Finset Set MeasureTheory

namespace Odd

noncomputable def limitingWeightedNormSq (y : PhaseEuclidean m) : ℝ :=
  ∑ r : Fin m, (
    (y (r, 0) ^ 2 + y (r, 1) ^ 2) +
      3 * (y (r, 2) ^ 2 + y (r, 3) ^ 2))

lemma norm_sq_le_limitingWeightedNormSq (y : PhaseEuclidean m) :
    ‖y‖ ^ 2 ≤ limitingWeightedNormSq y := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  unfold limitingWeightedNormSq
  apply Finset.sum_le_sum
  intro r _hr
  simp only [Fin.sum_univ_four]
  nlinarith [sq_nonneg (y (r, 2)), sq_nonneg (y (r, 3))]

lemma phaseLimitingDensity_eq (y : PhaseEuclidean m) :
    phaseLimitingDensity y =
      (3 / Real.pi ^ 2) ^ m * Real.exp (-limitingWeightedNormSq y) := by
  unfold Erdos525.phaseLimitingDensity limitingWeightedNormSq
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Real.exp_sum]
  congr 2
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  ring

lemma phaseLimitingDensity_nonneg (y : PhaseEuclidean m) :
    0 ≤ phaseLimitingDensity y := by
  rw [phaseLimitingDensity_eq]
  positivity

lemma phaseLimitingDensity_le_gaussian (y : PhaseEuclidean m) :
    phaseLimitingDensity y ≤
      (3 / Real.pi ^ 2) ^ m * Real.exp (-‖y‖ ^ 2) := by
  rw [phaseLimitingDensity_eq]
  gcongr
  exact norm_sq_le_limitingWeightedNormSq y

lemma phaseLimitingDensity_le_const (y : PhaseEuclidean m) :
    phaseLimitingDensity y ≤ (3 / Real.pi ^ 2) ^ m := by
  calc
    phaseLimitingDensity y ≤
        (3 / Real.pi ^ 2) ^ m * Real.exp (-‖y‖ ^ 2) :=
      phaseLimitingDensity_le_gaussian y
    _ ≤ (3 / Real.pi ^ 2) ^ m * 1 := by
      gcongr
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
    _ = _ := mul_one _

lemma phaseLimitingDensity_tendsto_cocompact_zero :
    Tendsto (phaseLimitingDensity : PhaseEuclidean m → ℝ)
      (cocompact _) (𝓝 0) := by
  letI : ProperSpace (PhaseEuclidean m) :=
    FiniteDimensional.proper_real (PhaseEuclidean m)
  have hnorm : Tendsto (fun y : PhaseEuclidean m ↦ ‖y‖)
      (cocompact (PhaseEuclidean m)) atTop :=
    tendsto_norm_cocompact_atTop (E := PhaseEuclidean m)
  have hsq : Tendsto (fun y : PhaseEuclidean m ↦ ‖y‖ ^ 2)
      (cocompact _) atTop :=
    (tendsto_pow_atTop (α := ℝ) (by norm_num)).comp hnorm
  have hexp : Tendsto (fun y : PhaseEuclidean m ↦ Real.exp (-‖y‖ ^ 2))
      (cocompact _) (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero.comp hsq
  have hupper := hexp.const_mul ((3 / Real.pi ^ 2) ^ m)
  simp only [mul_zero] at hupper
  apply squeeze_zero'
  · exact Eventually.of_forall phaseLimitingDensity_nonneg
  · exact Eventually.of_forall phaseLimitingDensity_le_gaussian
  · exact hupper

lemma uniformContinuous_phaseLimitingDensity :
    UniformContinuous (phaseLimitingDensity : PhaseEuclidean m → ℝ) :=
  by
    letI : ProperSpace (PhaseEuclidean m) :=
      FiniteDimensional.proper_real (PhaseEuclidean m)
    exact (continuous_phaseLimitingDensity m).uniformContinuous_of_tendsto_cocompact
      phaseLimitingDensity_tendsto_cocompact_zero


/-- Gaussian smoothing of the exact odd interval walk. -/
noncomputable def phaseSmoothedDensity (n : ℕ) (points : Fin m → ℝ)
    (sigma : ℝ) (y : PhaseEuclidean m) : ℝ :=
  uniformExpectation fun e : SignVector (2 * n + 1) ↦
    phaseGaussianKernel m sigma
      (normalizedPhaseEuclideanWalk n e points - y)

lemma phaseGaussianKernel_smul (m : ℕ) (a sigma : ℝ)
    (ha : 0 < a) (hsigma : 0 < sigma) (x : PhaseEuclidean m) :
    phaseGaussianKernel m (a * sigma) (a • x) =
      ((a ^ 2)⁻¹ ^ (2 * m)) * phaseGaussianKernel m sigma x := by
  have ha0 : a ≠ 0 := ha.ne'
  have hs0 : sigma ≠ 0 := hsigma.ne'
  have hnorm : ‖a • x‖ = a * ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  have hbase :
      2 * Real.pi / (a * sigma) ^ 2 =
        (a ^ 2)⁻¹ * (2 * Real.pi / sigma ^ 2) := by
    field_simp [ha0, hs0]
  have hexp :
      -((a * ‖x‖) ^ 2 / (2 * (a * sigma) ^ 2)) =
        -(‖x‖ ^ 2 / (2 * sigma ^ 2)) := by
    field_simp [ha0, hs0]
  unfold phaseGaussianKernel
  rw [hnorm, hbase, mul_pow, hexp]
  ring

lemma phaseGaussianKernel_affine (m : ℕ) (a sigma : ℝ)
    (ha : 0 < a) (hsigma : 0 < sigma)
    (x d y : PhaseEuclidean m) :
    phaseGaussianKernel m (a * sigma) (a • x + d - y) =
      ((a ^ 2)⁻¹ ^ (2 * m)) *
        phaseGaussianKernel m sigma (x - a⁻¹ • (y - d)) := by
  have ha0 : a ≠ 0 := ha.ne'
  rw [show a • x + d - y = a • (x - a⁻¹ • (y - d)) by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ ha0, one_smul]
    module]
  exact phaseGaussianKernel_smul m a sigma ha hsigma _

/-- Exact density formula after conditioning on the last sign. -/
lemma phaseSmoothedDensity_eq_average (n : ℕ) (hn : 0 < n)
    (points : Fin m → ℝ) (sigma : ℝ) (hsigma : 0 < sigma)
    (y : PhaseEuclidean m) :
    phaseSmoothedDensity n points (prefixScale n * sigma) y =
      ((prefixScale n ^ 2)⁻¹ ^ (2 * m)) *
        (Erdos525.phaseSmoothedDensity n points sigma
            ((prefixScale n)⁻¹ • (y - extraPhaseEuclidean n false points)) +
          Erdos525.phaseSmoothedDensity n points sigma
            ((prefixScale n)⁻¹ • (y - extraPhaseEuclidean n true points))) / 2 := by
  rw [phaseSmoothedDensity, uniformExpectation_split]
  simp_rw [normalizedPhaseEuclideanWalk_appendSign]
  simp_rw [phaseGaussianKernel_affine m (prefixScale n) sigma
    (prefixScale_pos n) hsigma]
  rw [Erdos525.phaseSmoothedDensity_eq_expectation_kernel,
    Erdos525.phaseSmoothedDensity_eq_expectation_kernel]
  rw [uniformExpectation_const_mul, uniformExpectation_const_mul]
  ring

noncomputable def densityScaleFactor (m n : ℕ) : ℝ :=
  ((prefixScale n ^ 2)⁻¹ ^ (2 * m))

lemma densityScaleFactor_pos (m n : ℕ) : 0 < densityScaleFactor m n := by
  unfold densityScaleFactor
  exact pow_pos (inv_pos.mpr (sq_pos_of_pos (prefixScale_pos n))) _

lemma densityScaleFactor_tendsto_one (m : ℕ) :
    Tendsto (densityScaleFactor m) atTop (𝓝 1) := by
  have hsq : Tendsto (fun n : ℕ ↦ prefixScale n ^ 2) atTop (𝓝 1) := by
    simpa only [one_pow] using prefixScale_tendsto_one.pow 2
  have hinv : Tendsto (fun n : ℕ ↦ (prefixScale n ^ 2)⁻¹)
      atTop (𝓝 1) := by
    simpa only [inv_one] using hsq.inv₀ (by norm_num)
  change Tendsto (fun n : ℕ ↦ (prefixScale n ^ 2)⁻¹ ^ (2 * m))
    atTop (𝓝 1)
  simpa only [one_pow] using hinv.pow (2 * m)

lemma prefixScale_inv_tendsto_one :
    Tendsto (fun n : ℕ ↦ (prefixScale n)⁻¹) atTop (𝓝 1) := by
  simpa only [inv_one] using prefixScale_tendsto_one.inv₀ (by norm_num)

/-- The vanishing perturbation and the asymptotically trivial dilation in the
odd interval model do not change the limiting phase density, uniformly in the
spatial target and in the conditioned final sign. -/
lemma eventually_uniform_phaseLimitingDensity_affine
    {m : ℕ} (hm : 0 < m) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, ∀ (b : Bool) (points : Fin m → ℝ)
        (y : PhaseEuclidean m),
      |phaseLimitingDensity
          ((prefixScale n)⁻¹ • (y - extraPhaseEuclidean n b points)) -
        phaseLimitingDensity y| < eps := by
  let C : ℝ := (3 / Real.pi ^ 2) ^ m
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have htail0 : Tendsto (fun R : ℝ ↦ C * Real.exp (-R ^ 2))
      atTop (𝓝 0) := by
    have hsq : Tendsto (fun R : ℝ ↦ R ^ 2) atTop atTop :=
      tendsto_pow_atTop (α := ℝ) (by norm_num)
    have hexp : Tendsto (fun R : ℝ ↦ Real.exp (-R ^ 2))
        atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero.comp hsq
    simpa only [mul_zero] using hexp.const_mul C
  have htailEvent : ∀ᶠ R : ℝ in atTop,
      C * Real.exp (-R ^ 2) < eps / 2 :=
    htail0.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < eps / 2))
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp htailEvent
  let T : ℝ := max 1 R₀
  let R : ℝ := T + 1
  have hT : 0 < T := lt_of_lt_of_le (by norm_num) (le_max_left 1 R₀)
  have hR : 0 < R := by dsimp [R]; linarith
  have htail : C * Real.exp (-T ^ 2) < eps / 2 := by
    exact hR₀ T (le_max_right 1 R₀)
  obtain ⟨delta, hdelta, huc⟩ :=
    (Metric.uniformContinuous_iff.mp
      (uniformContinuous_phaseLimitingDensity (m := m))) eps heps
  have hInvDiff : Tendsto (fun n : ℕ ↦ |(prefixScale n)⁻¹ - 1|)
      atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using
      (prefixScale_inv_tendsto_one.sub_const 1).abs
  filter_upwards [Nat.eventually_pos,
      hInvDiff.eventually
        (Iio_mem_nhds (show 0 < delta / (2 * R) from
          div_pos hdelta (mul_pos (by norm_num) hR))),
      prefixScale_inv_tendsto_one.eventually
        (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2)),
      eventually_uniform_norm_extraPhaseEuclidean_lt
        (m := m) (show 0 < min 1 (delta / 4) from
          lt_min (by norm_num) (by linarith : 0 < delta / 4))]
    with n hn hInvDiffSmall hInvTwo hExtra
  intro b points y
  let d : PhaseEuclidean m := extraPhaseEuclidean n b points
  let y' : PhaseEuclidean m := (prefixScale n)⁻¹ • (y - d)
  have hd : ‖d‖ < min 1 (delta / 4) := hExtra b points
  have hdOne : ‖d‖ < 1 := hd.trans_le (min_le_left _ _)
  have hdDelta : ‖d‖ < delta / 4 := hd.trans_le (min_le_right _ _)
  have hinvPos : 0 < (prefixScale n)⁻¹ := inv_pos.mpr (prefixScale_pos n)
  have hinvOne : 1 ≤ (prefixScale n)⁻¹ :=
    (one_le_inv₀ (prefixScale_pos n)).2 (prefixScale_le_one n)
  by_cases hy : ‖y‖ ≤ R
  · have htermOne : |(prefixScale n)⁻¹ - 1| * ‖y‖ < delta / 2 := by
      have hle : |(prefixScale n)⁻¹ - 1| * ‖y‖ ≤
          |(prefixScale n)⁻¹ - 1| * R :=
        mul_le_mul_of_nonneg_left hy (abs_nonneg _)
      have hlt : |(prefixScale n)⁻¹ - 1| * R < delta / 2 := by
        calc
          |(prefixScale n)⁻¹ - 1| * R < (delta / (2 * R)) * R :=
            mul_lt_mul_of_pos_right hInvDiffSmall hR
          _ = delta / 2 := by field_simp
      exact hle.trans_lt hlt
    have htermTwo : |(prefixScale n)⁻¹| * ‖d‖ < delta / 2 := by
      rw [abs_of_pos hinvPos]
      nlinarith [norm_nonneg d]
    have hdist : dist y' y < delta := by
      rw [dist_eq_norm]
      have heq : y' - y =
          ((prefixScale n)⁻¹ - 1) • y - (prefixScale n)⁻¹ • d := by
        dsimp [y']
        module
      rw [heq]
      calc
        ‖((prefixScale n)⁻¹ - 1) • y - (prefixScale n)⁻¹ • d‖ ≤
            ‖((prefixScale n)⁻¹ - 1) • y‖ +
              ‖(prefixScale n)⁻¹ • d‖ := norm_sub_le _ _
        _ = |(prefixScale n)⁻¹ - 1| * ‖y‖ +
              |(prefixScale n)⁻¹| * ‖d‖ := by
            simp only [norm_smul, Real.norm_eq_abs]
        _ < delta := by linarith
    simpa only [y', Real.dist_eq] using huc hdist
  · have hyLarge : R < ‖y‖ := lt_of_not_ge hy
    have hsubLarge : T < ‖y - d‖ := by
      have hreverse := norm_sub_norm_le y d
      dsimp [R] at hyLarge
      linarith
    have hy'Large : T < ‖y'‖ := by
      rw [show ‖y'‖ = (prefixScale n)⁻¹ * ‖y - d‖ by
        dsimp [y']
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hinvPos]]
      have hmul : ‖y - d‖ ≤ (prefixScale n)⁻¹ * ‖y - d‖ := by
        nlinarith [norm_nonneg (y - d)]
      exact hsubLarge.trans_le hmul
    have hyTail : phaseLimitingDensity y < eps / 2 := by
      calc
        phaseLimitingDensity y ≤ C * Real.exp (-‖y‖ ^ 2) := by
          simpa only [C] using phaseLimitingDensity_le_gaussian y
        _ ≤ C * Real.exp (-T ^ 2) := by
          gcongr
          nlinarith [norm_nonneg y]
        _ < eps / 2 := htail
    have hy'Tail : phaseLimitingDensity y' < eps / 2 := by
      calc
        phaseLimitingDensity y' ≤ C * Real.exp (-‖y'‖ ^ 2) := by
          simpa only [C] using phaseLimitingDensity_le_gaussian y'
        _ ≤ C * Real.exp (-T ^ 2) := by
          gcongr
        _ < eps / 2 := htail
    calc
      |phaseLimitingDensity y' - phaseLimitingDensity y| ≤
          |phaseLimitingDensity y'| + |phaseLimitingDensity y| :=
        abs_sub _ _
      _ = phaseLimitingDensity y' + phaseLimitingDensity y := by
        rw [abs_of_nonneg (phaseLimitingDensity_nonneg y'),
          abs_of_nonneg (phaseLimitingDensity_nonneg y)]
      _ < eps := by linarith

/-- Uniform local central limit theorem for the odd integer interval
`[-n,n+1]`.  It is obtained from the symmetric theorem by conditioning on the
last coefficient; the normalization factor and the deterministic last-step
translation are both absorbed uniformly. -/
theorem eventually_uniform_phaseSmoothedDensity
    {m : ℕ} (hm : 0 < m) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, ∀ (points : Fin m → ℝ)
        (y : PhaseEuclidean m),
      (∀ r, IsSmooth n (rigiditySmoothScale n) (points r)) →
      IsSpread n (rigiditySmoothScale n) points →
      |Odd.phaseSmoothedDensity n points
          (prefixScale n * localCLTSmoothingScaleTest n) y -
        phaseLimitingDensity y| < eps := by
  let C : ℝ := (3 / Real.pi ^ 2) ^ m
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hCOne : 0 < C + 1 := by linarith
  have hFactorDiff : Tendsto
      (fun n : ℕ ↦ |densityScaleFactor m n - 1|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using
      ((densityScaleFactor_tendsto_one m).sub_const 1).abs
  filter_upwards [Nat.eventually_pos,
      Erdos525.eventually_uniform_phaseSmoothedDensity hm
        (show 0 < eps / 16 by linarith),
      eventually_uniform_phaseLimitingDensity_affine hm
        (show 0 < eps / 16 by linarith),
      hFactorDiff.eventually
        (Iio_mem_nhds (show 0 < eps / (4 * (C + 1)) by positivity)),
      (densityScaleFactor_tendsto_one m).eventually
        (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))]
    with n hn hEven hAffine hFactorSmall hFactorTwo
  intro points y hsmooth hspread
  let c : ℝ := densityScaleFactor m n
  let d₀ : PhaseEuclidean m := extraPhaseEuclidean n false points
  let d₁ : PhaseEuclidean m := extraPhaseEuclidean n true points
  let y₀ : PhaseEuclidean m := (prefixScale n)⁻¹ • (y - d₀)
  let y₁ : PhaseEuclidean m := (prefixScale n)⁻¹ • (y - d₁)
  let E₀ : ℝ := Erdos525.phaseSmoothedDensity n points
    (localCLTSmoothingScaleTest n) y₀
  let E₁ : ℝ := Erdos525.phaseSmoothedDensity n points
    (localCLTSmoothingScaleTest n) y₁
  let L : ℝ := phaseLimitingDensity y
  have hEven₀ : |E₀ - phaseLimitingDensity y₀| < eps / 16 :=
    hEven points y₀ hsmooth hspread
  have hEven₁ : |E₁ - phaseLimitingDensity y₁| < eps / 16 :=
    hEven points y₁ hsmooth hspread
  have hAffine₀ : |phaseLimitingDensity y₀ - L| < eps / 16 := by
    exact hAffine false points y
  have hAffine₁ : |phaseLimitingDensity y₁ - L| < eps / 16 := by
    exact hAffine true points y
  have hE₀ : |E₀ - L| < eps / 8 := by
    calc
      |E₀ - L| ≤ |E₀ - phaseLimitingDensity y₀| +
          |phaseLimitingDensity y₀ - L| := by
        rw [show E₀ - L =
          (E₀ - phaseLimitingDensity y₀) +
            (phaseLimitingDensity y₀ - L) by ring]
        exact abs_add_le _ _
      _ < eps / 16 + eps / 16 := add_lt_add hEven₀ hAffine₀
      _ = eps / 8 := by ring
  have hE₁ : |E₁ - L| < eps / 8 := by
    calc
      |E₁ - L| ≤ |E₁ - phaseLimitingDensity y₁| +
          |phaseLimitingDensity y₁ - L| := by
        rw [show E₁ - L =
          (E₁ - phaseLimitingDensity y₁) +
            (phaseLimitingDensity y₁ - L) by ring]
        exact abs_add_le _ _
      _ < eps / 16 + eps / 16 := add_lt_add hEven₁ hAffine₁
      _ = eps / 8 := by ring
  let A : ℝ := (E₀ + E₁) / 2
  have hA : |A - L| < eps / 8 := by
    rw [show A - L = ((E₀ - L) + (E₁ - L)) / 2 by
      dsimp [A]
      ring, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      |(E₀ - L) + (E₁ - L)| / 2 ≤
          (|E₀ - L| + |E₁ - L|) / 2 := by
        gcongr
        exact abs_add_le _ _
      _ < (eps / 8 + eps / 8) / 2 := by gcongr
      _ = eps / 8 := by ring
  have hcPos : 0 < c := densityScaleFactor_pos m n
  have hFirst : c * |A - L| < eps / 4 := by
    calc
      c * |A - L| ≤ 2 * |A - L| :=
        mul_le_mul_of_nonneg_right hFactorTwo.le (abs_nonneg _)
      _ < 2 * (eps / 8) := mul_lt_mul_of_pos_left hA (by norm_num)
      _ = eps / 4 := by ring
  have hL : |L| ≤ C := by
    rw [abs_of_nonneg (phaseLimitingDensity_nonneg y)]
    simpa only [L, C] using phaseLimitingDensity_le_const y
  have hSecond : |c - 1| * |L| < eps / 4 := by
    calc
      |c - 1| * |L| ≤ |c - 1| * C :=
        mul_le_mul_of_nonneg_left hL (abs_nonneg _)
      _ < (eps / (4 * (C + 1))) * C := by
        gcongr
      _ < eps / 4 := by
        calc
          (eps / (4 * (C + 1))) * C =
              (eps / 4) * (C / (C + 1)) := by
            field_simp
          _ < (eps / 4) * 1 := by
            apply mul_lt_mul_of_pos_left
            · exact (div_lt_one hCOne).2 (by linarith)
            · positivity
          _ = eps / 4 := mul_one _
  rw [phaseSmoothedDensity_eq_average n hn points
      (localCLTSmoothingScaleTest n)
      (by unfold localCLTSmoothingScaleTest; exact rigidityPower_pos hn _) y]
  change |c * (E₀ + E₁) / 2 - L| < eps
  rw [show c * (E₀ + E₁) / 2 = c * A by
    dsimp [A]
    ring]
  calc
    |c * A - L| = |c * (A - L) + (c - 1) * L| := by
      congr 1
      ring
    _ ≤ |c * (A - L)| + |(c - 1) * L| := abs_add_le _ _
    _ = c * |A - L| + |c - 1| * |L| := by
      rw [abs_mul, abs_mul, abs_of_pos hcPos]
    _ < eps / 4 + eps / 4 := add_lt_add hFirst hSecond
    _ < eps := by linarith

end Odd

end Erdos525
