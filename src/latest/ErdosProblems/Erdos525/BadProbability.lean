import ErdosProblems.Erdos525.BadCover

open scoped BigOperators Topology ComplexConjugate RealInnerProductSpace

namespace Erdos525

open Classical Filter Finset Set MeasureTheory

lemma norm_normalizedPositionEuclideanWalk_singleton
    (n : ℕ) (e : SignVector (2 * n)) (t : ℝ) :
    ‖normalizedPositionEuclideanWalk n e (fun _ : Fin 1 ↦ t)‖ =
      ‖rescaledCenteredEval n e t‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [norm_normalizedPositionEuclideanWalk_sq]
  simp

noncomputable def positionSmallBallUpper
    (n : ℕ) (gamma delta : ℝ) : ℝ :=
  Real.exp (1 / 2) * (Real.pi ^ 2 / 2) * (delta ^ 2 / gamma) +
    2 * Real.exp (1 / 2) *
      Real.exp (-(delta ^ 2 / 4) * phaseNoWrapRadius n 1 ^ 2)

lemma uniformProbability_eval_ball_le
    (n : ℕ) (t gamma delta : ℝ)
    (hgamma : 0 < gamma) (hdelta : 0 < delta)
    (hcov : HasPositionCovarianceLower n (fun _ : Fin 1 ↦ t) gamma) :
    uniformProbability (fun e : SignVector (2 * n) ↦
        ‖rescaledCenteredEval n e t‖ ≤ delta) ≤
      positionSmallBallUpper n gamma delta := by
  have hraw := uniformProbability_positionBall_le_of_positionCovariance
    n 1 (fun _ : Fin 1 ↦ t) gamma delta delta hgamma hdelta hdelta.le
      hcov (0 : PositionEuclidean 1)
  have hevent : (fun e : SignVector (2 * n) ↦
      ‖normalizedPositionEuclideanWalk n e (fun _ : Fin 1 ↦ t) -
        (0 : PositionEuclidean 1)‖ ≤ delta) =
      (fun e : SignVector (2 * n) ↦
        ‖rescaledCenteredEval n e t‖ ≤ delta) := by
    funext e
    apply propext
    simp only [sub_zero, norm_normalizedPositionEuclideanWalk_singleton]
  rw [hevent] at hraw
  calc
    uniformProbability (fun e : SignVector (2 * n) ↦
        ‖rescaledCenteredEval n e t‖ ≤ delta) ≤
        ((Real.pi / (gamma / Real.pi ^ 2)) ^ (1 : ℕ) +
            Real.exp (-(delta ^ 2 / 4) * phaseNoWrapRadius n 1 ^ 2) *
              (Real.pi / (delta ^ 2 / 4)) ^ (1 : ℕ)) /
          ((2 * Real.pi / delta ^ 2) ^ (1 : ℕ) *
            Real.exp (-(delta ^ 2 / (2 * delta ^ 2)))) := hraw
    _ = positionSmallBallUpper n gamma delta := by
      unfold positionSmallBallUpper
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      have hd : delta ≠ 0 := hdelta.ne'
      have hg : gamma ≠ 0 := hgamma.ne'
      rw [pow_one, pow_one, pow_one]
      have hexp : Real.exp (-(delta ^ 2 / (2 * delta ^ 2))) =
          Real.exp (-(1 / 2 : ℝ)) := by
        congr 1
        field_simp [hd]
      rw [hexp]
      rw [Real.exp_neg]
      field_simp [hpi, hd, hg]
      ring

lemma HasPositionCovarianceLower.mono
    {n m : ℕ} {points : Fin m → ℝ} {gamma₁ gamma₂ : ℝ}
    (h₁ : 0 ≤ gamma₁) (hgamma : gamma₁ ≤ gamma₂)
    (hcov : HasPositionCovarianceLower n points gamma₂) :
    HasPositionCovarianceLower n points gamma₁ := by
  intro v
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hgamma (by positivity))
    (sq_nonneg ‖positionToEuclidean v‖)).trans (hcov v)

noncomputable def endpointCoverGamma (n ℓ : ℕ) : ℝ :=
  endpointShellLower n ℓ ^ 2 / 1000000000

noncomputable def endpointCoverDelta (n ℓ : ℕ) (u : ℝ) : ℝ :=
  u / n + 2 * growingVelocityCutoff n * endpointShellStep n ℓ

lemma endpointCoverGamma_pos
    {n : ℕ} (hn : 0 < n) (ℓ : ℕ) :
    0 < endpointCoverGamma n ℓ := by
  unfold endpointCoverGamma
  exact div_pos (sq_pos_of_pos (endpointShellLower_pos hn ℓ)) (by norm_num)

lemma endpointCoverDelta_pos
    {n : ℕ} (hn : 0 < n) {u : ℝ} (hu : 0 < u) (ℓ : ℕ) :
    0 < endpointCoverDelta n ℓ u := by
  unfold endpointCoverDelta
  exact add_pos_of_pos_of_nonneg (div_pos hu (by exact_mod_cast hn))
    (mul_nonneg (mul_nonneg (by norm_num) (growingVelocityCutoff_nonneg n))
      (endpointShellStep_pos hn ℓ).le)

lemma endpointCoverGamma_le_near
    {n ℓ : ℕ} {q : ℝ}
    (hq : endpointShellLower n ℓ ≤ q) :
    endpointCoverGamma n ℓ ≤ q ^ 2 / 1000000000 := by
  unfold endpointCoverGamma
  apply div_le_div_of_nonneg_right _ (by norm_num)
  have hl0 : 0 ≤ endpointShellLower n ℓ := by
    unfold endpointShellLower
    exact rigidityPower_nonneg n _
  have hq0 : 0 ≤ q := hl0.trans hq
  exact (sq_le_sq₀ hl0 hq0).2 hq

lemma endpoint_hasPositionCovarianceLower
    {n ℓ : ℕ} (hn : 1000 ≤ n) {q : ℝ}
    (hqLower : endpointShellLower n ℓ ≤ q)
    (hq : q ∈ Set.Icc (0 : ℝ) 11)
    (hqHalf : q ≤ Real.pi * n / 2) :
    HasPositionCovarianceLower n (fun _ : Fin 1 ↦ q)
      (endpointCoverGamma n ℓ) := by
  by_cases hqTen : q ≤ 10
  · exact (endpoint_hasPositionCovarianceLower_near_zero n hn q hq.1 hqTen).mono
      (by unfold endpointCoverGamma; positivity)
      (endpointCoverGamma_le_near hqLower)
  · have hfar := endpoint_hasPositionCovarianceLower_far_zero
      n hn q (le_of_not_ge hqTen) hqHalf
    apply hfar.mono (by unfold endpointCoverGamma; positivity)
    unfold endpointCoverGamma
    have hl0 : 0 ≤ endpointShellLower n ℓ := by
      unfold endpointShellLower
      exact rigidityPower_nonneg n _
    have hlq : endpointShellLower n ℓ ≤ 11 := hqLower.trans hq.2
    have hsq : endpointShellLower n ℓ ^ 2 ≤ 121 := by
      have hsq' := (sq_le_sq₀ hl0 (by norm_num : (0 : ℝ) ≤ 11)).2 hlq
      norm_num at hsq'
      exact hsq'
    nlinarith

lemma endpoint_hasPositionCovarianceLower_pi
    {n ℓ : ℕ} (hn : 1000 ≤ n) {d : ℝ}
    (hdLower : endpointShellLower n ℓ ≤ d)
    (hd : d ∈ Set.Icc (0 : ℝ) 11)
    (hdHalf : d ≤ Real.pi * n / 2) :
    HasPositionCovarianceLower n
      (fun _ : Fin 1 ↦ Real.pi * n - d) (endpointCoverGamma n ℓ) := by
  by_cases hdTen : d ≤ 10
  · exact (endpoint_hasPositionCovarianceLower_near_pi n hn d hd.1 hdTen).mono
      (by unfold endpointCoverGamma; positivity)
      (endpointCoverGamma_le_near hdLower)
  · have hfar := endpoint_hasPositionCovarianceLower_far_pi
      n hn d (le_of_not_ge hdTen) hdHalf
    apply hfar.mono (by unfold endpointCoverGamma; positivity)
    unfold endpointCoverGamma
    have hl0 : 0 ≤ endpointShellLower n ℓ := by
      unfold endpointShellLower
      exact rigidityPower_nonneg n _
    have hlq : endpointShellLower n ℓ ≤ 11 := hdLower.trans hd.2
    have hsq : endpointShellLower n ℓ ^ 2 ≤ 121 := by
      have hsq' := (sq_le_sq₀ hl0 (by norm_num : (0 : ℝ) ≤ 11)).2 hlq
      norm_num at hsq'
      exact hsq'
    nlinarith

lemma growingVelocityCutoff_mul_endpointShellStep
    {n : ℕ} (hn : 0 < n) (ℓ : ℕ) :
    growingVelocityCutoff n * endpointShellStep n ℓ =
      rigidityPower n (((ℓ : ℝ) - 55) / 128) := by
  unfold growingVelocityCutoff endpointShellStep endpointShellLower
  rw [← rigidityPower_add hn, ← rigidityPower_add hn]
  congr 2
  push_cast
  ring

lemma endpointCoverGamma_eq_power
    {n : ℕ} (hn : 0 < n) (ℓ : ℕ) :
    endpointCoverGamma n ℓ =
      rigidityPower n ((2 * (ℓ : ℝ) - 96) / 128) / 1000000000 := by
  unfold endpointCoverGamma endpointShellLower
  rw [rigidityPower_nat_pow hn]
  congr 2
  push_cast
  ring

lemma endpointCoverDelta_upper
    {n : ℕ} (hn : 0 < n) {u : ℝ} (hu : 0 ≤ u)
    {ℓ : ℕ} (hℓ : ℓ < 49) :
    endpointCoverDelta n ℓ u ≤
      (u + 2) * rigidityPower n (((ℓ : ℝ) - 55) / 128) := by
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hexp : (-1 : ℝ) ≤ ((ℓ : ℝ) - 55) / 128 := by
    have hℓ0 : (0 : ℝ) ≤ ℓ := by positivity
    linarith
  have hpower : rigidityPower n (-1) ≤
      rigidityPower n (((ℓ : ℝ) - 55) / 128) := by
    unfold rigidityPower
    exact Real.rpow_le_rpow_of_exponent_le hnOne hexp
  have hinv : (n : ℝ)⁻¹ = rigidityPower n (-1) := by
    unfold rigidityPower
    rw [Real.rpow_neg (by exact_mod_cast hn.le), Real.rpow_one]
  unfold endpointCoverDelta
  rw [div_eq_mul_inv, hinv]
  rw [show 2 * growingVelocityCutoff n * endpointShellStep n ℓ =
      2 * (growingVelocityCutoff n * endpointShellStep n ℓ) by ring,
    growingVelocityCutoff_mul_endpointShellStep hn]
  calc
    u * rigidityPower n (-1) +
        2 * rigidityPower n (((ℓ : ℝ) - 55) / 128) ≤
      u * rigidityPower n (((ℓ : ℝ) - 55) / 128) +
        2 * rigidityPower n (((ℓ : ℝ) - 55) / 128) := by
      gcongr
    _ = (u + 2) * rigidityPower n (((ℓ : ℝ) - 55) / 128) := by ring

lemma endpoint_delta_sq_div_gamma_upper
    {n : ℕ} (hn : 0 < n) {u : ℝ} (hu : 0 ≤ u)
    {ℓ : ℕ} (hℓ : ℓ < 49) :
    endpointCoverDelta n ℓ u ^ 2 / endpointCoverGamma n ℓ ≤
      (1000000000 * (u + 2) ^ 2) * rigidityPower n (-14 / 128) := by
  have hdelta := endpointCoverDelta_upper hn hu hℓ
  have hdelta0 : 0 ≤ endpointCoverDelta n ℓ u := by
    unfold endpointCoverDelta
    exact add_nonneg (div_nonneg hu (Nat.cast_nonneg n))
      (mul_nonneg (mul_nonneg (by norm_num) (growingVelocityCutoff_nonneg n))
        (endpointShellStep_pos hn ℓ).le)
  have hpow0 : 0 ≤ rigidityPower n (((ℓ : ℝ) - 55) / 128) :=
    rigidityPower_nonneg n _
  have hsquare := (sq_le_sq₀ hdelta0
    (mul_nonneg (by linarith) hpow0)).2 hdelta
  rw [endpointCoverGamma_eq_power hn]
  have hgammaPower : 0 < rigidityPower n ((2 * (ℓ : ℝ) - 96) / 128) :=
    rigidityPower_pos hn _
  rw [show endpointCoverDelta n ℓ u ^ 2 /
      (rigidityPower n ((2 * (ℓ : ℝ) - 96) / 128) / 1000000000) =
      endpointCoverDelta n ℓ u ^ 2 * 1000000000 /
        rigidityPower n ((2 * (ℓ : ℝ) - 96) / 128) by
    field_simp [hgammaPower.ne']]
  have hratio : rigidityPower n (((ℓ : ℝ) - 55) / 128) ^ 2 /
      rigidityPower n ((2 * (ℓ : ℝ) - 96) / 128) =
        rigidityPower n (-14 / 128) := by
    rw [rigidityPower_nat_pow hn]
    unfold rigidityPower
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    rw [← Real.rpow_sub hnR]
    congr 2
    push_cast
    ring
  calc
    endpointCoverDelta n ℓ u ^ 2 * 1000000000 /
        rigidityPower n ((2 * (ℓ : ℝ) - 96) / 128) ≤
      ((u + 2) * rigidityPower n (((ℓ : ℝ) - 55) / 128)) ^ 2 *
          1000000000 /
        rigidityPower n ((2 * (ℓ : ℝ) - 96) / 128) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsquare (by norm_num)) hgammaPower.le
    _ = (1000000000 * (u + 2) ^ 2) * rigidityPower n (-14 / 128) := by
      rw [mul_pow]
      calc
        (u + 2) ^ 2 * rigidityPower n (((ℓ : ℝ) - 55) / 128) ^ 2 *
              1000000000 /
            rigidityPower n ((2 * (ℓ : ℝ) - 96) / 128) =
            (1000000000 * (u + 2) ^ 2) *
              (rigidityPower n (((ℓ : ℝ) - 55) / 128) ^ 2 /
                rigidityPower n ((2 * (ℓ : ℝ) - 96) / 128)) := by ring
        _ = _ := by rw [hratio]

lemma phaseNoWrapRadius_one_sq_lower (n : ℕ) :
    (n : ℝ) / 1024 ≤ phaseNoWrapRadius n 1 ^ 2 := by
  unfold phaseNoWrapRadius
  norm_num
  have hsqrt : Real.sqrt (2 * n + 1 : ℝ) ^ 2 = 2 * n + 1 :=
    Real.sq_sqrt (by positivity)
  rw [div_pow, mul_pow, hsqrt]
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hpiSq : (1 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
  apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 1024)
    (by norm_num : (0 : ℝ) < 32 ^ 2)).2
  norm_num
  nlinarith [mul_le_mul_of_nonneg_right hpiSq
    (by positivity : (0 : ℝ) ≤ 2 * n + 1)]

lemma endpoint_smoothing_exponent_lower
    {n : ℕ} (hn : 0 < n) {u : ℝ} (hu : 0 ≤ u)
    {ℓ : ℕ} (hℓ : ℓ < 49) :
    (1 / 1024 : ℝ) * rigidityPower n (18 / 128) ≤
      endpointCoverDelta n ℓ u ^ 2 / 4 * phaseNoWrapRadius n 1 ^ 2 := by
  let a : ℝ := ((ℓ : ℝ) - 55) / 128
  have hcore : 2 * rigidityPower n a ≤ endpointCoverDelta n ℓ u := by
    unfold endpointCoverDelta
    rw [show 2 * growingVelocityCutoff n * endpointShellStep n ℓ =
      2 * (growingVelocityCutoff n * endpointShellStep n ℓ) by ring,
      growingVelocityCutoff_mul_endpointShellStep hn]
    dsimp [a]
    exact le_add_of_nonneg_left (div_nonneg hu (Nat.cast_nonneg n))
  have hcore0 : 0 ≤ 2 * rigidityPower n a := by
    exact mul_nonneg (by norm_num) (rigidityPower_nonneg n _)
  have hdelta0 : 0 ≤ endpointCoverDelta n ℓ u := hcore0.trans hcore
  have hsquare := (sq_le_sq₀ hcore0 hdelta0).2 hcore
  have hdeltaSq : rigidityPower n a ^ 2 ≤
      endpointCoverDelta n ℓ u ^ 2 / 4 := by nlinarith
  have hR := phaseNoWrapRadius_one_sq_lower n
  have hmul : rigidityPower n a ^ 2 * ((n : ℝ) / 1024) ≤
      (endpointCoverDelta n ℓ u ^ 2 / 4) *
        phaseNoWrapRadius n 1 ^ 2 := by
    exact mul_le_mul hdeltaSq hR (by positivity) (by positivity)
  have hpower : rigidityPower n a ^ 2 * (n : ℝ) =
      rigidityPower n ((2 * (ℓ : ℝ) + 18) / 128) := by
    rw [rigidityPower_nat_pow hn]
    rw [show (n : ℝ) = rigidityPower n 1 by simp [rigidityPower],
      ← rigidityPower_add hn]
    dsimp [a]
    congr 2
    push_cast
    ring
  have hexp : (18 / 128 : ℝ) ≤ (2 * (ℓ : ℝ) + 18) / 128 := by
    have hℓ0 : (0 : ℝ) ≤ ℓ := by positivity
    linarith
  have hpowerMono : rigidityPower n (18 / 128) ≤
      rigidityPower n ((2 * (ℓ : ℝ) + 18) / 128) := by
    unfold rigidityPower
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ n by omega)) hexp
  calc
    (1 / 1024 : ℝ) * rigidityPower n (18 / 128) ≤
        (1 / 1024) * rigidityPower n ((2 * (ℓ : ℝ) + 18) / 128) := by
      gcongr
    _ = rigidityPower n a ^ 2 * ((n : ℝ) / 1024) := by
      rw [← hpower]
      ring
    _ ≤ _ := hmul

noncomputable def endpointPointProbabilityUpper (n : ℕ) (u : ℝ) : ℝ :=
  (Real.exp (1 / 2) * (Real.pi ^ 2 / 2) *
      (1000000000 * (u + 2) ^ 2)) * rigidityPower n (-14 / 128) +
    2 * Real.exp (1 / 2) *
      Real.exp (-(1 / 1024 : ℝ) * rigidityPower n (18 / 128))

lemma endpoint_point_probability_le
    {n : ℕ} (hn : 1000 ≤ n) {u : ℝ} (hu : 0 < u)
    {ℓ : ℕ} (hℓ : ℓ < 49) (q : ℝ)
    (hqLower : endpointShellLower n ℓ ≤ q) :
    uniformProbability (fun e : SignVector (2 * n) ↦
      q ∈ Set.Icc (0 : ℝ) 11 ∧
        ‖rescaledCenteredEval n e q‖ ≤ endpointCoverDelta n ℓ u) ≤
      endpointPointProbabilityUpper n u := by
  by_cases hq : q ∈ Set.Icc (0 : ℝ) 11
  · have hhalf : q ≤ Real.pi * n / 2 := by
      have hnR : (1000 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [hq.2, Real.pi_gt_three]
    have hcov := endpoint_hasPositionCovarianceLower hn hqLower hq hhalf
    have hprob := uniformProbability_eval_ball_le n q
      (endpointCoverGamma n ℓ) (endpointCoverDelta n ℓ u)
      (endpointCoverGamma_pos (by omega) ℓ)
      (endpointCoverDelta_pos (by omega) hu ℓ) hcov
    have hratio := endpoint_delta_sq_div_gamma_upper
      (by omega : 0 < n) hu.le hℓ
    have hsmooth := endpoint_smoothing_exponent_lower
      (by omega : 0 < n) hu.le hℓ
    have htail : Real.exp
          (-(endpointCoverDelta n ℓ u ^ 2 / 4) *
            phaseNoWrapRadius n 1 ^ 2) ≤
        Real.exp (-(1 / 1024 : ℝ) * rigidityPower n (18 / 128)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hevent : (fun e : SignVector (2 * n) ↦
        q ∈ Set.Icc (0 : ℝ) 11 ∧
          ‖rescaledCenteredEval n e q‖ ≤ endpointCoverDelta n ℓ u) =
        (fun e : SignVector (2 * n) ↦
          ‖rescaledCenteredEval n e q‖ ≤ endpointCoverDelta n ℓ u) := by
      funext e
      simp [hq]
    rw [hevent]
    exact hprob.trans (by
      unfold positionSmallBallUpper endpointPointProbabilityUpper
      have hC : 0 ≤ Real.exp (1 / 2) * (Real.pi ^ 2 / 2) := by positivity
      have hfirst := mul_le_mul_of_nonneg_left hratio hC
      have hfirst' :
          Real.exp (1 / 2) * (Real.pi ^ 2 / 2) *
              (endpointCoverDelta n ℓ u ^ 2 / endpointCoverGamma n ℓ) ≤
            (Real.exp (1 / 2) * (Real.pi ^ 2 / 2) *
              (1000000000 * (u + 2) ^ 2)) * rigidityPower n (-14 / 128) := by
        calc
          _ ≤ (Real.exp (1 / 2) * (Real.pi ^ 2 / 2)) *
              ((1000000000 * (u + 2) ^ 2) *
                rigidityPower n (-14 / 128)) := hfirst
          _ = _ := by ring
      exact add_le_add hfirst'
        (mul_le_mul_of_nonneg_left htail (by positivity)))
  · have hzero : uniformProbability (fun e : SignVector (2 * n) ↦
        q ∈ Set.Icc (0 : ℝ) 11 ∧
          ‖rescaledCenteredEval n e q‖ ≤ endpointCoverDelta n ℓ u) = 0 := by
      unfold uniformProbability
      simp [hq]
    rw [hzero]
    unfold endpointPointProbabilityUpper
    exact add_nonneg
      (mul_nonneg (by positivity) (rigidityPower_nonneg n _)) (by positivity)

lemma endpoint_point_probability_le_of_shellPoint
    {n : ℕ} (hn : 1000 ≤ n) {u : ℝ} (hu : 0 < u)
    {ℓ b : ℕ} (hℓ : ℓ < 49) :
    uniformProbability (fun e : SignVector (2 * n) ↦
      endpointShellPoint n ℓ b ∈ Set.Icc (0 : ℝ) 11 ∧
        ‖rescaledCenteredEval n e (endpointShellPoint n ℓ b)‖ ≤
          endpointCoverDelta n ℓ u) ≤ endpointPointProbabilityUpper n u := by
  by_cases hq : endpointShellPoint n ℓ b ∈ Set.Icc (0 : ℝ) 11
  · have hqLower : endpointShellLower n ℓ ≤ endpointShellPoint n ℓ b := by
      unfold endpointShellPoint
      exact le_add_of_nonneg_right
        (mul_nonneg (Nat.cast_nonneg b) (endpointShellStep_pos (by omega) ℓ).le)
    have hhalf : endpointShellPoint n ℓ b ≤ Real.pi * n / 2 := by
      have hnR : (1000 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [hq.2, Real.pi_gt_three]
    have hcov := endpoint_hasPositionCovarianceLower hn hqLower hq hhalf
    have hprob := uniformProbability_eval_ball_le n (endpointShellPoint n ℓ b)
      (endpointCoverGamma n ℓ) (endpointCoverDelta n ℓ u)
      (endpointCoverGamma_pos (by omega) ℓ)
      (endpointCoverDelta_pos (by omega) hu ℓ) hcov
    have hratio := endpoint_delta_sq_div_gamma_upper
      (by omega : 0 < n) hu.le hℓ
    have hsmooth := endpoint_smoothing_exponent_lower
      (by omega : 0 < n) hu.le hℓ
    have htail : Real.exp
          (-(endpointCoverDelta n ℓ u ^ 2 / 4) *
            phaseNoWrapRadius n 1 ^ 2) ≤
        Real.exp (-(1 / 1024 : ℝ) * rigidityPower n (18 / 128)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hevent : (fun e : SignVector (2 * n) ↦
        endpointShellPoint n ℓ b ∈ Set.Icc (0 : ℝ) 11 ∧
          ‖rescaledCenteredEval n e (endpointShellPoint n ℓ b)‖ ≤
            endpointCoverDelta n ℓ u) =
        (fun e : SignVector (2 * n) ↦
          ‖rescaledCenteredEval n e (endpointShellPoint n ℓ b)‖ ≤
            endpointCoverDelta n ℓ u) := by
      funext e
      simp [hq]
    rw [hevent]
    exact hprob.trans (by
      unfold positionSmallBallUpper endpointPointProbabilityUpper
      have hC : 0 ≤ Real.exp (1 / 2) * (Real.pi ^ 2 / 2) := by positivity
      have hfirst := mul_le_mul_of_nonneg_left hratio hC
      have hfirst' :
          Real.exp (1 / 2) * (Real.pi ^ 2 / 2) *
              (endpointCoverDelta n ℓ u ^ 2 / endpointCoverGamma n ℓ) ≤
            (Real.exp (1 / 2) * (Real.pi ^ 2 / 2) *
              (1000000000 * (u + 2) ^ 2)) * rigidityPower n (-14 / 128) := by
        calc
          _ ≤ (Real.exp (1 / 2) * (Real.pi ^ 2 / 2)) *
              ((1000000000 * (u + 2) ^ 2) *
                rigidityPower n (-14 / 128)) := hfirst
          _ = _ := by ring
      exact add_le_add hfirst'
        (mul_le_mul_of_nonneg_left htail (by positivity)))
  · have hzero : uniformProbability (fun e : SignVector (2 * n) ↦
        endpointShellPoint n ℓ b ∈ Set.Icc (0 : ℝ) 11 ∧
          ‖rescaledCenteredEval n e (endpointShellPoint n ℓ b)‖ ≤
            endpointCoverDelta n ℓ u) = 0 := by
      unfold uniformProbability
      simp [hq]
    rw [hzero]
    unfold endpointPointProbabilityUpper
    exact add_nonneg
      (mul_nonneg (by positivity) (rigidityPower_nonneg n _)) (by positivity)

lemma endpoint_point_probability_le_of_shellPoint_pi
    {n : ℕ} (hn : 1000 ≤ n) {u : ℝ} (hu : 0 < u)
    {ℓ b : ℕ} (hℓ : ℓ < 49) :
    uniformProbability (fun e : SignVector (2 * n) ↦
      endpointShellPoint n ℓ b ∈ Set.Icc (0 : ℝ) 11 ∧
        ‖rescaledCenteredEval n e
            (Real.pi * n - endpointShellPoint n ℓ b)‖ ≤
          endpointCoverDelta n ℓ u) ≤ endpointPointProbabilityUpper n u := by
  by_cases hd : endpointShellPoint n ℓ b ∈ Set.Icc (0 : ℝ) 11
  · have hdLower : endpointShellLower n ℓ ≤ endpointShellPoint n ℓ b := by
      unfold endpointShellPoint
      exact le_add_of_nonneg_right
        (mul_nonneg (Nat.cast_nonneg b) (endpointShellStep_pos (by omega) ℓ).le)
    have hhalf : endpointShellPoint n ℓ b ≤ Real.pi * n / 2 := by
      have hnR : (1000 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [hd.2, Real.pi_gt_three]
    have hcov := endpoint_hasPositionCovarianceLower_pi hn hdLower hd hhalf
    have hprob := uniformProbability_eval_ball_le n
      (Real.pi * n - endpointShellPoint n ℓ b)
      (endpointCoverGamma n ℓ) (endpointCoverDelta n ℓ u)
      (endpointCoverGamma_pos (by omega) ℓ)
      (endpointCoverDelta_pos (by omega) hu ℓ) hcov
    have hratio := endpoint_delta_sq_div_gamma_upper
      (by omega : 0 < n) hu.le hℓ
    have hsmooth := endpoint_smoothing_exponent_lower
      (by omega : 0 < n) hu.le hℓ
    have htail : Real.exp
          (-(endpointCoverDelta n ℓ u ^ 2 / 4) *
            phaseNoWrapRadius n 1 ^ 2) ≤
        Real.exp (-(1 / 1024 : ℝ) * rigidityPower n (18 / 128)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hevent : (fun e : SignVector (2 * n) ↦
        endpointShellPoint n ℓ b ∈ Set.Icc (0 : ℝ) 11 ∧
          ‖rescaledCenteredEval n e
              (Real.pi * n - endpointShellPoint n ℓ b)‖ ≤
            endpointCoverDelta n ℓ u) =
        (fun e : SignVector (2 * n) ↦
          ‖rescaledCenteredEval n e
              (Real.pi * n - endpointShellPoint n ℓ b)‖ ≤
            endpointCoverDelta n ℓ u) := by
      funext e
      simp [hd]
    rw [hevent]
    exact hprob.trans (by
      unfold positionSmallBallUpper endpointPointProbabilityUpper
      have hC : 0 ≤ Real.exp (1 / 2) * (Real.pi ^ 2 / 2) := by positivity
      have hfirst := mul_le_mul_of_nonneg_left hratio hC
      have hfirst' :
          Real.exp (1 / 2) * (Real.pi ^ 2 / 2) *
              (endpointCoverDelta n ℓ u ^ 2 / endpointCoverGamma n ℓ) ≤
            (Real.exp (1 / 2) * (Real.pi ^ 2 / 2) *
              (1000000000 * (u + 2) ^ 2)) * rigidityPower n (-14 / 128) := by
        calc
          _ ≤ (Real.exp (1 / 2) * (Real.pi ^ 2 / 2)) *
              ((1000000000 * (u + 2) ^ 2) *
                rigidityPower n (-14 / 128)) := hfirst
          _ = _ := by ring
      exact add_le_add hfirst'
        (mul_le_mul_of_nonneg_left htail (by positivity)))
  · have hzero : uniformProbability (fun e : SignVector (2 * n) ↦
        endpointShellPoint n ℓ b ∈ Set.Icc (0 : ℝ) 11 ∧
          ‖rescaledCenteredEval n e
              (Real.pi * n - endpointShellPoint n ℓ b)‖ ≤
            endpointCoverDelta n ℓ u) = 0 := by
      unfold uniformProbability
      simp [hd]
    rw [hzero]
    unfold endpointPointProbabilityUpper
    exact add_nonneg
      (mul_nonneg (by positivity) (rigidityPower_nonneg n _)) (by positivity)

def HasLeftEndpointCoverWitness (n : ℕ) (u : ℝ)
    (e : SignVector (2 * n)) : Prop :=
  ∃ ℓ : Fin 49, ∃ b : Fin (endpointShellCount n ℓ),
    endpointShellPoint n ℓ b ∈ Set.Icc (0 : ℝ) 11 ∧
      ‖rescaledCenteredEval n e (endpointShellPoint n ℓ b)‖ ≤
        endpointCoverDelta n ℓ u

def HasRightEndpointCoverWitness (n : ℕ) (u : ℝ)
    (e : SignVector (2 * n)) : Prop :=
  ∃ ℓ : Fin 49, ∃ b : Fin (endpointShellCount n ℓ),
    endpointShellPoint n ℓ b ∈ Set.Icc (0 : ℝ) 11 ∧
      ‖rescaledCenteredEval n e
          (Real.pi * n - endpointShellPoint n ℓ b)‖ ≤
        endpointCoverDelta n ℓ u

noncomputable def endpointWitnessProbabilityUpper (n : ℕ) (u : ℝ) : ℝ :=
  98 * rigidityPower n (9 / 128) * endpointPointProbabilityUpper n u

lemma uniformProbability_leftEndpointCoverWitness_le
    {n : ℕ} (hn : 1000 ≤ n) {u : ℝ} (hu : 0 < u) :
    uniformProbability (HasLeftEndpointCoverWitness n u) ≤
      endpointWitnessProbabilityUpper n u := by
  let P : Fin 49 → SignVector (2 * n) → Prop := fun ℓ e ↦
    ∃ b : Fin (endpointShellCount n ℓ),
      endpointShellPoint n ℓ b ∈ Set.Icc (0 : ℝ) 11 ∧
        ‖rescaledCenteredEval n e (endpointShellPoint n ℓ b)‖ ≤
          endpointCoverDelta n ℓ u
  have houter := uniformProbability_exists_le_sum P
  have hinner : ∀ ℓ : Fin 49,
      uniformProbability (P ℓ) ≤
        (endpointShellCount n ℓ : ℝ) * endpointPointProbabilityUpper n u := by
    intro ℓ
    have hsum := uniformProbability_exists_le_sum
      (fun b : Fin (endpointShellCount n ℓ) ↦ fun e : SignVector (2 * n) ↦
        endpointShellPoint n ℓ b ∈ Set.Icc (0 : ℝ) 11 ∧
          ‖rescaledCenteredEval n e (endpointShellPoint n ℓ b)‖ ≤
            endpointCoverDelta n ℓ u)
    calc
      uniformProbability (P ℓ) ≤
          ∑ b : Fin (endpointShellCount n ℓ),
            uniformProbability (fun e : SignVector (2 * n) ↦
              endpointShellPoint n ℓ b ∈ Set.Icc (0 : ℝ) 11 ∧
                ‖rescaledCenteredEval n e (endpointShellPoint n ℓ b)‖ ≤
                  endpointCoverDelta n ℓ u) := by simpa [P] using hsum
      _ ≤ ∑ _b : Fin (endpointShellCount n ℓ),
          endpointPointProbabilityUpper n u := by
        apply Finset.sum_le_sum
        intro b _hb
        exact endpoint_point_probability_le_of_shellPoint hn hu ℓ.isLt
      _ = (endpointShellCount n ℓ : ℝ) *
          endpointPointProbabilityUpper n u := by simp
  have hsum : uniformProbability (HasLeftEndpointCoverWitness n u) ≤
      ∑ ℓ : Fin 49,
        (endpointShellCount n ℓ : ℝ) * endpointPointProbabilityUpper n u := by
    calc
      uniformProbability (HasLeftEndpointCoverWitness n u) =
          uniformProbability (fun e ↦ ∃ ℓ : Fin 49, P ℓ e) := by rfl
      _ ≤ ∑ ℓ : Fin 49, uniformProbability (P ℓ) := houter
      _ ≤ ∑ ℓ : Fin 49,
          (endpointShellCount n ℓ : ℝ) * endpointPointProbabilityUpper n u := by
        apply Finset.sum_le_sum
        intro ℓ _hℓ
        exact hinner ℓ
  have hcount := endpointShellCounts_sum_cast_le (by omega : 0 < n)
  have hupper0 : 0 ≤ endpointPointProbabilityUpper n u := by
    unfold endpointPointProbabilityUpper
    exact add_nonneg
      (mul_nonneg (by positivity) (rigidityPower_nonneg n _)) (by positivity)
  unfold endpointWitnessProbabilityUpper
  calc
    uniformProbability (HasLeftEndpointCoverWitness n u) ≤
        ∑ ℓ : Fin 49,
          (endpointShellCount n ℓ : ℝ) * endpointPointProbabilityUpper n u := hsum
    _ = (∑ ℓ : Fin 49, (endpointShellCount n ℓ : ℝ)) *
          endpointPointProbabilityUpper n u := by
      rw [Finset.sum_mul]
    _ = (∑ ℓ ∈ Finset.range 49, (endpointShellCount n ℓ : ℝ)) *
          endpointPointProbabilityUpper n u := by
      congr 1
    _ ≤ (98 * rigidityPower n (9 / 128)) *
          endpointPointProbabilityUpper n u :=
      mul_le_mul_of_nonneg_right hcount hupper0

lemma uniformProbability_rightEndpointCoverWitness_le
    {n : ℕ} (hn : 1000 ≤ n) {u : ℝ} (hu : 0 < u) :
    uniformProbability (HasRightEndpointCoverWitness n u) ≤
      endpointWitnessProbabilityUpper n u := by
  let P : Fin 49 → SignVector (2 * n) → Prop := fun ℓ e ↦
    ∃ b : Fin (endpointShellCount n ℓ),
      endpointShellPoint n ℓ b ∈ Set.Icc (0 : ℝ) 11 ∧
        ‖rescaledCenteredEval n e
            (Real.pi * n - endpointShellPoint n ℓ b)‖ ≤
          endpointCoverDelta n ℓ u
  have houter := uniformProbability_exists_le_sum P
  have hinner : ∀ ℓ : Fin 49,
      uniformProbability (P ℓ) ≤
        (endpointShellCount n ℓ : ℝ) * endpointPointProbabilityUpper n u := by
    intro ℓ
    have hsum := uniformProbability_exists_le_sum
      (fun b : Fin (endpointShellCount n ℓ) ↦ fun e : SignVector (2 * n) ↦
        endpointShellPoint n ℓ b ∈ Set.Icc (0 : ℝ) 11 ∧
          ‖rescaledCenteredEval n e
              (Real.pi * n - endpointShellPoint n ℓ b)‖ ≤
            endpointCoverDelta n ℓ u)
    calc
      uniformProbability (P ℓ) ≤
          ∑ b : Fin (endpointShellCount n ℓ),
            uniformProbability (fun e : SignVector (2 * n) ↦
              endpointShellPoint n ℓ b ∈ Set.Icc (0 : ℝ) 11 ∧
                ‖rescaledCenteredEval n e
                    (Real.pi * n - endpointShellPoint n ℓ b)‖ ≤
                  endpointCoverDelta n ℓ u) := by simpa [P] using hsum
      _ ≤ ∑ _b : Fin (endpointShellCount n ℓ),
          endpointPointProbabilityUpper n u := by
        apply Finset.sum_le_sum
        intro b _hb
        exact endpoint_point_probability_le_of_shellPoint_pi hn hu ℓ.isLt
      _ = (endpointShellCount n ℓ : ℝ) *
          endpointPointProbabilityUpper n u := by simp
  have hsum : uniformProbability (HasRightEndpointCoverWitness n u) ≤
      ∑ ℓ : Fin 49,
        (endpointShellCount n ℓ : ℝ) * endpointPointProbabilityUpper n u := by
    calc
      uniformProbability (HasRightEndpointCoverWitness n u) =
          uniformProbability (fun e ↦ ∃ ℓ : Fin 49, P ℓ e) := by rfl
      _ ≤ ∑ ℓ : Fin 49, uniformProbability (P ℓ) := houter
      _ ≤ ∑ ℓ : Fin 49,
          (endpointShellCount n ℓ : ℝ) * endpointPointProbabilityUpper n u := by
        apply Finset.sum_le_sum
        intro ℓ _hℓ
        exact hinner ℓ
  have hcount := endpointShellCounts_sum_cast_le (by omega : 0 < n)
  have hupper0 : 0 ≤ endpointPointProbabilityUpper n u := by
    unfold endpointPointProbabilityUpper
    exact add_nonneg
      (mul_nonneg (by positivity) (rigidityPower_nonneg n _)) (by positivity)
  unfold endpointWitnessProbabilityUpper
  calc
    uniformProbability (HasRightEndpointCoverWitness n u) ≤
        ∑ ℓ : Fin 49,
          (endpointShellCount n ℓ : ℝ) * endpointPointProbabilityUpper n u := hsum
    _ = (∑ ℓ : Fin 49, (endpointShellCount n ℓ : ℝ)) *
          endpointPointProbabilityUpper n u := by
      rw [Finset.sum_mul]
    _ = (∑ ℓ ∈ Finset.range 49, (endpointShellCount n ℓ : ℝ)) *
          endpointPointProbabilityUpper n u := by
      congr 1
    _ ≤ (98 * rigidityPower n (9 / 128)) *
          endpointPointProbabilityUpper n u :=
      mul_le_mul_of_nonneg_right hcount hupper0

lemma endpointWitnessProbabilityUpper_tendsto_zero (u : ℝ) :
    Tendsto (fun n : ℕ ↦ endpointWitnessProbabilityUpper n u)
      atTop (𝓝 0) := by
  let C : ℝ := Real.exp (1 / 2) * (Real.pi ^ 2 / 2) *
    (1000000000 * (u + 2) ^ 2)
  have hfirstBase := tendsto_rigidityPower_neg_zero
    (show (0 : ℝ) < 5 / 128 by norm_num)
  have hfirst : Tendsto (fun n : ℕ ↦
      98 * C * rigidityPower n (-(5 / 128))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hfirstBase.const_mul (98 * C)
  have htailBase := tendsto_rigidityPower_mul_exp_neg_power_test
    (9 / 128) (18 / 128) (1 / 1024) (by norm_num) (by norm_num)
  have htail : Tendsto (fun n : ℕ ↦
      (196 * Real.exp (1 / 2)) *
        (rigidityPower n (9 / 128) *
          Real.exp (-(1 / 1024 : ℝ) * rigidityPower n (18 / 128))))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using htailBase.const_mul (196 * Real.exp (1 / 2))
  have hsum := hfirst.add htail
  have hsum' : Tendsto (fun n : ℕ ↦
      98 * C * rigidityPower n (-(5 / 128)) +
        (196 * Real.exp (1 / 2)) *
          (rigidityPower n (9 / 128) *
            Real.exp (-(1 / 1024 : ℝ) * rigidityPower n (18 / 128))))
      atTop (𝓝 0) := by simpa using hsum
  apply hsum'.congr'
  filter_upwards [Nat.eventually_pos] with n hn
  unfold endpointWitnessProbabilityUpper endpointPointProbabilityUpper
  dsimp [C]
  have hp : rigidityPower n (9 / 128) * rigidityPower n (-14 / 128) =
      rigidityPower n (-(5 / 128)) := by
    rw [← rigidityPower_add hn]
    congr 2
    norm_num
  rw [← hp]
  ring

theorem uniformProbability_leftEndpointCoverWitness_tendsto_zero
    (u : ℝ) (hu : 0 < u) :
    Tendsto (fun n : ℕ ↦ uniformProbability (HasLeftEndpointCoverWitness n u))
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun n ↦ uniformProbability_nonneg _)
  · filter_upwards [eventually_ge_atTop (1000 : ℕ)] with n hn
    exact uniformProbability_leftEndpointCoverWitness_le hn hu
  · exact endpointWitnessProbabilityUpper_tendsto_zero u

theorem uniformProbability_rightEndpointCoverWitness_tendsto_zero
    (u : ℝ) (hu : 0 < u) :
    Tendsto (fun n : ℕ ↦ uniformProbability (HasRightEndpointCoverWitness n u))
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun n ↦ uniformProbability_nonneg _)
  · filter_upwards [eventually_ge_atTop (1000 : ℕ)] with n hn
    exact uniformProbability_rightEndpointCoverWitness_le hn hu
  · exact endpointWitnessProbabilityUpper_tendsto_zero u

noncomputable def interiorCoverDelta (n : ℕ) (u : ℝ) : ℝ :=
  u / n + 2 * growingVelocityCutoff n * badArcCoarseWidth n

lemma growingVelocityCutoff_mul_badArcCoarseWidth
    {n : ℕ} (hn : 0 < n) :
    growingVelocityCutoff n * badArcCoarseWidth n =
      rigidityPower n (-31 / 128) := by
  unfold growingVelocityCutoff badArcCoarseWidth
  rw [← rigidityPower_add hn]
  congr 2
  norm_num

lemma interiorCoverDelta_pos
    {n : ℕ} (hn : 0 < n) {u : ℝ} (hu : 0 < u) :
    0 < interiorCoverDelta n u := by
  unfold interiorCoverDelta
  exact add_pos_of_pos_of_nonneg (div_pos hu (by exact_mod_cast hn))
    (mul_nonneg (mul_nonneg (by norm_num) (growingVelocityCutoff_nonneg n))
      (badArcCoarseWidth_pos hn).le)

lemma interiorCoverDelta_upper
    {n : ℕ} (hn : 0 < n) {u : ℝ} (hu : 0 ≤ u) :
    interiorCoverDelta n u ≤
      (u + 2) * rigidityPower n (-31 / 128) := by
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hexp : (-1 : ℝ) ≤ -31 / 128 := by norm_num
  have hpower : rigidityPower n (-1) ≤ rigidityPower n (-31 / 128) := by
    unfold rigidityPower
    exact Real.rpow_le_rpow_of_exponent_le hnOne hexp
  have hinv : (n : ℝ)⁻¹ = rigidityPower n (-1) := by
    unfold rigidityPower
    rw [Real.rpow_neg (by exact_mod_cast hn.le), Real.rpow_one]
  unfold interiorCoverDelta
  rw [div_eq_mul_inv, hinv]
  rw [show 2 * growingVelocityCutoff n * badArcCoarseWidth n =
      2 * (growingVelocityCutoff n * badArcCoarseWidth n) by ring,
    growingVelocityCutoff_mul_badArcCoarseWidth hn]
  calc
    u * rigidityPower n (-1) + 2 * rigidityPower n (-31 / 128) ≤
        u * rigidityPower n (-31 / 128) +
          2 * rigidityPower n (-31 / 128) := by
      gcongr
    _ = (u + 2) * rigidityPower n (-31 / 128) := by ring

lemma interior_hasPositionCovarianceLower
    {n : ℕ} (hn : 1000 ≤ n) {q : ℝ}
    (hq : q ∈ Set.Icc (10 : ℝ) (Real.pi * n - 10)) :
    HasPositionCovarianceLower n (fun _ : Fin 1 ↦ q) (1 / 10) := by
  by_cases hhalf : q ≤ Real.pi * n / 2
  · exact endpoint_hasPositionCovarianceLower_far_zero n hn q hq.1 hhalf
  · have hqHalf : Real.pi * n / 2 ≤ q := le_of_not_ge hhalf
    have hdTen : 10 ≤ Real.pi * n - q := by linarith [hq.2]
    have hdHalf : Real.pi * n - q ≤ Real.pi * n / 2 := by linarith
    have hcov := endpoint_hasPositionCovarianceLower_far_pi n hn
      (Real.pi * n - q) hdTen hdHalf
    convert hcov using 1
    funext i
    ring

lemma interior_delta_sq_div_gamma_upper
    {n : ℕ} (hn : 0 < n) {u : ℝ} (hu : 0 ≤ u) :
    interiorCoverDelta n u ^ 2 / (1 / 10 : ℝ) ≤
      (10 * (u + 2) ^ 2) * rigidityPower n (-62 / 128) := by
  have hdelta := interiorCoverDelta_upper hn hu
  have hdelta0 : 0 ≤ interiorCoverDelta n u := by
    unfold interiorCoverDelta
    exact add_nonneg (div_nonneg hu (Nat.cast_nonneg n))
      (mul_nonneg (mul_nonneg (by norm_num) (growingVelocityCutoff_nonneg n))
        (badArcCoarseWidth_pos hn).le)
  have hpow0 : 0 ≤ rigidityPower n (-31 / 128) :=
    rigidityPower_nonneg n _
  have hsquare := (sq_le_sq₀ hdelta0
    (mul_nonneg (by linarith) hpow0)).2 hdelta
  have hpower : rigidityPower n (-31 / 128) ^ 2 =
      rigidityPower n (-62 / 128) := by
    rw [pow_two, ← rigidityPower_add hn]
    congr 2
    norm_num
  calc
    interiorCoverDelta n u ^ 2 / (1 / 10 : ℝ) =
        10 * interiorCoverDelta n u ^ 2 := by ring
    _ ≤ 10 * ((u + 2) * rigidityPower n (-31 / 128)) ^ 2 := by
      gcongr
    _ = (10 * (u + 2) ^ 2) * rigidityPower n (-62 / 128) := by
      rw [mul_pow, hpower]
      ring

lemma interior_smoothing_exponent_lower
    {n : ℕ} (hn : 0 < n) {u : ℝ} (hu : 0 ≤ u) :
    (1 / 1024 : ℝ) * rigidityPower n (66 / 128) ≤
      interiorCoverDelta n u ^ 2 / 4 * phaseNoWrapRadius n 1 ^ 2 := by
  have hcore : 2 * rigidityPower n (-31 / 128) ≤ interiorCoverDelta n u := by
    unfold interiorCoverDelta
    rw [show 2 * growingVelocityCutoff n * badArcCoarseWidth n =
      2 * (growingVelocityCutoff n * badArcCoarseWidth n) by ring,
      growingVelocityCutoff_mul_badArcCoarseWidth hn]
    exact le_add_of_nonneg_left (div_nonneg hu (Nat.cast_nonneg n))
  have hcore0 : 0 ≤ 2 * rigidityPower n (-31 / 128) :=
    mul_nonneg (by norm_num) (rigidityPower_nonneg n _)
  have hdelta0 : 0 ≤ interiorCoverDelta n u := hcore0.trans hcore
  have hsquare := (sq_le_sq₀ hcore0 hdelta0).2 hcore
  have hdeltaSq : rigidityPower n (-31 / 128) ^ 2 ≤
      interiorCoverDelta n u ^ 2 / 4 := by nlinarith
  have hR := phaseNoWrapRadius_one_sq_lower n
  have hmul : rigidityPower n (-31 / 128) ^ 2 * ((n : ℝ) / 1024) ≤
      (interiorCoverDelta n u ^ 2 / 4) * phaseNoWrapRadius n 1 ^ 2 := by
    exact mul_le_mul hdeltaSq hR (by positivity) (by positivity)
  have hpower : rigidityPower n (-31 / 128) ^ 2 * (n : ℝ) =
      rigidityPower n (66 / 128) := by
    rw [pow_two, ← rigidityPower_add hn]
    rw [show (n : ℝ) = rigidityPower n 1 by simp [rigidityPower],
      ← rigidityPower_add hn]
    congr 2
    norm_num
  calc
    (1 / 1024 : ℝ) * rigidityPower n (66 / 128) =
        rigidityPower n (-31 / 128) ^ 2 * ((n : ℝ) / 1024) := by
      rw [← hpower]
      ring
    _ ≤ _ := hmul

noncomputable def interiorPointProbabilityUpper (n : ℕ) (u : ℝ) : ℝ :=
  (Real.exp (1 / 2) * (Real.pi ^ 2 / 2) *
      (10 * (u + 2) ^ 2)) * rigidityPower n (-62 / 128) +
    2 * Real.exp (1 / 2) *
      Real.exp (-(1 / 1024 : ℝ) * rigidityPower n (66 / 128))

lemma interior_point_probability_le
    {n : ℕ} (hn : 1000 ≤ n) {u : ℝ} (hu : 0 < u) (q : ℝ) :
    uniformProbability (fun e : SignVector (2 * n) ↦
      q ∈ Set.Icc (10 : ℝ) (Real.pi * n - 10) ∧
        ‖rescaledCenteredEval n e q‖ ≤ interiorCoverDelta n u) ≤
      interiorPointProbabilityUpper n u := by
  by_cases hq : q ∈ Set.Icc (10 : ℝ) (Real.pi * n - 10)
  · have hcov := interior_hasPositionCovarianceLower hn hq
    have hprob := uniformProbability_eval_ball_le n q (1 / 10)
      (interiorCoverDelta n u) (by norm_num)
      (interiorCoverDelta_pos (by omega) hu) hcov
    have hratio := interior_delta_sq_div_gamma_upper
      (by omega : 0 < n) hu.le
    have hsmooth := interior_smoothing_exponent_lower
      (by omega : 0 < n) hu.le
    have htail : Real.exp
          (-(interiorCoverDelta n u ^ 2 / 4) * phaseNoWrapRadius n 1 ^ 2) ≤
        Real.exp (-(1 / 1024 : ℝ) * rigidityPower n (66 / 128)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hevent : (fun e : SignVector (2 * n) ↦
        q ∈ Set.Icc (10 : ℝ) (Real.pi * n - 10) ∧
          ‖rescaledCenteredEval n e q‖ ≤ interiorCoverDelta n u) =
        (fun e : SignVector (2 * n) ↦
          ‖rescaledCenteredEval n e q‖ ≤ interiorCoverDelta n u) := by
      funext e
      simp [hq]
    rw [hevent]
    exact hprob.trans (by
      unfold positionSmallBallUpper interiorPointProbabilityUpper
      have hC : 0 ≤ Real.exp (1 / 2) * (Real.pi ^ 2 / 2) := by positivity
      have hfirst := mul_le_mul_of_nonneg_left hratio hC
      have hfirst' :
          Real.exp (1 / 2) * (Real.pi ^ 2 / 2) *
              (interiorCoverDelta n u ^ 2 / (1 / 10)) ≤
            (Real.exp (1 / 2) * (Real.pi ^ 2 / 2) *
              (10 * (u + 2) ^ 2)) * rigidityPower n (-62 / 128) := by
        calc
          _ ≤ (Real.exp (1 / 2) * (Real.pi ^ 2 / 2)) *
              ((10 * (u + 2) ^ 2) * rigidityPower n (-62 / 128)) := hfirst
          _ = _ := by ring
      exact add_le_add hfirst'
        (mul_le_mul_of_nonneg_left htail (by positivity)))
  · have hzero : uniformProbability (fun e : SignVector (2 * n) ↦
        q ∈ Set.Icc (10 : ℝ) (Real.pi * n - 10) ∧
          ‖rescaledCenteredEval n e q‖ ≤ interiorCoverDelta n u) = 0 := by
      unfold uniformProbability
      simp [hq]
    rw [hzero]
    unfold interiorPointProbabilityUpper
    exact add_nonneg
      (mul_nonneg (by positivity) (rigidityPower_nonneg n _)) (by positivity)

def HasInteriorCoverWitness (n : ℕ) (u : ℝ)
    (e : SignVector (2 * n)) : Prop :=
  ∃ q : ↥(interiorArcCover n),
    (q : ℝ) ∈ Set.Icc (10 : ℝ) (Real.pi * n - 10) ∧
      ‖rescaledCenteredEval n e q‖ ≤ interiorCoverDelta n u

noncomputable def interiorWitnessProbabilityUpper (n : ℕ) (u : ℝ) : ℝ :=
  2145 * rigidityPower n (56 / 128) * interiorPointProbabilityUpper n u

lemma uniformProbability_interiorCoverWitness_le
    {n : ℕ} (hn : 1000 ≤ n) {u : ℝ} (hu : 0 < u) :
    uniformProbability (HasInteriorCoverWitness n u) ≤
      interiorWitnessProbabilityUpper n u := by
  let P : ↥(interiorArcCover n) → SignVector (2 * n) → Prop := fun q e ↦
    (q : ℝ) ∈ Set.Icc (10 : ℝ) (Real.pi * n - 10) ∧
      ‖rescaledCenteredEval n e q‖ ≤ interiorCoverDelta n u
  have houter := uniformProbability_exists_le_sum P
  have hpoint : ∀ q : ↥(interiorArcCover n),
      uniformProbability (P q) ≤ interiorPointProbabilityUpper n u := by
    intro q
    exact interior_point_probability_le hn hu q
  have hcard := interiorArcCover_card_cast_le (by omega : 0 < n)
  have hupper0 : 0 ≤ interiorPointProbabilityUpper n u := by
    unfold interiorPointProbabilityUpper
    exact add_nonneg
      (mul_nonneg (by positivity) (rigidityPower_nonneg n _)) (by positivity)
  unfold interiorWitnessProbabilityUpper
  calc
    uniformProbability (HasInteriorCoverWitness n u) =
        uniformProbability (fun e ↦ ∃ q : ↥(interiorArcCover n), P q e) := by rfl
    _ ≤ ∑ q : ↥(interiorArcCover n), uniformProbability (P q) := houter
    _ ≤ ∑ _q : ↥(interiorArcCover n), interiorPointProbabilityUpper n u := by
      apply Finset.sum_le_sum
      intro q _hq
      exact hpoint q
    _ = ((interiorArcCover n).card : ℝ) *
        interiorPointProbabilityUpper n u := by simp
    _ ≤ (2145 * rigidityPower n (7 / 16)) *
        interiorPointProbabilityUpper n u :=
      mul_le_mul_of_nonneg_right hcard hupper0
    _ = 2145 * rigidityPower n (56 / 128) *
        interiorPointProbabilityUpper n u := by norm_num

lemma interiorWitnessProbabilityUpper_tendsto_zero (u : ℝ) :
    Tendsto (fun n : ℕ ↦ interiorWitnessProbabilityUpper n u)
      atTop (𝓝 0) := by
  let C : ℝ := Real.exp (1 / 2) * (Real.pi ^ 2 / 2) *
    (10 * (u + 2) ^ 2)
  have hfirstBase := tendsto_rigidityPower_neg_zero
    (show (0 : ℝ) < 6 / 128 by norm_num)
  have hfirst : Tendsto (fun n : ℕ ↦
      2145 * C * rigidityPower n (-(6 / 128))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hfirstBase.const_mul (2145 * C)
  have htailBase := tendsto_rigidityPower_mul_exp_neg_power_test
    (56 / 128) (66 / 128) (1 / 1024) (by norm_num) (by norm_num)
  have htail : Tendsto (fun n : ℕ ↦
      (4290 * Real.exp (1 / 2)) *
        (rigidityPower n (56 / 128) *
          Real.exp (-(1 / 1024 : ℝ) * rigidityPower n (66 / 128))))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using htailBase.const_mul (4290 * Real.exp (1 / 2))
  have hsum := hfirst.add htail
  have hsum' : Tendsto (fun n : ℕ ↦
      2145 * C * rigidityPower n (-(6 / 128)) +
        (4290 * Real.exp (1 / 2)) *
          (rigidityPower n (56 / 128) *
            Real.exp (-(1 / 1024 : ℝ) * rigidityPower n (66 / 128))))
      atTop (𝓝 0) := by simpa using hsum
  apply hsum'.congr'
  filter_upwards [Nat.eventually_pos] with n hn
  unfold interiorWitnessProbabilityUpper interiorPointProbabilityUpper
  dsimp [C]
  have hp : rigidityPower n (56 / 128) * rigidityPower n (-62 / 128) =
      rigidityPower n (-(6 / 128)) := by
    rw [← rigidityPower_add hn]
    congr 2
    norm_num
  rw [← hp]
  ring

theorem uniformProbability_interiorCoverWitness_tendsto_zero
    (u : ℝ) (hu : 0 < u) :
    Tendsto (fun n : ℕ ↦ uniformProbability (HasInteriorCoverWitness n u))
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun n ↦ uniformProbability_nonneg _)
  · filter_upwards [eventually_ge_atTop (1000 : ℕ)] with n hn
    exact uniformProbability_interiorCoverWitness_le hn hu
  · exact interiorWitnessProbabilityUpper_tendsto_zero u

end Erdos525
