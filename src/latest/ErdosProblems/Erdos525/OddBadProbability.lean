import ErdosProblems.Erdos525.OddHighMinimum
import ErdosProblems.Erdos525.BadProbability

open scoped BigOperators Topology ComplexConjugate RealInnerProductSpace

namespace Erdos525

open Classical Filter Finset Set MeasureTheory

namespace Odd

lemma norm_normalizedPositionEuclideanWalk_singleton
    (n : ℕ) (e : SignVector (2 * n + 1)) (t : ℝ) :
    ‖normalizedPositionEuclideanWalk n e (fun _ : Fin 1 ↦ t)‖ =
      ‖eval n e t‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [norm_normalizedPositionEuclideanWalk_sq]
  simp

lemma uniformProbability_eval_ball_le
    (n : ℕ) (hn : 0 < n) (t gamma delta : ℝ)
    (hgamma : 0 < gamma) (hdelta : 0 < delta)
    (hcov : HasPositionCovarianceLower n (fun _ : Fin 1 ↦ t) gamma) :
    uniformProbability (fun e : SignVector (2 * n + 1) ↦
        ‖eval n e t‖ ≤ delta) ≤
      positionSmallBallUpper n gamma (2 * delta) := by
  have hinvTwo : (prefixScale n)⁻¹ ≤ 2 := by
    have hsub := prefixScale_inv_sub_one_le_inv_nat n hn
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hinvN : (n : ℝ)⁻¹ ≤ 1 := by
      exact (inv_le_one₀ (by positivity : (0 : ℝ) < n)).2 hnOne
    have hsub' : (prefixScale n)⁻¹ - 1 ≤ 1 :=
      hsub.trans (by simpa [one_div] using hinvN)
    linarith
  have hconditional : ∀ b : Bool,
      uniformProbability (fun e : SignVector (2 * n) ↦
        ‖eval n (appendSign n e b) t‖ ≤ delta) ≤
          positionSmallBallUpper n gamma (2 * delta) := by
    intro b
    let center : PositionEuclidean 1 :=
      -((prefixScale n)⁻¹ •
        extraPositionEuclidean n b (fun _ : Fin 1 ↦ t))
    have hmono : uniformProbability (fun e : SignVector (2 * n) ↦
          ‖eval n (appendSign n e b) t‖ ≤ delta) ≤
        uniformProbability (fun e : SignVector (2 * n) ↦
          ‖Erdos525.normalizedPositionEuclideanWalk n e
              (fun _ : Fin 1 ↦ t) - center‖ ≤ 2 * delta) := by
      apply uniformProbability_mono
      intro e he
      have hinvPos : 0 < (prefixScale n)⁻¹ :=
        inv_pos.mpr (prefixScale_pos n)
      have heq :
          Erdos525.normalizedPositionEuclideanWalk n e
              (fun _ : Fin 1 ↦ t) - center =
            (prefixScale n)⁻¹ •
              normalizedPositionEuclideanWalk n (appendSign n e b)
                (fun _ : Fin 1 ↦ t) := by
        rw [normalizedPositionEuclideanWalk_appendSign]
        dsimp [center]
        have hscale0 : prefixScale n ≠ 0 := (prefixScale_pos n).ne'
        rw [smul_add, smul_smul, inv_mul_cancel₀ hscale0, one_smul]
        module
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hinvPos,
        norm_normalizedPositionEuclideanWalk_singleton]
      calc
        (prefixScale n)⁻¹ * ‖eval n (appendSign n e b) t‖ ≤
            (prefixScale n)⁻¹ * delta :=
          mul_le_mul_of_nonneg_left he hinvPos.le
        _ ≤ 2 * delta := mul_le_mul_of_nonneg_right hinvTwo hdelta.le
    have hraw := uniformProbability_positionBall_le_of_positionCovariance
      n 1 (fun _ : Fin 1 ↦ t) gamma (2 * delta) (2 * delta)
        hgamma (mul_pos (by norm_num) hdelta)
        (mul_nonneg (by norm_num) hdelta.le) hcov center
    refine hmono.trans (hraw.trans_eq ?_)
    unfold positionSmallBallUpper
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hd : 2 * delta ≠ 0 := (mul_ne_zero (by norm_num) hdelta.ne')
    have hg : gamma ≠ 0 := hgamma.ne'
    rw [pow_one, pow_one, pow_one]
    have hexp : Real.exp (-((2 * delta) ^ 2 / (2 * (2 * delta) ^ 2))) =
        Real.exp (-(1 / 2 : ℝ)) := by
      congr 1
      field_simp [hd]
    rw [hexp, Real.exp_neg]
    field_simp [hpi, hd, hg]
    ring
  rw [uniformProbability_split]
  have hfalse := hconditional false
  have htrue := hconditional true
  linarith

lemma positionSmallBallUpper_two_le_four
    (n : ℕ) (gamma delta : ℝ) (hgamma : 0 < gamma) :
    positionSmallBallUpper n gamma (2 * delta) ≤
      4 * positionSmallBallUpper n gamma delta := by
  have htail : Real.exp (-((2 * delta) ^ 2 / 4) *
        phaseNoWrapRadius n 1 ^ 2) ≤
      Real.exp (-(delta ^ 2 / 4) * phaseNoWrapRadius n 1 ^ 2) := by
    apply Real.exp_le_exp.mpr
    have hr0 : 0 ≤ phaseNoWrapRadius n 1 ^ 2 := sq_nonneg _
    nlinarith [sq_nonneg delta]
  unfold positionSmallBallUpper
  have hC : 0 ≤ Real.exp (1 / 2) * (Real.pi ^ 2 / 2) := by positivity
  have hD : 0 ≤ 2 * Real.exp (1 / 2) := by positivity
  have hfirst :
      Real.exp (1 / 2) * (Real.pi ^ 2 / 2) *
          ((2 * delta) ^ 2 / gamma) =
        4 * (Real.exp (1 / 2) * (Real.pi ^ 2 / 2) *
          (delta ^ 2 / gamma)) := by ring
  rw [hfirst]
  have htail' := mul_le_mul_of_nonneg_left htail hD
  nlinarith [Real.exp_pos (-(delta ^ 2 / 4) *
    phaseNoWrapRadius n 1 ^ 2)]

lemma endpointPointProbabilityUpper_nonneg (n : ℕ) (u : ℝ) :
    0 ≤ endpointPointProbabilityUpper n u := by
  unfold endpointPointProbabilityUpper
  exact add_nonneg
    (mul_nonneg (by positivity) (rigidityPower_nonneg n _)) (by positivity)

lemma interiorPointProbabilityUpper_nonneg (n : ℕ) (u : ℝ) :
    0 ≤ interiorPointProbabilityUpper n u := by
  unfold interiorPointProbabilityUpper
  exact add_nonneg
    (mul_nonneg (by positivity) (rigidityPower_nonneg n _)) (by positivity)

lemma endpoint_point_probability_le_of_covariance
    {n : ℕ} (hn : 1000 ≤ n) {u : ℝ} (hu : 0 < u)
    {ℓ : ℕ} (hℓ : ℓ < 49) (q : ℝ)
    (hcov : HasPositionCovarianceLower n (fun _ : Fin 1 ↦ q)
      (endpointCoverGamma n ℓ)) :
    uniformProbability (fun e : SignVector (2 * n + 1) ↦
        ‖eval n e q‖ ≤ endpointCoverDelta n ℓ u) ≤
      4 * endpointPointProbabilityUpper n u := by
  have hnpos : 0 < n := by omega
  have hgamma := endpointCoverGamma_pos hnpos ℓ
  have hdelta := endpointCoverDelta_pos hnpos hu ℓ
  have hprob := uniformProbability_eval_ball_le n hnpos q
    (endpointCoverGamma n ℓ) (endpointCoverDelta n ℓ u)
      hgamma hdelta hcov
  have htwo := positionSmallBallUpper_two_le_four n
    (endpointCoverGamma n ℓ) (endpointCoverDelta n ℓ u) hgamma
  have hratio := endpoint_delta_sq_div_gamma_upper hnpos hu.le hℓ
  have hsmooth := endpoint_smoothing_exponent_lower hnpos hu.le hℓ
  have htail : Real.exp
        (-(endpointCoverDelta n ℓ u ^ 2 / 4) *
          phaseNoWrapRadius n 1 ^ 2) ≤
      Real.exp (-(1 / 1024 : ℝ) * rigidityPower n (18 / 128)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    uniformProbability (fun e : SignVector (2 * n + 1) ↦
        ‖eval n e q‖ ≤ endpointCoverDelta n ℓ u) ≤
        positionSmallBallUpper n (endpointCoverGamma n ℓ)
          (2 * endpointCoverDelta n ℓ u) := hprob
    _ ≤ 4 * positionSmallBallUpper n (endpointCoverGamma n ℓ)
          (endpointCoverDelta n ℓ u) := htwo
    _ ≤ 4 * endpointPointProbabilityUpper n u := by
      gcongr
      unfold positionSmallBallUpper endpointPointProbabilityUpper
      have hC : 0 ≤ Real.exp (1 / 2) * (Real.pi ^ 2 / 2) := by positivity
      exact add_le_add
        (calc
          Real.exp (1 / 2) * (Real.pi ^ 2 / 2) *
              (endpointCoverDelta n ℓ u ^ 2 / endpointCoverGamma n ℓ) ≤
            (Real.exp (1 / 2) * (Real.pi ^ 2 / 2)) *
              ((1000000000 * (u + 2) ^ 2) *
                rigidityPower n (-14 / 128)) :=
            mul_le_mul_of_nonneg_left hratio hC
          _ = (Real.exp (1 / 2) * (Real.pi ^ 2 / 2) *
              (1000000000 * (u + 2) ^ 2)) *
                rigidityPower n (-14 / 128) := by ring)
        (mul_le_mul_of_nonneg_left htail (by positivity))

def HasLeftEndpointCoverWitness (n : ℕ) (u : ℝ)
    (e : SignVector (2 * n + 1)) : Prop :=
  ∃ ℓ : Fin 49, ∃ b : Fin (endpointShellCount n ℓ),
    endpointShellPoint n ℓ b ∈ Set.Icc (0 : ℝ) 11 ∧
      ‖eval n e (endpointShellPoint n ℓ b)‖ ≤ endpointCoverDelta n ℓ u

def HasRightEndpointCoverWitness (n : ℕ) (u : ℝ)
    (e : SignVector (2 * n + 1)) : Prop :=
  ∃ ℓ : Fin 49, ∃ b : Fin (endpointShellCount n ℓ),
    endpointShellPoint n ℓ b ∈ Set.Icc (0 : ℝ) 11 ∧
      ‖eval n e (Real.pi * n - endpointShellPoint n ℓ b)‖ ≤
        endpointCoverDelta n ℓ u

lemma uniformProbability_leftEndpointCoverWitness_le
    {n : ℕ} (hn : 1000 ≤ n) {u : ℝ} (hu : 0 < u) :
    uniformProbability (HasLeftEndpointCoverWitness n u) ≤
      4 * endpointWitnessProbabilityUpper n u := by
  let P : Fin 49 → SignVector (2 * n + 1) → Prop := fun ℓ e ↦
    ∃ b : Fin (endpointShellCount n ℓ),
      endpointShellPoint n ℓ b ∈ Set.Icc (0 : ℝ) 11 ∧
        ‖eval n e (endpointShellPoint n ℓ b)‖ ≤ endpointCoverDelta n ℓ u
  have houter := uniformProbability_exists_le_sum P
  have hinner : ∀ ℓ : Fin 49,
      uniformProbability (P ℓ) ≤
        (endpointShellCount n ℓ : ℝ) *
          (4 * endpointPointProbabilityUpper n u) := by
    intro ℓ
    have hsum := uniformProbability_exists_le_sum
      (fun b : Fin (endpointShellCount n ℓ) ↦ fun e : SignVector (2 * n + 1) ↦
        endpointShellPoint n ℓ b ∈ Set.Icc (0 : ℝ) 11 ∧
          ‖eval n e (endpointShellPoint n ℓ b)‖ ≤ endpointCoverDelta n ℓ u)
    calc
      uniformProbability (P ℓ) ≤ ∑ b : Fin (endpointShellCount n ℓ),
          uniformProbability (fun e : SignVector (2 * n + 1) ↦
            endpointShellPoint n ℓ b ∈ Set.Icc (0 : ℝ) 11 ∧
              ‖eval n e (endpointShellPoint n ℓ b)‖ ≤
                endpointCoverDelta n ℓ u) := by simpa [P] using hsum
      _ ≤ ∑ _b : Fin (endpointShellCount n ℓ),
          4 * endpointPointProbabilityUpper n u := by
        apply Finset.sum_le_sum
        intro b _hb
        by_cases hq : endpointShellPoint n ℓ b ∈ Set.Icc (0 : ℝ) 11
        · have hqLower : endpointShellLower n ℓ ≤ endpointShellPoint n ℓ b := by
            unfold endpointShellPoint
            exact le_add_of_nonneg_right
              (mul_nonneg (Nat.cast_nonneg b) (endpointShellStep_pos (by omega) ℓ).le)
          have hhalf : endpointShellPoint n ℓ b ≤ Real.pi * n / 2 := by
            have hnR : (1000 : ℝ) ≤ n := by exact_mod_cast hn
            nlinarith [hq.2, Real.pi_gt_three]
          have hbase := endpoint_point_probability_le_of_covariance hn hu ℓ.isLt
            (endpointShellPoint n ℓ b)
            (endpoint_hasPositionCovarianceLower hn hqLower hq hhalf)
          apply (uniformProbability_mono (fun e he ↦ he.2)).trans hbase
        · have hzero : uniformProbability (fun e : SignVector (2 * n + 1) ↦
              endpointShellPoint n ℓ b ∈ Set.Icc (0 : ℝ) 11 ∧
                ‖eval n e (endpointShellPoint n ℓ b)‖ ≤
                  endpointCoverDelta n ℓ u) = 0 := by
            unfold uniformProbability
            simp [hq]
          rw [hzero]
          exact mul_nonneg (by norm_num) (endpointPointProbabilityUpper_nonneg n u)
      _ = _ := by simp
  have hsum : uniformProbability (HasLeftEndpointCoverWitness n u) ≤
      ∑ ℓ : Fin 49, (endpointShellCount n ℓ : ℝ) *
        (4 * endpointPointProbabilityUpper n u) := by
    calc
      _ = uniformProbability (fun e ↦ ∃ ℓ : Fin 49, P ℓ e) := by rfl
      _ ≤ ∑ ℓ : Fin 49, uniformProbability (P ℓ) := houter
      _ ≤ _ := Finset.sum_le_sum fun ℓ _hℓ ↦ hinner ℓ
  have hcount := endpointShellCounts_sum_cast_le (by omega : 0 < n)
  have hupper0 : 0 ≤ 4 * endpointPointProbabilityUpper n u := by
    exact mul_nonneg (by norm_num) (endpointPointProbabilityUpper_nonneg n u)
  unfold endpointWitnessProbabilityUpper
  calc
    _ ≤ ∑ ℓ : Fin 49, (endpointShellCount n ℓ : ℝ) *
        (4 * endpointPointProbabilityUpper n u) := hsum
    _ = (∑ ℓ : Fin 49, (endpointShellCount n ℓ : ℝ)) *
        (4 * endpointPointProbabilityUpper n u) := by rw [Finset.sum_mul]
    _ = (∑ ℓ ∈ Finset.range 49, (endpointShellCount n ℓ : ℝ)) *
        (4 * endpointPointProbabilityUpper n u) := by congr 1
    _ ≤ (98 * rigidityPower n (9 / 128)) *
        (4 * endpointPointProbabilityUpper n u) :=
      mul_le_mul_of_nonneg_right hcount hupper0
    _ = 4 * (98 * rigidityPower n (9 / 128) *
        endpointPointProbabilityUpper n u) := by ring

lemma uniformProbability_rightEndpointCoverWitness_le
    {n : ℕ} (hn : 1000 ≤ n) {u : ℝ} (hu : 0 < u) :
    uniformProbability (HasRightEndpointCoverWitness n u) ≤
      4 * endpointWitnessProbabilityUpper n u := by
  let P : Fin 49 → SignVector (2 * n + 1) → Prop := fun ℓ e ↦
    ∃ b : Fin (endpointShellCount n ℓ),
      endpointShellPoint n ℓ b ∈ Set.Icc (0 : ℝ) 11 ∧
        ‖eval n e (Real.pi * n - endpointShellPoint n ℓ b)‖ ≤
          endpointCoverDelta n ℓ u
  have houter := uniformProbability_exists_le_sum P
  have hinner : ∀ ℓ : Fin 49,
      uniformProbability (P ℓ) ≤
        (endpointShellCount n ℓ : ℝ) *
          (4 * endpointPointProbabilityUpper n u) := by
    intro ℓ
    have hsum := uniformProbability_exists_le_sum
      (fun b : Fin (endpointShellCount n ℓ) ↦ fun e : SignVector (2 * n + 1) ↦
        endpointShellPoint n ℓ b ∈ Set.Icc (0 : ℝ) 11 ∧
          ‖eval n e (Real.pi * n - endpointShellPoint n ℓ b)‖ ≤
            endpointCoverDelta n ℓ u)
    calc
      uniformProbability (P ℓ) ≤ ∑ b : Fin (endpointShellCount n ℓ),
          uniformProbability (fun e : SignVector (2 * n + 1) ↦
            endpointShellPoint n ℓ b ∈ Set.Icc (0 : ℝ) 11 ∧
              ‖eval n e (Real.pi * n - endpointShellPoint n ℓ b)‖ ≤
                endpointCoverDelta n ℓ u) := by simpa [P] using hsum
      _ ≤ ∑ _b : Fin (endpointShellCount n ℓ),
          4 * endpointPointProbabilityUpper n u := by
        apply Finset.sum_le_sum
        intro b _hb
        by_cases hd : endpointShellPoint n ℓ b ∈ Set.Icc (0 : ℝ) 11
        · have hdLower : endpointShellLower n ℓ ≤ endpointShellPoint n ℓ b := by
            unfold endpointShellPoint
            exact le_add_of_nonneg_right
              (mul_nonneg (Nat.cast_nonneg b) (endpointShellStep_pos (by omega) ℓ).le)
          have hhalf : endpointShellPoint n ℓ b ≤ Real.pi * n / 2 := by
            have hnR : (1000 : ℝ) ≤ n := by exact_mod_cast hn
            nlinarith [hd.2, Real.pi_gt_three]
          have hbase := endpoint_point_probability_le_of_covariance hn hu ℓ.isLt
            (Real.pi * n - endpointShellPoint n ℓ b)
            (endpoint_hasPositionCovarianceLower_pi hn hdLower hd hhalf)
          apply (uniformProbability_mono (fun e he ↦ he.2)).trans hbase
        · have hzero : uniformProbability (fun e : SignVector (2 * n + 1) ↦
              endpointShellPoint n ℓ b ∈ Set.Icc (0 : ℝ) 11 ∧
                ‖eval n e (Real.pi * n - endpointShellPoint n ℓ b)‖ ≤
                  endpointCoverDelta n ℓ u) = 0 := by
            unfold uniformProbability
            simp [hd]
          rw [hzero]
          exact mul_nonneg (by norm_num) (endpointPointProbabilityUpper_nonneg n u)
      _ = _ := by simp
  have hsum : uniformProbability (HasRightEndpointCoverWitness n u) ≤
      ∑ ℓ : Fin 49, (endpointShellCount n ℓ : ℝ) *
        (4 * endpointPointProbabilityUpper n u) := by
    calc
      _ = uniformProbability (fun e ↦ ∃ ℓ : Fin 49, P ℓ e) := by rfl
      _ ≤ ∑ ℓ : Fin 49, uniformProbability (P ℓ) := houter
      _ ≤ _ := Finset.sum_le_sum fun ℓ _hℓ ↦ hinner ℓ
  have hcount := endpointShellCounts_sum_cast_le (by omega : 0 < n)
  have hupper0 : 0 ≤ 4 * endpointPointProbabilityUpper n u := by
    exact mul_nonneg (by norm_num) (endpointPointProbabilityUpper_nonneg n u)
  unfold endpointWitnessProbabilityUpper
  calc
    _ ≤ ∑ ℓ : Fin 49, (endpointShellCount n ℓ : ℝ) *
        (4 * endpointPointProbabilityUpper n u) := hsum
    _ = (∑ ℓ : Fin 49, (endpointShellCount n ℓ : ℝ)) *
        (4 * endpointPointProbabilityUpper n u) := by rw [Finset.sum_mul]
    _ = (∑ ℓ ∈ Finset.range 49, (endpointShellCount n ℓ : ℝ)) *
        (4 * endpointPointProbabilityUpper n u) := by congr 1
    _ ≤ (98 * rigidityPower n (9 / 128)) *
        (4 * endpointPointProbabilityUpper n u) :=
      mul_le_mul_of_nonneg_right hcount hupper0
    _ = 4 * (98 * rigidityPower n (9 / 128) *
        endpointPointProbabilityUpper n u) := by ring

theorem uniformProbability_leftEndpointCoverWitness_tendsto_zero
    (u : ℝ) (hu : 0 < u) :
    Tendsto (fun n : ℕ ↦ uniformProbability (HasLeftEndpointCoverWitness n u))
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun n ↦ uniformProbability_nonneg _)
  · filter_upwards [eventually_ge_atTop (1000 : ℕ)] with n hn
    exact uniformProbability_leftEndpointCoverWitness_le hn hu
  · simpa only [mul_zero] using (endpointWitnessProbabilityUpper_tendsto_zero u).const_mul 4

theorem uniformProbability_rightEndpointCoverWitness_tendsto_zero
    (u : ℝ) (hu : 0 < u) :
    Tendsto (fun n : ℕ ↦ uniformProbability (HasRightEndpointCoverWitness n u))
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun n ↦ uniformProbability_nonneg _)
  · filter_upwards [eventually_ge_atTop (1000 : ℕ)] with n hn
    exact uniformProbability_rightEndpointCoverWitness_le hn hu
  · simpa only [mul_zero] using (endpointWitnessProbabilityUpper_tendsto_zero u).const_mul 4

def HasInteriorCoverWitness (n : ℕ) (u : ℝ)
    (e : SignVector (2 * n + 1)) : Prop :=
  ∃ q : ↥(interiorArcCover n),
    (q : ℝ) ∈ Set.Icc (10 : ℝ) (Real.pi * n - 10) ∧
      ‖eval n e q‖ ≤ interiorCoverDelta n u

lemma interior_point_probability_le
    {n : ℕ} (hn : 1000 ≤ n) {u : ℝ} (hu : 0 < u)
    (q : ↥(interiorArcCover n)) :
    uniformProbability (fun e : SignVector (2 * n + 1) ↦
      (q : ℝ) ∈ Set.Icc (10 : ℝ) (Real.pi * n - 10) ∧
        ‖eval n e q‖ ≤ interiorCoverDelta n u) ≤
      4 * interiorPointProbabilityUpper n u := by
  by_cases hq : (q : ℝ) ∈ Set.Icc (10 : ℝ) (Real.pi * n - 10)
  · have hnpos : 0 < n := by omega
    have hgamma : (0 : ℝ) < 1 / 10 := by norm_num
    have hdelta := interiorCoverDelta_pos hnpos hu
    have hcov := interior_hasPositionCovarianceLower hn hq
    have hprob := uniformProbability_eval_ball_le n hnpos (q : ℝ)
      (1 / 10) (interiorCoverDelta n u) hgamma hdelta hcov
    have htwo := positionSmallBallUpper_two_le_four n
      (1 / 10) (interiorCoverDelta n u) hgamma
    have hratio := interior_delta_sq_div_gamma_upper hnpos hu.le
    have hsmooth := interior_smoothing_exponent_lower hnpos hu.le
    have htail : Real.exp (-(interiorCoverDelta n u ^ 2 / 4) *
          phaseNoWrapRadius n 1 ^ 2) ≤
        Real.exp (-(1 / 1024 : ℝ) * rigidityPower n (66 / 128)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hbase : uniformProbability (fun e : SignVector (2 * n + 1) ↦
        ‖eval n e q‖ ≤ interiorCoverDelta n u) ≤
        4 * interiorPointProbabilityUpper n u :=
      hprob.trans (htwo.trans (by
        gcongr
        unfold positionSmallBallUpper interiorPointProbabilityUpper
        have hC : 0 ≤ Real.exp (1 / 2) * (Real.pi ^ 2 / 2) := by positivity
        exact add_le_add
          (calc
            Real.exp (1 / 2) * (Real.pi ^ 2 / 2) *
                (interiorCoverDelta n u ^ 2 / (1 / 10)) ≤
              (Real.exp (1 / 2) * (Real.pi ^ 2 / 2)) *
                ((10 * (u + 2) ^ 2) * rigidityPower n (-62 / 128)) :=
              mul_le_mul_of_nonneg_left hratio hC
            _ = (Real.exp (1 / 2) * (Real.pi ^ 2 / 2) *
                (10 * (u + 2) ^ 2)) * rigidityPower n (-62 / 128) := by ring)
          (mul_le_mul_of_nonneg_left htail (by positivity))))
    apply (uniformProbability_mono (fun e he ↦ he.2)).trans hbase
  · have hzero : uniformProbability (fun e : SignVector (2 * n + 1) ↦
        (q : ℝ) ∈ Set.Icc (10 : ℝ) (Real.pi * n - 10) ∧
          ‖eval n e q‖ ≤ interiorCoverDelta n u) = 0 := by
      unfold uniformProbability
      simp [hq]
    rw [hzero]
    exact mul_nonneg (by norm_num) (interiorPointProbabilityUpper_nonneg n u)

lemma uniformProbability_interiorCoverWitness_le
    {n : ℕ} (hn : 1000 ≤ n) {u : ℝ} (hu : 0 < u) :
    uniformProbability (HasInteriorCoverWitness n u) ≤
      4 * interiorWitnessProbabilityUpper n u := by
  let P : ↥(interiorArcCover n) → SignVector (2 * n + 1) → Prop := fun q e ↦
    (q : ℝ) ∈ Set.Icc (10 : ℝ) (Real.pi * n - 10) ∧
      ‖eval n e q‖ ≤ interiorCoverDelta n u
  have houter := uniformProbability_exists_le_sum P
  have hcard := interiorArcCover_card_cast_le (by omega : 0 < n)
  have hupper0 : 0 ≤ 4 * interiorPointProbabilityUpper n u := by
    exact mul_nonneg (by norm_num) (interiorPointProbabilityUpper_nonneg n u)
  unfold interiorWitnessProbabilityUpper
  calc
    uniformProbability (HasInteriorCoverWitness n u) =
        uniformProbability (fun e ↦ ∃ q : ↥(interiorArcCover n), P q e) := by rfl
    _ ≤ ∑ q : ↥(interiorArcCover n), uniformProbability (P q) := houter
    _ ≤ ∑ _q : ↥(interiorArcCover n),
        4 * interiorPointProbabilityUpper n u := by
      exact Finset.sum_le_sum fun q _hq ↦ interior_point_probability_le hn hu q
    _ = ((interiorArcCover n).card : ℝ) *
        (4 * interiorPointProbabilityUpper n u) := by simp
    _ ≤ (2145 * rigidityPower n (7 / 16)) *
        (4 * interiorPointProbabilityUpper n u) :=
      mul_le_mul_of_nonneg_right hcard hupper0
    _ = 4 * (2145 * rigidityPower n (56 / 128) *
        interiorPointProbabilityUpper n u) := by norm_num; ring

theorem uniformProbability_interiorCoverWitness_tendsto_zero
    (u : ℝ) (hu : 0 < u) :
    Tendsto (fun n : ℕ ↦ uniformProbability (HasInteriorCoverWitness n u))
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun n ↦ uniformProbability_nonneg _)
  · filter_upwards [eventually_ge_atTop (1000 : ℕ)] with n hn
    exact uniformProbability_interiorCoverWitness_le hn hu
  · simpa only [mul_zero] using (interiorWitnessProbabilityUpper_tendsto_zero u).const_mul 4

end Odd

end Erdos525
