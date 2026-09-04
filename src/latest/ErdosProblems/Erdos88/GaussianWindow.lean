import ErdosProblems.Erdos88.BoundedWindowAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos88
namespace BoundedWindowAnalytic

noncomputable def centeredGaussianVariance (sigma : ℝ) : ℝ≥0 :=
  ⟨sigma ^ 2, sq_nonneg sigma⟩

noncomputable def centeredGaussianLaw (sigma : ℝ) : Measure ℝ :=
  gaussianReal 0 (centeredGaussianVariance sigma)

noncomputable def centeredGaussianDensity (sigma x : ℝ) : ℝ :=
  gaussianPDFReal 0 (centeredGaussianVariance sigma) x

lemma charFun_centeredGaussianLaw_eq (sigma t : ℝ) :
    charFun (centeredGaussianLaw sigma) t =
      GaussianQuadratic.standardNormalChar (sigma * t) := by
  rw [centeredGaussianLaw, charFun_gaussianReal]
  unfold GaussianQuadratic.standardNormalChar
  push_cast
  congr 1
  have hv : ((centeredGaussianVariance sigma : ℝ≥0) : ℝ) = sigma ^ 2 := rfl
  rw [hv]
  push_cast
  ring

lemma centeredGaussianVariance_ne_zero {sigma : ℝ} (hsigma : 0 < sigma) :
    centeredGaussianVariance sigma ≠ 0 := by
  apply ne_of_gt
  change 0 < sigma ^ 2
  positivity

lemma hasContinuousDensity_centeredGaussianLaw {sigma : ℝ}
    (hsigma : 0 < sigma) :
    Esseen.HasContinuousDensity (centeredGaussianLaw sigma)
      (centeredGaussianDensity sigma) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold centeredGaussianDensity gaussianPDFReal centeredGaussianVariance
    fun_prop
  · intro x
    exact gaussianPDFReal_nonneg 0 (centeredGaussianVariance sigma) x
  · intro eps x heps
    unfold Esseen.smallBall centeredGaussianLaw centeredGaussianDensity
    rw [measureReal_def,
      gaussianReal_apply_eq_integral 0
        (centeredGaussianVariance_ne_zero hsigma)]
    have hnonneg : 0 ≤ ∫ y in Set.Icc (x - eps) (x + eps),
        gaussianPDFReal 0 (centeredGaussianVariance sigma) y := by
      apply setIntegral_nonneg measurableSet_Icc
      intro y hy
      exact gaussianPDFReal_nonneg 0 (centeredGaussianVariance sigma) y
    rw [ENNReal.toReal_ofReal hnonneg]
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact integral_Icc_eq_integral_Ioc

lemma sqrt_two_pi_mul_centeredGaussianVariance {sigma : ℝ}
    (hsigma : 0 ≤ sigma) :
    Real.sqrt (2 * Real.pi * (centeredGaussianVariance sigma : ℝ)) =
      Real.sqrt (2 * Real.pi) * sigma := by
  change Real.sqrt (2 * Real.pi * sigma ^ 2) = _
  rw [show 2 * Real.pi * sigma ^ 2 = (2 * Real.pi) * sigma ^ 2 by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq hsigma]

lemma centeredGaussianDensity_eq {sigma : ℝ} (hsigma : 0 < sigma)
    (x : ℝ) :
    centeredGaussianDensity sigma x =
      Real.exp (-(x / sigma) ^ 2 / 2) /
        (Real.sqrt (2 * Real.pi) * sigma) := by
  rw [centeredGaussianDensity, gaussianPDFReal,
    sqrt_two_pi_mul_centeredGaussianVariance hsigma.le]
  change (Real.sqrt (2 * Real.pi) * sigma)⁻¹ *
      Real.exp (-(x - 0) ^ 2 / (2 * sigma ^ 2)) = _
  rw [inv_mul_eq_div]
  congr 1
  field_simp [hsigma.ne']
  ring_nf

lemma one_le_sqrt_two_pi : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
  rw [Real.one_le_sqrt]
  linarith [Real.pi_gt_three]

lemma centeredGaussianDensity_le_one_div {sigma : ℝ} (hsigma : 0 < sigma)
    (x : ℝ) : centeredGaussianDensity sigma x ≤ 1 / sigma := by
  rw [centeredGaussianDensity_eq hsigma]
  have hden : 0 < Real.sqrt (2 * Real.pi) * sigma := by positivity
  have hexp : Real.exp (-(x / sigma) ^ 2 / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [sq_nonneg (x / sigma)]
  calc
    Real.exp (-(x / sigma) ^ 2 / 2) /
        (Real.sqrt (2 * Real.pi) * sigma) ≤
        1 / (Real.sqrt (2 * Real.pi) * sigma) :=
      (div_le_div_iff_of_pos_right hden).2 hexp
    _ ≤ 1 / sigma := by
      apply one_div_le_one_div_of_le hsigma
      nlinarith [one_le_sqrt_two_pi]

lemma smallBall_centeredGaussianLaw_le {sigma eps x : ℝ}
    (hsigma : 0 < sigma) (heps : 0 < eps) :
    Esseen.smallBall (centeredGaussianLaw sigma) eps x ≤ 2 * eps / sigma := by
  let f := centeredGaussianDensity sigma
  have hdens := hasContinuousDensity_centeredGaussianLaw hsigma
  rw [hdens.smallBall_eq_integral eps x heps.le]
  calc
    (∫ y in (x - eps)..(x + eps), f y) ≤
        ∫ _y in (x - eps)..(x + eps), (1 / sigma : ℝ) := by
      apply intervalIntegral.integral_mono_on (by linarith)
        (hdens.intervalIntegrable _ _) intervalIntegrable_const
      intro y hy
      exact centeredGaussianDensity_le_one_div hsigma y
    _ = 2 * eps / sigma := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      ring

lemma concentration_centeredGaussianLaw_le {sigma eps : ℝ}
    (hsigma : 0 < sigma) (heps : 0 < eps) :
    Esseen.concentration (centeredGaussianLaw sigma) eps ≤ 2 * eps / sigma := by
  apply csSup_le (Set.range_nonempty _)
  intro y hy
  rcases hy with ⟨x, rfl⟩
  exact smallBall_centeredGaussianLaw_le hsigma heps

lemma centeredGaussianDensity_le_localTail {sigma eps y z : ℝ}
    (hsigma : 0 < sigma) (heps : 0 < eps) (hepssigma : eps ≤ sigma)
    (hz : z ∈ Set.Icc (y - eps) (y + eps)) :
    centeredGaussianDensity sigma z ≤
      (4 / sigma) * Real.exp (-|y| / (8 * sigma)) := by
  have hzdist : |z - y| ≤ eps := by
    rw [abs_le]
    constructor <;> linarith [hz.1, hz.2]
  have hyabs : |y| ≤ |z| + eps := by
    calc
      |y| = |z + (y - z)| := by congr 1 <;> ring
      _ ≤ |z| + |y - z| := abs_add_le _ _
      _ = |z| + |z - y| := by rw [abs_sub_comm]
      _ ≤ |z| + eps := add_le_add_right hzdist _
  have hydiv : |y| / sigma ≤ |z| / sigma + 1 := by
    calc
      |y| / sigma ≤ (|z| + sigma) / sigma := by
        apply div_le_div_of_nonneg_right _ hsigma.le
        exact hyabs.trans (add_le_add_right hepssigma _)
      _ = |z| / sigma + 1 := by field_simp [hsigma.ne']
  have hsq : (|z| / sigma) ^ 2 = (z / sigma) ^ 2 := by
    field_simp [hsigma.ne']
    exact sq_abs z
  have hquad : -(z / sigma) ^ 2 / 2 ≤ 1 / 8 - (|z| / sigma) / 2 := by
    have h := sq_nonneg (|z| / sigma - 1 / 2)
    nlinarith [hsq]
  have hratio : |y| / (8 * sigma) = (|y| / sigma) / 8 := by
    field_simp [hsigma.ne']
  have hexponent : -(z / sigma) ^ 2 / 2 ≤ 1 - |y| / (8 * sigma) := by
    rw [hratio]
    nlinarith [abs_nonneg z]
  rw [centeredGaussianDensity_eq hsigma]
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) := by positivity
  calc
    Real.exp (-(z / sigma) ^ 2 / 2) /
        (Real.sqrt (2 * Real.pi) * sigma) ≤
        Real.exp (-(z / sigma) ^ 2 / 2) / sigma := by
      apply div_le_div_of_nonneg_left (Real.exp_pos _).le hsigma
      nlinarith [one_le_sqrt_two_pi]
    _ ≤ Real.exp (1 - |y| / (8 * sigma)) / sigma := by
      exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hexponent) hsigma.le
    _ = Real.exp 1 * Real.exp (-|y| / (8 * sigma)) / sigma := by
      rw [Real.exp_sub]
      have hneg : -|y| / (8 * sigma) = -(|y| / (8 * sigma)) := by ring
      rw [hneg, Real.exp_neg]
      simp only [div_eq_mul_inv]
    _ ≤ 4 * Real.exp (-|y| / (8 * sigma)) / sigma := by
      apply div_le_div_of_nonneg_right _ hsigma.le
      gcongr
      linarith [Real.exp_one_lt_three]
    _ = (4 / sigma) * Real.exp (-|y| / (8 * sigma)) := by ring

lemma smallBall_centeredGaussianLaw_le_localTail {sigma eps : ℝ}
    (hsigma : 0 < sigma) (heps : 0 < eps) (hepssigma : eps ≤ sigma)
    (y : ℝ) :
    Esseen.smallBall (centeredGaussianLaw sigma) eps y ≤
      (eps / ((1 / 8 : ℝ) * sigma)) *
        Real.exp (-(1 / 8 : ℝ) * |y| / sigma) := by
  let f := centeredGaussianDensity sigma
  have hdens := hasContinuousDensity_centeredGaussianLaw hsigma
  rw [hdens.smallBall_eq_integral eps y heps.le]
  calc
    (∫ z in (y - eps)..(y + eps), f z) ≤
        ∫ _z in (y - eps)..(y + eps),
          (4 / sigma) * Real.exp (-|y| / (8 * sigma)) := by
      apply intervalIntegral.integral_mono_on (by linarith)
        (hdens.intervalIntegrable _ _) intervalIntegrable_const
      intro z hz
      exact centeredGaussianDensity_le_localTail hsigma heps hepssigma hz
    _ = (eps / ((1 / 8 : ℝ) * sigma)) *
        Real.exp (-(1 / 8 : ℝ) * |y| / sigma) := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      field_simp [hsigma.ne']
      ring

lemma sqrt_two_pi_le_three : Real.sqrt (2 * Real.pi) ≤ (3 : ℝ) := by
  rw [Real.sqrt_le_iff]
  constructor
  · norm_num
  · nlinarith [Real.pi_lt_four]

lemma centeredGaussianDensity_lower {sigma M z : ℝ}
    (hsigma : 0 < sigma) (hM : 0 ≤ M) (hz : |z| ≤ M * sigma) :
    Real.exp (-(M ^ 2) / 2) / (3 * sigma) ≤
      centeredGaussianDensity sigma z := by
  have habsDiv : |z / sigma| ≤ M := by
    rw [abs_div, abs_of_pos hsigma]
    exact (div_le_iff₀ hsigma).2 hz
  have hsquare : (z / sigma) ^ 2 ≤ M ^ 2 := by
    nlinarith [sq_nonneg (M - |z / sigma|), sq_abs (z / sigma), abs_nonneg (z / sigma)]
  have hexp : Real.exp (-(M ^ 2) / 2) ≤
      Real.exp (-(z / sigma) ^ 2 / 2) := by
    rw [Real.exp_le_exp]
    linarith
  rw [centeredGaussianDensity_eq hsigma]
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) := by positivity
  calc
    Real.exp (-(M ^ 2) / 2) / (3 * sigma) ≤
        Real.exp (-(z / sigma) ^ 2 / 2) / (3 * sigma) := by
      exact div_le_div_of_nonneg_right hexp (by positivity)
    _ ≤ Real.exp (-(z / sigma) ^ 2 / 2) /
        (Real.sqrt (2 * Real.pi) * sigma) := by
      apply div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity)
      exact mul_le_mul_of_nonneg_right sqrt_two_pi_le_three hsigma.le

lemma smallBall_centeredGaussianLaw_lower {sigma eps M x : ℝ}
    (hsigma : 0 < sigma) (heps : 0 < eps) (hepssigma : eps ≤ sigma)
    (hM : 0 ≤ M) (hx : |x| ≤ M * sigma) :
    (2 * eps) * Real.exp (-((M + 1) ^ 2) / 2) / (3 * sigma) ≤
      Esseen.smallBall (centeredGaussianLaw sigma) eps x := by
  let f := centeredGaussianDensity sigma
  have hdens := hasContinuousDensity_centeredGaussianLaw hsigma
  rw [hdens.smallBall_eq_integral eps x heps.le]
  calc
    (2 * eps) * Real.exp (-((M + 1) ^ 2) / 2) / (3 * sigma) =
        ∫ _z in (x - eps)..(x + eps),
          Real.exp (-((M + 1) ^ 2) / 2) / (3 * sigma) := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      ring
    _ ≤ ∫ z in (x - eps)..(x + eps), f z := by
      apply intervalIntegral.integral_mono_on (by linarith)
        intervalIntegrable_const (hdens.intervalIntegrable _ _)
      intro z hz
      apply centeredGaussianDensity_lower hsigma (by linarith)
      have hzdist : |z - x| ≤ eps := by
        rw [abs_le]
        constructor <;> linarith [hz.1, hz.2]
      calc
        |z| = |x + (z - x)| := by congr 1 <;> ring
        _ ≤ |x| + |z - x| := abs_add_le _ _
        _ ≤ M * sigma + eps := add_le_add hx hzdist
        _ ≤ (M + 1) * sigma := by nlinarith

lemma centeredGaussianDensity_ratio_three {sigma y z : ℝ}
    (hsigma : 0 < sigma) (hdiff : z ^ 2 - y ^ 2 ≤ 2 * sigma ^ 2) :
    centeredGaussianDensity sigma y ≤
      3 * centeredGaussianDensity sigma z := by
  have hexponent : -(y / sigma) ^ 2 / 2 ≤
      -(z / sigma) ^ 2 / 2 + 1 := by
    field_simp [hsigma.ne']
    nlinarith
  have hexp : Real.exp (-(y / sigma) ^ 2 / 2) ≤
      3 * Real.exp (-(z / sigma) ^ 2 / 2) := by
    calc
      Real.exp (-(y / sigma) ^ 2 / 2) ≤
          Real.exp (-(z / sigma) ^ 2 / 2 + 1) :=
        Real.exp_le_exp.mpr hexponent
      _ = Real.exp (-(z / sigma) ^ 2 / 2) * Real.exp 1 := by
        rw [Real.exp_add]
      _ ≤ 3 * Real.exp (-(z / sigma) ^ 2 / 2) := by
        nlinarith [Real.exp_one_lt_three, Real.exp_pos (-(z / sigma) ^ 2 / 2)]
  rw [centeredGaussianDensity_eq hsigma, centeredGaussianDensity_eq hsigma]
  have hden : 0 ≤ Real.sqrt (2 * Real.pi) * sigma := by positivity
  calc
    Real.exp (-(y / sigma) ^ 2 / 2) /
        (Real.sqrt (2 * Real.pi) * sigma) ≤
        (3 * Real.exp (-(z / sigma) ^ 2 / 2)) /
          (Real.sqrt (2 * Real.pi) * sigma) :=
      div_le_div_of_nonneg_right hexp hden
    _ = 3 * (Real.exp (-(z / sigma) ^ 2 / 2) /
        (Real.sqrt (2 * Real.pi) * sigma)) := by ring

lemma densityRatioOn_centeredGaussian_three {sigma x eps R : ℝ}
    (hsigma : 0 < sigma) (heps : 0 ≤ eps) (hR : 0 ≤ R)
    (hscale : 2 * (R * eps) * (|x| + R * eps) ≤ sigma ^ 2) :
    Esseen.DensityRatioOn (centeredGaussianDensity sigma) x eps R 3 := by
  intro y z
  let d : ℝ := R * eps
  have hd : 0 ≤ d := mul_nonneg hR heps
  have hydist : |y.1 - x| ≤ d := by
    rw [abs_le]
    exact ⟨by linarith [y.2.1], by linarith [y.2.2]⟩
  have hzdist : |z.1 - x| ≤ d := by
    rw [abs_le]
    exact ⟨by linarith [z.2.1], by linarith [z.2.2]⟩
  have hyabs : |y.1| ≤ |x| + d := by
    calc
      |y.1| = |x + (y.1 - x)| := by congr 1 <;> ring
      _ ≤ |x| + |y.1 - x| := abs_add_le _ _
      _ ≤ |x| + d := add_le_add_right hydist _
  have hzabs : |z.1| ≤ |x| + d := by
    calc
      |z.1| = |x + (z.1 - x)| := by congr 1 <;> ring
      _ ≤ |x| + |z.1 - x| := abs_add_le _ _
      _ ≤ |x| + d := add_le_add_right hzdist _
  have hzydist : |z.1 - y.1| ≤ 2 * d := by
    rw [abs_le]
    constructor <;> linarith [y.2.1, y.2.2, z.2.1, z.2.2]
  have hsum : |z.1 + y.1| ≤ 2 * (|x| + d) := by
    calc
      |z.1 + y.1| ≤ |z.1| + |y.1| := abs_add_le _ _
      _ ≤ (|x| + d) + (|x| + d) := add_le_add hzabs hyabs
      _ = 2 * (|x| + d) := by ring
  have hdiff : z.1 ^ 2 - y.1 ^ 2 ≤ 2 * sigma ^ 2 := by
    calc
      z.1 ^ 2 - y.1 ^ 2 = (z.1 - y.1) * (z.1 + y.1) := by ring
      _ ≤ |(z.1 - y.1) * (z.1 + y.1)| := le_abs_self _
      _ = |z.1 - y.1| * |z.1 + y.1| := abs_mul _ _
      _ ≤ (2 * d) * (2 * (|x| + d)) := by
        exact mul_le_mul hzydist hsum (abs_nonneg _) (by positivity)
      _ ≤ 2 * sigma ^ 2 := by
        dsimp [d] at *
        nlinarith
  exact centeredGaussianDensity_ratio_three hsigma hdiff

lemma fourierError_graphCenteredLaw_centeredGaussianLaw {n : ℕ}
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    (sigma eps : ℝ) :
    Esseen.fourierError (graphCenteredLaw G e₀ c)
        (centeredGaussianLaw sigma) eps =
      fourierErrorAtRadius
        (GraphQuadratic.centeredGraphCharacteristic G e₀ c)
        (fun t ↦ GaussianQuadratic.standardNormalChar (sigma * t)) eps := by
  unfold Esseen.fourierError fourierErrorAtRadius
  apply intervalIntegral.integral_congr
  intro t ht
  change ‖charFun (graphCenteredLaw G e₀ c) t -
      charFun (centeredGaussianLaw sigma) t‖ =
    ‖GraphQuadratic.centeredGraphCharacteristic G e₀ c t -
      GaussianQuadratic.standardNormalChar (sigma * t)‖
  rw [charFun_graphCenteredLaw, charFun_centeredGaussianLaw_eq]

lemma smallBall_graphCenteredLaw_le_of_fourierL1 {n : ℕ}
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    {sigma gamma alpha nu scaleUpper cLinear cTail eta B : ℝ}
    (h : FrequencyBandHypotheses
      (GraphQuadratic.centeredGraphCharacteristic G e₀ c)
      (fun t ↦ GaussianQuadratic.standardNormalChar (sigma * t))
      n sigma gamma alpha nu scaleUpper cLinear cTail)
    (hFourier : fourierL1Error
      (GraphQuadratic.centeredGraphCharacteristic G e₀ c)
      (fun t ↦ GaussianQuadratic.standardNormalChar (sigma * t)) nu ≤
        eta / sigma)
    (hB : 0 < B) (hcut : 2 / B ≤ nu) (x : ℝ) :
    Esseen.smallBall (graphCenteredLaw G e₀ c) B x ≤
      (∑' k : ℤ, Esseen.kernelCellWeight k) *
        (2 * B + B * eta) / sigma := by
  let : IsProbabilityMeasure (graphCenteredLaw G e₀ c) := by
    unfold graphCenteredLaw
    infer_instance
  let : IsProbabilityMeasure (centeredGaussianLaw sigma) := by
    unfold centeredGaussianLaw
    infer_instance
  have herr : Esseen.fourierError (graphCenteredLaw G e₀ c)
      (centeredGaussianLaw sigma) B ≤ eta / sigma := by
    rw [fourierError_graphCenteredLaw_centeredGaussianLaw]
    exact (fourierErrorAtRadius_le_full h.cutoff_pos.le hB hcut
      h.error_intervalIntegrable).trans hFourier
  have hrel := Esseen.relative_esseen_6_1
    (graphCenteredLaw G e₀ c) (centeredGaussianLaw sigma) hB
  have hmass : 0 ≤ ∑' k : ℤ, Esseen.kernelCellWeight k :=
    tsum_nonneg Esseen.kernelCellWeight_nonneg
  calc
    Esseen.smallBall (graphCenteredLaw G e₀ c) B x ≤
        Esseen.concentration (graphCenteredLaw G e₀ c) B :=
      Esseen.smallBall_le_concentration _ _ _
    _ ≤ (∑' k : ℤ, Esseen.kernelCellWeight k) *
        (Esseen.concentration (centeredGaussianLaw sigma) B +
          B * Esseen.fourierError (graphCenteredLaw G e₀ c)
            (centeredGaussianLaw sigma) B) := hrel
    _ ≤ (∑' k : ℤ, Esseen.kernelCellWeight k) *
        (2 * B / sigma + B * (eta / sigma)) := by
      apply mul_le_mul_of_nonneg_left _ hmass
      exact add_le_add
        (concentration_centeredGaussianLaw_le h.sigma_pos hB)
        (mul_le_mul_of_nonneg_left herr hB.le)
    _ = (∑' k : ℤ, Esseen.kernelCellWeight k) *
        (2 * B + B * eta) / sigma := by ring

lemma smallBall_graphCenteredLaw_lower_of_fourierL1 {n : ℕ}
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    {sigma gamma alpha nu scaleUpper cLinear cTail eta eps M R x : ℝ}
    (h : FrequencyBandHypotheses
      (GraphQuadratic.centeredGraphCharacteristic G e₀ c)
      (fun t ↦ GaussianQuadratic.standardNormalChar (sigma * t))
      n sigma gamma alpha nu scaleUpper cLinear cTail)
    (hFourier : fourierL1Error
      (GraphQuadratic.centeredGraphCharacteristic G e₀ c)
      (fun t ↦ GaussianQuadratic.standardNormalChar (sigma * t)) nu ≤
        eta / sigma)
    (heps : 0 < eps) (hcut : 2 / eps ≤ nu) (hepssigma : eps ≤ sigma)
    (hM : 0 ≤ M) (hx : |x| ≤ M * sigma)
    (hR : 4 ≤ R)
    (hratio : Esseen.DensityRatioOn (centeredGaussianDensity sigma)
      x eps R 3) :
    (eps / sigma) *
        (Real.exp (-((M + 1) ^ 2) / 2) / 12 -
          Esseen.relativeEsseenConstant * (2 / R + eta)) ≤
      Esseen.smallBall (graphCenteredLaw G e₀ c) (30000 * eps) x := by
  let : IsProbabilityMeasure (graphCenteredLaw G e₀ c) := by
    unfold graphCenteredLaw
    infer_instance
  let : IsProbabilityMeasure (centeredGaussianLaw sigma) := by
    unfold centeredGaussianLaw
    infer_instance
  have herr : Esseen.fourierError (graphCenteredLaw G e₀ c)
      (centeredGaussianLaw sigma) eps ≤ eta / sigma := by
    rw [fourierError_graphCenteredLaw_centeredGaussianLaw]
    exact (fourierErrorAtRadius_le_full h.cutoff_pos.le heps hcut
      h.error_intervalIntegrable).trans hFourier
  have hZ := smallBall_centeredGaussianLaw_lower h.sigma_pos heps hepssigma hM hx
  have hconc := concentration_centeredGaussianLaw_le h.sigma_pos heps
  have hnoise :
      Esseen.concentration (centeredGaussianLaw sigma) eps / R +
          eps * Esseen.fourierError (graphCenteredLaw G e₀ c)
            (centeredGaussianLaw sigma) eps ≤
        (2 * eps / sigma) / R + eps * (eta / sigma) := by
    exact add_le_add
      ((div_le_div_iff_of_pos_right (lt_of_lt_of_le (by norm_num) hR)).2 hconc)
      (mul_le_mul_of_nonneg_left herr heps.le)
  have hrel := Esseen.relative_esseen_6_3
    (graphCenteredLaw G e₀ c) (centeredGaussianLaw sigma)
    (hasContinuousDensity_centeredGaussianLaw h.sigma_pos)
    heps (show (1 : ℝ) ≤ 3 by norm_num) hR hratio
  have hpositive :
      (1 / 8 : ℝ) *
          ((2 * eps) * Real.exp (-((M + 1) ^ 2) / 2) / (3 * sigma)) ≤
        (1 / 8 : ℝ) *
          Esseen.smallBall (centeredGaussianLaw sigma) eps x :=
    mul_le_mul_of_nonneg_left hZ (by norm_num)
  have hnoiseMul := mul_le_mul_of_nonneg_left hnoise
    Esseen.relativeEsseenConstant_nonneg
  calc
    (eps / sigma) *
        (Real.exp (-((M + 1) ^ 2) / 2) / 12 -
          Esseen.relativeEsseenConstant * (2 / R + eta)) =
        (1 / 8 : ℝ) *
            ((2 * eps) * Real.exp (-((M + 1) ^ 2) / 2) / (3 * sigma)) -
          Esseen.relativeEsseenConstant *
            ((2 * eps / sigma) / R + eps * (eta / sigma)) := by ring
    _ ≤ (1 / 8 : ℝ) *
          Esseen.smallBall (centeredGaussianLaw sigma) eps x -
        Esseen.relativeEsseenConstant *
          (Esseen.concentration (centeredGaussianLaw sigma) eps / R +
            eps * Esseen.fourierError (graphCenteredLaw G e₀ c)
              (centeredGaussianLaw sigma) eps) := by linarith
    _ ≤ Esseen.smallBall (graphCenteredLaw G e₀ c)
        ((10000 * 3) * eps) x := hrel
    _ = Esseen.smallBall (graphCenteredLaw G e₀ c) (30000 * eps) x := by
      norm_num

lemma graphGaussianError_intervalIntegrable {n : ℕ}
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    (sigma a b : ℝ) :
    IntervalIntegrable (fun t ↦
      ‖GraphQuadratic.centeredGraphCharacteristic G e₀ c t -
        GaussianQuadratic.standardNormalChar (sigma * t)‖) volume a b := by
  let : IsProbabilityMeasure (graphCenteredLaw G e₀ c) := by
    unfold graphCenteredLaw
    infer_instance
  let : IsProbabilityMeasure (centeredGaussianLaw sigma) := by
    unfold centeredGaussianLaw
    infer_instance
  have hc : Continuous (fun t ↦
      ‖charFun (graphCenteredLaw G e₀ c) t -
        charFun (centeredGaussianLaw sigma) t‖) :=
    (continuous_charFun.sub continuous_charFun).norm
  have hfun : (fun t ↦
      ‖charFun (graphCenteredLaw G e₀ c) t -
        charFun (centeredGaussianLaw sigma) t‖) =
      fun t ↦ ‖GraphQuadratic.centeredGraphCharacteristic G e₀ c t -
        GaussianQuadratic.standardNormalChar (sigma * t)‖ := by
    funext t
    rw [charFun_graphCenteredLaw, charFun_centeredGaussianLaw_eq]
  rw [hfun] at hc
  exact hc.intervalIntegrable _ _

lemma eventually_gaussian_tail_on_linearBand (gamma : ℝ) (hgamma : 0 < gamma) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (sigma t : ℝ), 0 < sigma →
        linearBandEnd n sigma gamma ≤ |t| →
        ‖GaussianQuadratic.standardNormalChar (sigma * t)‖ ≤
          (n : ℝ) ^ (-5 : ℝ) := by
  have hdecay := QuadraticCancellation.eventually_exp_neg_const_rpow_le_rpow
    (1 / 2) (4 * gamma) 5 (by norm_num) (by positivity) (by norm_num)
  filter_upwards [hdecay, Filter.eventually_ge_atTop 1] with n hdecayN hn
  intro sigma t hsigma ht
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hbase : (n : ℝ) ^ (2 * gamma) ≤ sigma * |t| := by
    have hbase' : (n : ℝ) ^ (2 * gamma) ≤ |t| * sigma :=
      (div_le_iff₀ hsigma).mp (by simpa only [linearBandEnd] using ht)
    simpa only [mul_comm] using hbase'
  have habsmul : |sigma * t| = sigma * |t| := by
    rw [abs_mul, abs_of_pos hsigma]
  have hsquare : (n : ℝ) ^ (4 * gamma) ≤ (sigma * t) ^ 2 := by
    have hsq := mul_self_le_mul_self (Real.rpow_nonneg hnpos.le (2 * gamma))
      (by simpa only [habsmul] using hbase)
    rw [← Real.rpow_add hnpos] at hsq
    calc
      (n : ℝ) ^ (4 * gamma) = (n : ℝ) ^ (2 * gamma + 2 * gamma) := by
        congr 1
        ring
      _ ≤ (sigma * |t|) * (sigma * |t|) := hsq
      _ = (sigma * t) ^ 2 := by
        rw [← habsmul, ← pow_two, sq_abs]
  rw [GaussianQuadratic.norm_standardNormalChar]
  calc
    Real.exp (-(sigma * t) ^ 2 / 2) ≤
        Real.exp (-(1 / 2) * (n : ℝ) ^ (4 * gamma)) := by
      rw [Real.exp_le_exp]
      nlinarith
    _ ≤ (n : ℝ) ^ (-5 : ℝ) := hdecayN

/-- The graph-specific hypotheses for the unstructured Fourier argument,
assembled from Lemmas 7.1, 7.2, and 8.1. -/
theorem eventually_frequencyBands_unstructured_of_slice
    (C H nu : ℝ) (hC : 0 < C) (hH : 0 ≤ H) (hnu : 0 < nu)
    (hslice : ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        RamseyFree C G →
        ∀ (e₀ : ℝ) (coeff : Fin n → ℝ) (t : ℝ),
          (n : ℝ) ^ (-1 + unstructuredGamma / 9) ≤ |t| → |t| ≤ nu →
          ‖GraphQuadratic.centeredGraphCharacteristic G e₀ coeff t‖ ≤
            2 * (n : ℝ) ^ (-5 : ℝ)) :
    let gamma := unstructuredGamma
    let L : ℝ := (Nat.ceil (100 / gamma) : ℕ)
    ∃ a alpha scaleUpper cLinear cTail : ℝ,
      0 < a ∧ 0 < alpha ∧ 0 < scaleUpper ∧
      0 ≤ cLinear ∧ 0 ≤ cTail ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
          (e₀ : ℝ) (c : Fin n → ℝ),
          RamseyFree C G →
          (∀ i, 0 ≤ c i ∧ c i ≤ H * n) →
          BooleanSlices.scale n (1 / 2) ≤
            RLCD.regularizedLCD L gamma
              (GraphQuadratic.graphEffectiveLinear G c) →
          let sigma := GraphQuadratic.graphPerturbedSigma G e₀ c
          FrequencyBandHypotheses
              (GraphQuadratic.centeredGraphCharacteristic G e₀ c)
              (fun t ↦ GaussianQuadratic.standardNormalChar (sigma * t))
              n sigma gamma alpha nu scaleUpper cLinear cTail ∧
            (a / 2) * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ sigma := by
  dsimp only
  let gamma : ℝ := unstructuredGamma
  let L : ℝ := (Nat.ceil (100 / gamma) : ℕ)
  have hgamma : 0 < gamma := by exact unstructuredGamma_pos
  have hgammaUpper : gamma < 1 / 4 := by exact unstructuredGamma_lt_quarter
  obtain ⟨a, ha, Ndensity, hdensity⟩ :=
    AKSGraph.ramseyFree_eventually_whole_density_lower C hC
  obtain ⟨alpha, c72, halpha, hc72, h72⟩ :=
    ksssLemma72_unstructuredBand C H gamma hC hH hgamma hgammaUpper
  let scaleUpper : ℝ := max 1 H
  let cLinear : ℝ := 5400 / a ^ 4 + 1 / (2 * a) + 1 / (8 * a ^ 2)
  let cTail : ℝ := max c72 2
  have hscaleUpper : 0 < scaleUpper := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hcLinear : 0 ≤ cLinear := by dsimp only [cLinear]; positivity
  have hcTail : 0 ≤ cTail := hc72.trans (le_max_left _ _)
  have hlarge := BooleanSlices.eventually_const_le_scale
    (H / 2 + 1 / 4) (1 / 10) (by norm_num)
  have hoverlap := BooleanSlices.eventually_const_le_scale
    (scaleUpper / alpha) (gamma / 72) (by positivity)
  have hlinearGap := QuadraticCancellation.eventually_const_mul_rpow_le_rpow
    (1 / alpha) (2 * gamma) (1 / 2 + gamma / 8)
    (by positivity) (by
      dsimp only [gamma, unstructuredGamma]
      norm_num)
  have hcutoffGap := QuadraticCancellation.eventually_const_mul_rpow_le_rpow
    (2 * alpha / (a * nu)) (-1 + gamma / 8) 0
    (by positivity) (by
      dsimp only [gamma, unstructuredGamma]
      norm_num)
  have hgaussian := eventually_gaussian_tail_on_linearBand gamma hgamma
  refine ⟨a, alpha, scaleUpper, cLinear, cTail, ha, halpha,
    hscaleUpper, hcLinear, hcTail, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 2,
    Filter.eventually_ge_atTop Ndensity,
    hslice, h72, hlarge, hoverlap,
    hlinearGap, hcutoffGap, hgaussian]
    with n hn hdensityN hsliceN h72N hlargeN hoverlapN
      hlinearGapN hcutoffGapN hgaussianN
  intro G _instAdj e₀ c hG hc hLCD
  let : DecidableRel G.Adj := fun _ _ ↦ Classical.propDecidable _
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnOne : 1 ≤ n := hnpos
  have hedge : a * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ) := by
    have hd := hdensity n hdensityN G hG
    simpa [AKSGraph.edgeCount] using hd
  have hcNonneg : ∀ i, 0 ≤ c i := fun i ↦ (hc i).1
  have hcUpper : ∀ i, c i ≤ H * n := fun i ↦ (hc i).2
  have hcAbs : ∀ i, |c i| ≤ scaleUpper * n := by
    intro i
    rw [abs_of_nonneg (hcNonneg i)]
    exact (hcUpper i).trans (mul_le_mul_of_nonneg_right
      (le_max_right 1 H) (by positivity))
  let sigma := GraphQuadratic.graphPerturbedSigma G e₀ c
  have hsigmaLower : (a / 2) * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ sigma := by
    dsimp only [sigma]
    exact GraphQuadratic.graphPerturbedSigma_lower G e₀ c hnpos ha.le
      hcNonneg hedge
  have hsigmaUpper : sigma ≤ scaleUpper * (n : ℝ) ^ ((3 : ℝ) / 2) := by
    dsimp only [sigma]
    exact GraphQuadratic.graphPerturbedSigma_upper G e₀ c scaleUpper
      (le_max_left _ _) hcAbs
  have hsigma : 0 < sigma := by
    dsimp only [sigma]
    exact GraphQuadratic.graphPerturbedSigma_pos G e₀ c hnpos ha hcNonneg hedge
  have hlinearNumerator : (n : ℝ) ^ (2 * gamma) ≤
      alpha * (n : ℝ) ^ (1 / 2 + gamma / 8) := by
    calc
      (n : ℝ) ^ (2 * gamma) =
          alpha * ((1 / alpha) * (n : ℝ) ^ (2 * gamma)) := by
        field_simp [halpha.ne']
      _ ≤ alpha * (n : ℝ) ^ (1 / 2 + gamma / 8) :=
        mul_le_mul_of_nonneg_left hlinearGapN halpha.le
  have hlinearLcd : linearBandEnd n sigma gamma ≤
      lcdBandEnd n sigma gamma alpha := by
    unfold linearBandEnd lcdBandEnd
    exact div_le_div_of_nonneg_right hlinearNumerator hsigma.le
  have hlcdCutoff : lcdBandEnd n sigma gamma alpha ≤ nu := by
    have hden : 0 < (a / 2) * (n : ℝ) ^ ((3 : ℝ) / 2) := by positivity
    have hfirst : alpha * (n : ℝ) ^ (1 / 2 + gamma / 8) / sigma ≤
        alpha * (n : ℝ) ^ (1 / 2 + gamma / 8) /
          ((a / 2) * (n : ℝ) ^ ((3 : ℝ) / 2)) := by
      apply div_le_div_of_nonneg_left (by positivity) hden hsigmaLower
    have hnormalize :
        alpha * (n : ℝ) ^ (1 / 2 + gamma / 8) /
            ((a / 2) * (n : ℝ) ^ ((3 : ℝ) / 2)) =
          (2 * alpha / a) * (n : ℝ) ^ (-1 + gamma / 8) := by
      rw [show (-1 + gamma / 8) =
          (1 / 2 + gamma / 8) - (3 / 2 : ℝ) by ring,
        Real.rpow_sub hnR]
      field_simp [ha.ne']
    have hgap : (2 * alpha / a) * (n : ℝ) ^ (-1 + gamma / 8) ≤ nu := by
      have hscaled := mul_le_mul_of_nonneg_left hcutoffGapN hnu.le
      have hnzero : (n : ℝ) ^ (0 : ℝ) = 1 := by rw [Real.rpow_zero]
      rw [hnzero] at hscaled
      calc
        (2 * alpha / a) * (n : ℝ) ^ (-1 + gamma / 8) =
            nu * ((2 * alpha / (a * nu)) *
              (n : ℝ) ^ (-1 + gamma / 8)) := by
          field_simp [ha.ne', hnu.ne']
        _ ≤ nu * 1 := hscaled
        _ = nu := mul_one _
    exact hfirst.trans (hnormalize.trans_le hgap)
  refine ⟨?_, hsigmaLower⟩
  refine
    { one_lt_n := by exact_mod_cast (show 1 < n by omega)
      sigma_pos := hsigma
      gamma_pos := hgamma
      alpha_pos := halpha
      cutoff_pos := hnu
      scaleUpper_pos := hscaleUpper
      cLinear_nonneg := hcLinear
      cTail_nonneg := hcTail
      sigma_upper := hsigmaUpper
      overlap_growth := hoverlapN
      linear_le_lcd := hlinearLcd
      lcd_le_cutoff := hlcdCutoff
      error_intervalIntegrable :=
        graphGaussianError_intervalIntegrable G e₀ c sigma (-nu) nu
      linear_cancellation := ?_
      lcd_cancellation := ?_
      slice_cancellation := ?_
      gaussian_tail := ?_ }
  · intro t ht
    have hlin := GraphQuadratic.ksssLemma71_linearBand_explicit
      G e₀ c a H gamma hnOne ha hcNonneg hcUpper hedge hlargeN
      (by
        dsimp only [gamma, unstructuredGamma]
        norm_num) t (by
          change |t| ≤ BooleanSlices.scale n (2 * gamma) / sigma at ht
          exact ht)
    simpa only [sigma, cLinear,
      GraphQuadratic.matchingGraphGaussianCharacteristic] using hlin
  · intro t htLower htUpper
    have hraw := h72N G e₀ c hG hc hLCD t
      (by simpa only [sigma] using htLower)
      (by simpa only [sigma] using htUpper)
    exact hraw.trans (mul_le_mul_of_nonneg_right
      (le_max_left c72 2) (Real.rpow_nonneg hnR.le _))
  · intro t htLower htUpper
    have hs := hsliceN G hG e₀ c t
      (by simpa only [sliceBandStart, gamma] using htLower) htUpper
    exact hs.trans (mul_le_mul_of_nonneg_right
      (le_max_right c72 2) (Real.rpow_nonneg hnR.le _))
  · intro t htLower htUpper
    have hg := hgaussianN sigma t hsigma htLower
    exact hg.trans (by
      have htwo : (1 : ℝ) ≤ cTail :=
        (by norm_num : (1 : ℝ) ≤ 2).trans (le_max_right c72 2)
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hnR.le _))

/-- The quadratic cutoff is chosen before the coefficient bound.  This
quantifier order is what makes the eventual window radius independent of
the perturbation bound in `KSSSBoundedWindowFin`. -/
theorem exists_cutoff_eventually_frequencyBands_unstructured
    (C : ℝ) (hC : 0 < C) :
    ∃ nu : ℝ, 0 < nu ∧ ∀ H : ℝ, 0 ≤ H →
      let gamma := unstructuredGamma
      let L : ℝ := (Nat.ceil (100 / gamma) : ℕ)
      ∃ a alpha scaleUpper cLinear cTail : ℝ,
        0 < a ∧ 0 < alpha ∧ 0 < scaleUpper ∧
        0 ≤ cLinear ∧ 0 ≤ cTail ∧
        ∀ᶠ n : ℕ in Filter.atTop,
          ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
            (e₀ : ℝ) (c : Fin n → ℝ),
            RamseyFree C G →
            (∀ i, 0 ≤ c i ∧ c i ≤ H * n) →
            BooleanSlices.scale n (1 / 2) ≤
              RLCD.regularizedLCD L gamma
                (GraphQuadratic.graphEffectiveLinear G c) →
            let sigma := GraphQuadratic.graphPerturbedSigma G e₀ c
            FrequencyBandHypotheses
                (GraphQuadratic.centeredGraphCharacteristic G e₀ c)
                (fun t ↦ GaussianQuadratic.standardNormalChar (sigma * t))
                n sigma gamma alpha nu scaleUpper cLinear cTail ∧
              (a / 2) * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ sigma := by
  obtain ⟨nu, hnu, Nslice, hslice⟩ :=
    ksssLemma81_centeredGraphCharacteristic C (unstructuredGamma / 9) hC
      (div_pos unstructuredGamma_pos (by norm_num)) (by
        dsimp only [unstructuredGamma]
        norm_num)
  have hsliceEventually : ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        RamseyFree C G →
        ∀ (e₀ : ℝ) (coeff : Fin n → ℝ) (t : ℝ),
          (n : ℝ) ^ (-1 + unstructuredGamma / 9) ≤ |t| → |t| ≤ nu →
          ‖GraphQuadratic.centeredGraphCharacteristic G e₀ coeff t‖ ≤
            2 * (n : ℝ) ^ (-5 : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop Nslice] with n hn
    exact hslice n hn
  refine ⟨nu, hnu, ?_⟩
  intro H hH
  exact eventually_frequencyBands_unstructured_of_slice
    C H nu hC hH hnu hsliceEventually

lemma eventually_sigma_mul_band_bound_le
    (gamma scaleUpper A D eta : ℝ)
    (hscaleUpper : 0 ≤ scaleUpper) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (heta : 0 < eta) (hexponent : 4 * gamma - 1 / 2 < 0) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ sigma : ℝ, 0 ≤ sigma →
        sigma ≤ scaleUpper * (n : ℝ) ^ ((3 : ℝ) / 2) →
        sigma * (A * (n : ℝ) ^ (4 * gamma - 2) +
          D * (n : ℝ) ^ (-5 : ℝ)) ≤ eta := by
  have hfirst := QuadraticCancellation.eventually_const_mul_rpow_le_rpow
    (2 * scaleUpper * A / eta) (4 * gamma - 1 / 2) 0
    (by positivity) hexponent
  have hsecond := QuadraticCancellation.eventually_const_mul_rpow_le_rpow
    (2 * scaleUpper * D / eta) (-(7 : ℝ) / 2) 0
    (by positivity) (by norm_num)
  filter_upwards [hfirst, hsecond, Filter.eventually_ge_atTop 1]
    with n hfirstN hsecondN hn
  intro sigma hsigma hsigmaUpper
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have heta2 : 0 ≤ eta / 2 := by positivity
  have hfirstN' : scaleUpper * A *
      (n : ℝ) ^ (4 * gamma - 1 / 2) ≤ eta / 2 := by
    have hscaled := mul_le_mul_of_nonneg_left hfirstN heta2
    rw [Real.rpow_zero, mul_one] at hscaled
    calc
      scaleUpper * A * (n : ℝ) ^ (4 * gamma - 1 / 2) =
          (eta / 2) * ((2 * scaleUpper * A / eta) *
            (n : ℝ) ^ (4 * gamma - 1 / 2)) := by
        field_simp [heta.ne']
      _ ≤ (eta / 2) * 1 := by simpa only [mul_one] using hscaled
      _ = eta / 2 := mul_one _
  have hsecondN' : scaleUpper * D * (n : ℝ) ^ (-(7 : ℝ) / 2) ≤
      eta / 2 := by
    have hscaled := mul_le_mul_of_nonneg_left hsecondN heta2
    rw [Real.rpow_zero, mul_one] at hscaled
    calc
      scaleUpper * D * (n : ℝ) ^ (-(7 : ℝ) / 2) =
          (eta / 2) * ((2 * scaleUpper * D / eta) *
            (n : ℝ) ^ (-(7 : ℝ) / 2)) := by
        field_simp [heta.ne']
      _ ≤ (eta / 2) * 1 := by simpa only [mul_one] using hscaled
      _ = eta / 2 := mul_one _
  have hbracket : 0 ≤ A * (n : ℝ) ^ (4 * gamma - 2) +
      D * (n : ℝ) ^ (-5 : ℝ) := by positivity
  calc
    sigma * (A * (n : ℝ) ^ (4 * gamma - 2) +
        D * (n : ℝ) ^ (-5 : ℝ)) ≤
        (scaleUpper * (n : ℝ) ^ ((3 : ℝ) / 2)) *
          (A * (n : ℝ) ^ (4 * gamma - 2) +
            D * (n : ℝ) ^ (-5 : ℝ)) :=
      mul_le_mul_of_nonneg_right hsigmaUpper hbracket
    _ = scaleUpper * A * (n : ℝ) ^ (4 * gamma - 1 / 2) +
        scaleUpper * D * (n : ℝ) ^ (-(7 : ℝ) / 2) := by
      rw [mul_add]
      congr 1
      · calc
          scaleUpper * (n : ℝ) ^ ((3 : ℝ) / 2) *
              (A * (n : ℝ) ^ (4 * gamma - 2)) =
              scaleUpper * A * ((n : ℝ) ^ ((3 : ℝ) / 2) *
                (n : ℝ) ^ (4 * gamma - 2)) := by ring
          _ = scaleUpper * A * (n : ℝ) ^
              ((3 : ℝ) / 2 + (4 * gamma - 2)) := by
            rw [← Real.rpow_add hnR]
          _ = scaleUpper * A * (n : ℝ) ^ (4 * gamma - 1 / 2) := by
            congr 2
            ring
      · calc
          scaleUpper * (n : ℝ) ^ ((3 : ℝ) / 2) *
              (D * (n : ℝ) ^ (-5 : ℝ)) =
              scaleUpper * D * ((n : ℝ) ^ ((3 : ℝ) / 2) *
                (n : ℝ) ^ (-5 : ℝ)) := by ring
          _ = scaleUpper * D * (n : ℝ) ^ ((3 : ℝ) / 2 + (-5 : ℝ)) := by
            rw [← Real.rpow_add hnR]
          _ = scaleUpper * D * (n : ℝ) ^ (-(7 : ℝ) / 2) := by
            congr 2
            ring
    _ ≤ eta / 2 + eta / 2 := add_le_add hfirstN' hsecondN'
    _ = eta := by ring

end BoundedWindowAnalytic
end Erdos88
