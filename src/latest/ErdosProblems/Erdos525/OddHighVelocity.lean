import ErdosProblems.Erdos525.OddQuantitative
import ErdosProblems.Erdos525.HighVelocity

open scoped BigOperators ENNReal NNReal Topology Real ComplexConjugate
open MeasureTheory Filter Set

namespace Erdos525

open Classical Finset

namespace Odd

lemma phaseBoundaryGaussianTail_one_tendsto_zero :
    Tendsto (phaseBoundaryGaussianTail 1) atTop (𝓝 0) := by
  have hscaled := scaled_phaseBoundaryGaussianTail_tendsto_zero 1
  refine squeeze_zero'
    (f := phaseBoundaryGaussianTail 1)
    (g := fun n : ℕ ↦ (localMeshSize n : ℝ) *
      phaseBoundaryGaussianTail 1 n)
    (Eventually.of_forall fun n ↦ by
      exact phaseBoundaryGaussianTail_nonneg 1 n)
    ?_ (by simpa only [pow_one] using hscaled)
  exact Eventually.of_forall fun n ↦ by
    have hone : (1 : ℝ) ≤ localMeshSize n := by
      exact_mod_cast localMeshSize_pos n
    have hnonneg := phaseBoundaryGaussianTail_nonneg 1 n
    nlinarith

theorem eventually_uniform_scaled_highVelocityPhaseProbability_upper
    (u V : ℝ) (hu : 0 ≤ u) (hV : 0 < V) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℝ,
      IsSmooth n (rigiditySmoothScale n) t →
      IsSpread n (rigiditySmoothScale n) (fun _ : Fin 1 ↦ t) →
      (localMeshSize n : ℝ) *
          uniformProbability (fun e : SignVector (2 * n + 1) ↦
            normalizedPhaseEuclideanWalk n e (fun _ : Fin 1 ↦ t) ∈
              truncatedPhaseRegion (m := 1) n (u + 1)
                (2 * localMeshHalfWidth n) (V / 2)
                (2 * growingVelocityCutoff n)) ≤
        (72 / Real.pi) * (u + 2) * blockVelocityTailMass (V / 4) +
          648 * Real.pi ^ 2 * (u + 2) * growingVelocityCutoff n ^ 3 *
            quantitativePhaseDensityError n := by
  have htail := phaseBoundaryGaussianTail_one_tendsto_zero.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [Nat.eventually_pos,
      eventually_highVelocity_outer_bounds u V hu hV,
      htail, eventually_uniform_phaseSmoothedDensity_le_explicit]
    with n hn houterBounds htailN hdensity
  intro t hsmooth hspread
  rcases houterBounds with
    ⟨hOuterHeight0, hOuterHeight, hOuterWidth0, hOuterWidth,
      hOuterLower, hOuterUpper⟩
  let target := truncatedPhaseRegion (m := 1) n (u + 1)
    (2 * localMeshHalfWidth n) (V / 2) (2 * growingVelocityCutoff n)
  let expanded := truncatedPhaseRegion (m := 1) n (u + 2)
    (3 * localMeshHalfWidth n) (V / 4) (3 * growingVelocityCutoff n)
  let p := uniformProbability (fun e : SignVector (2 * n + 1) ↦
    normalizedPhaseEuclideanWalk n e (fun _ : Fin 1 ↦ t) ∈ target)
  let err := quantitativePhaseDensityError n
  have hhalf : 0 ≤ 2 * localMeshHalfWidth n := by
    unfold localMeshHalfWidth
    positivity
  have hrLower : phaseBoundaryRadius n < V / 2 := by linarith
  have hthick : Metric.thickening (phaseBoundaryRadius n) target ⊆ expanded := by
    have hfirst := thickening_truncatedPhaseRegion_subset_outer
      1 n hn (u + 1) (2 * localMeshHalfWidth n) (V / 2)
        (2 * growingVelocityCutoff n) (phaseBoundaryRadius n)
        (by linarith) hhalf (phaseBoundaryRadius_nonneg n) hrLower
    have hsecond := truncatedPhaseRegion_mono 1 n hn
      hOuterHeight.le hOuterWidth.le hOuterLower.le hOuterUpper.le
    exact hfirst.trans hsecond
  have hsigma : 0 < prefixScale n * localCLTSmoothingScaleTest n :=
    mul_pos (prefixScale_pos n) (by
      unfold localCLTSmoothingScaleTest
      exact rigidityPower_pos hn _)
  have hsandwich := uniformProbability_mul_gaussianLower_le_integral_thickening
    n (fun _ : Fin 1 ↦ t)
      (prefixScale n * localCLTSmoothingScaleTest n)
      (phaseBoundaryRadius n) hsigma (phaseBoundaryRadius_nonneg n) target
  have hmono :
      (∫ y in Metric.thickening (phaseBoundaryRadius n) target,
          phaseSmoothedDensity n (fun _ : Fin 1 ↦ t)
            (prefixScale n * localCLTSmoothingScaleTest n) y) ≤
        ∫ y in expanded,
          phaseSmoothedDensity n (fun _ : Fin 1 ↦ t)
            (prefixScale n * localCLTSmoothingScaleTest n) y := by
    exact setIntegral_mono_set
      (integrable_phaseSmoothedDensity 1 n (fun _ : Fin 1 ↦ t)
        (prefixScale n * localCLTSmoothingScaleTest n) hsigma).integrableOn
      (Eventually.of_forall fun y ↦ phaseSmoothedDensity_nonneg 1 n
        (fun _ : Fin 1 ↦ t)
          (prefixScale n * localCLTSmoothingScaleTest n) y)
      (Eventually.of_forall hthick)
  have hheight : 0 ≤ u + 2 := by linarith
  have hwidth : 0 ≤ 3 * localMeshHalfWidth n := by
    unfold localMeshHalfWidth
    positivity
  have hlower : 0 < V / 4 := by positivity
  have hfinite : volume expanded ≠ ⊤ := by
    dsimp [expanded]
    exact volume_truncatedPhaseRegion_ne_top 1 n (by omega) hn
      (u + 2) (3 * localMeshHalfWidth n) (V / 4)
        (3 * growingVelocityCutoff n) hheight hwidth hlower
  have hclose : ∀ y : PhaseEuclidean 1,
      |phaseSmoothedDensity n (fun _ : Fin 1 ↦ t)
          (prefixScale n * localCLTSmoothingScaleTest n) y -
        phaseLimitingDensity y| ≤ err := by
    intro y
    exact hdensity t y hsmooth hspread
  have herror := abs_setIntegral_phaseSmoothedDensity_sub_limiting_le
    1 n (by omega) (fun _ : Fin 1 ↦ t)
      (prefixScale n * localCLTSmoothingScaleTest n)
      err expanded hfinite (quantitativePhaseDensityError_nonneg n) hclose
  have hsmoothUpper :
      (∫ y in expanded, phaseSmoothedDensity n (fun _ : Fin 1 ↦ t)
          (prefixScale n * localCLTSmoothingScaleTest n) y) ≤
        (∫ y in expanded, phaseLimitingDensity y) +
          err * volume.real expanded := by
    linarith [le_abs_self
      ((∫ y in expanded, phaseSmoothedDensity n (fun _ : Fin 1 ↦ t)
          (prefixScale n * localCLTSmoothingScaleTest n) y) -
        ∫ y in expanded, phaseLimitingDensity y)]
  have hp : 0 ≤ p := uniformProbability_nonneg _
  have hpHalf : p * (1 / 2) ≤
      ∫ y in expanded, phaseSmoothedDensity n (fun _ : Fin 1 ↦ t)
        (prefixScale n * localCLTSmoothingScaleTest n) y := by
    have hfactor : (1 / 2 : ℝ) ≤ 1 - phaseBoundaryGaussianTail 1 n := by
      linarith
    calc
      p * (1 / 2) ≤ p * (1 - phaseBoundaryGaussianTail 1 n) :=
        mul_le_mul_of_nonneg_left hfactor hp
      _ ≤ (∫ y in Metric.thickening (phaseBoundaryRadius n) target,
          phaseSmoothedDensity n (fun _ : Fin 1 ↦ t)
            (prefixScale n * localCLTSmoothingScaleTest n) y) := by
        simpa only [p, target, phaseBoundaryGaussianTail, one_mul] using hsandwich
      _ ≤ _ := hmono
  have hpUpper : p ≤ 2 *
      ((∫ y in expanded, phaseLimitingDensity y) +
        err * volume.real expanded) := by
    linarith [hpHalf, hsmoothUpper]
  have hM : 0 ≤ (localMeshSize n : ℝ) := by positivity
  have hlim := scaled_highVelocity_expanded_limiting_upper n hn u V hu hV
  have hvol := scaled_highVelocity_expanded_volume_upper n hn u V hu hV
  have herr : 0 ≤ err := quantitativePhaseDensityError_nonneg n
  have hscaled := mul_le_mul_of_nonneg_left hpUpper hM
  change (localMeshSize n : ℝ) * p ≤ _
  calc
    (localMeshSize n : ℝ) * p ≤
        2 * ((localMeshSize n : ℝ) *
          (∫ y in expanded, phaseLimitingDensity y)) +
        2 * err * ((localMeshSize n : ℝ) * volume.real expanded) := by
      calc
        _ ≤ (localMeshSize n : ℝ) *
            (2 * ((∫ y in expanded, phaseLimitingDensity y) +
              err * volume.real expanded)) := hscaled
        _ = _ := by ring
    _ ≤ 2 * ((36 / Real.pi) * (u + 2) * blockVelocityTailMass (V / 4)) +
        2 * err *
          (324 * Real.pi ^ 2 * (u + 2) * growingVelocityCutoff n ^ 3) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hlim (by norm_num))
        (mul_le_mul_of_nonneg_left hvol (mul_nonneg (by norm_num) herr))
    _ = (72 / Real.pi) * (u + 2) * blockVelocityTailMass (V / 4) +
          648 * Real.pi ^ 2 * (u + 2) * growingVelocityCutoff n ^ 3 *
            quantitativePhaseDensityError n := by
      dsimp [err]
      ring

lemma sqrt_centeredCount_mul_halfWidth_mul_growingCutoff_tendsto_zero :
    Tendsto (fun n : ℕ ↦ Real.sqrt (2 * n + 1 : ℝ) *
      localMeshHalfWidth n * growingVelocityCutoff n) atTop (𝓝 0) := by
  have hpow := (tendsto_rigidityPower_neg_zero
    (show (0 : ℝ) < 63 / 128 by norm_num)).const_mul (2 * Real.pi)
  have hpow' : Tendsto (fun n : ℕ ↦
      2 * Real.pi * rigidityPower n (-(63 / 128))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hpow
  refine squeeze_zero'
    (Eventually.of_forall fun n ↦ by
      exact mul_nonneg
        (mul_nonneg (Real.sqrt_nonneg _)
          (by unfold localMeshHalfWidth; positivity))
        (growingVelocityCutoff_nonneg n)) ?_ hpow'
  filter_upwards [Nat.eventually_pos] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrtN : Real.sqrt (n : ℝ) = rigidityPower n (1 / 2) := by
    unfold rigidityPower
    rw [Real.sqrt_eq_rpow]
  have hsqrtCount : Real.sqrt (2 * n + 1 : ℝ) ≤ 2 * Real.sqrt n := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · rw [mul_pow, Real.sq_sqrt hnR.le]
      push_cast
      nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast hn]
  have hmesh := n_mul_localMeshHalfWidth_le_pi n
  have hhalf : localMeshHalfWidth n ≤ Real.pi / n := by
    apply (le_div_iff₀ hnR).2
    simpa [mul_comm] using hmesh
  have hcut0 : 0 ≤ growingVelocityCutoff n := growingVelocityCutoff_nonneg n
  have hsqrt0 : 0 ≤ Real.sqrt (2 * n + 1 : ℝ) := Real.sqrt_nonneg _
  have hhalf0 : 0 ≤ localMeshHalfWidth n := by
    unfold localMeshHalfWidth
    positivity
  calc
    Real.sqrt (2 * n + 1 : ℝ) * localMeshHalfWidth n *
        growingVelocityCutoff n ≤
      (2 * Real.sqrt n) * (Real.pi / n) * growingVelocityCutoff n := by
        gcongr
    _ = 2 * Real.pi * rigidityPower n (-(63 / 128)) := by
      unfold growingVelocityCutoff
      rw [hsqrtN]
      unfold rigidityPower
      rw [show Real.pi / (n : ℝ) = Real.pi * (n : ℝ)⁻¹ by
        rw [div_eq_mul_inv],
        show (n : ℝ)⁻¹ = (n : ℝ) ^ (-1 : ℝ) by
          rw [Real.rpow_neg_one]]
      calc
        2 * (n : ℝ) ^ (1 / 2 : ℝ) *
            (Real.pi * (n : ℝ) ^ (-1 : ℝ)) *
            (n : ℝ) ^ (1 / 128 : ℝ) =
          2 * Real.pi * (((n : ℝ) ^ (1 / 2 : ℝ) *
            (n : ℝ) ^ (1 / 128 : ℝ)) * (n : ℝ) ^ (-1 : ℝ)) := by ring
        _ = 2 * Real.pi * (n : ℝ) ^ (-(63 / 128 : ℝ)) := by
          rw [← Real.rpow_add hnR, ← Real.rpow_add hnR]
          congr 2
          norm_num

lemma globalAccelerationBound_mul_halfWidth_mul_growingCutoff_tendsto_zero :
    Tendsto (fun n : ℕ ↦ globalAccelerationBound n *
      localMeshHalfWidth n * growingVelocityCutoff n) atTop (𝓝 0) := by
  have hextra := extraAccelerationBound_tendsto_zero.mul
    localMeshHalfWidth_mul_growingVelocityCutoff_tendsto_zero
  simp only [zero_mul] at hextra
  have hsum := sqrt_centeredCount_mul_halfWidth_mul_growingCutoff_tendsto_zero.add
    hextra
  convert hsum using 1
  · funext n
    unfold globalAccelerationBound
    ring
  · norm_num

lemma highVelocity_fixedLower_minimumTransferWidthFactor_tendsto_one
    (u V : ℝ) (hV : 0 < V) :
    Tendsto (fun n : ℕ ↦ minimumTransferWidthFactor n u (V / 2)
      (2 * growingVelocityCutoff n)) atTop (𝓝 1) := by
  have hfirst := globalAccelerationBound_div_tendsto_zero.const_mul u
  have hsecond :=
    globalAccelerationBound_mul_halfWidth_mul_growingCutoff_tendsto_zero.const_mul 2
  have hnum : Tendsto (fun n : ℕ ↦
      u * (globalAccelerationBound n / (n : ℝ)) +
        2 * (globalAccelerationBound n * localMeshHalfWidth n *
          growingVelocityCutoff n)) atTop (𝓝 0) := by
    simpa using hfirst.add hsecond
  have hdiv := hnum.div_const ((V / 2) ^ 2)
  have hone :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).add hdiv
  have hone' : Tendsto (fun n : ℕ ↦
      1 + (u * (globalAccelerationBound n / (n : ℝ)) +
        2 * (globalAccelerationBound n * localMeshHalfWidth n *
          growingVelocityCutoff n)) / (V / 2) ^ 2) atTop (𝓝 1) := by
    simpa using hone
  apply hone'.congr'
  filter_upwards [Nat.eventually_pos] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hh0 : localMeshHalfWidth n ≠ 0 := by
    unfold localMeshHalfWidth
    exact div_ne_zero (mul_ne_zero Real.pi_ne_zero (by exact_mod_cast hn.ne'))
      (by exact_mod_cast (localMeshSize_pos n).ne')
  have hV0 : V / 2 ≠ 0 := (half_pos hV).ne'
  unfold minimumTransferWidthFactor minimumAffineOffsetError
  field_simp [hn0, hh0, hV0]

noncomputable def extraVelocity (n : ℕ) (b : Bool) (t : ℝ) : ℂ :=
  (sign b / Real.sqrt (2 * n + 2 : ℝ) : ℝ) *
    ((((n + 1 : ℕ) : ℝ) / n : ℂ) * Complex.I) *
      Complex.exp ((((n + 1 : ℕ) : ℝ) * (t / n) : ℂ) * Complex.I)

lemma norm_extraVelocity_le_four_div_sqrt_nat
    (n : ℕ) (hn : 0 < n) (b : Bool) (t : ℝ) :
    ‖extraVelocity n b t‖ ≤ 4 / Real.sqrt n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrtN : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hsqrtCount : Real.sqrt (n : ℝ) ≤ Real.sqrt (2 * n + 2 : ℝ) := by
    apply Real.sqrt_le_sqrt
    push_cast
    nlinarith
  have hratio : ((n + 1 : ℕ) : ℝ) / n ≤ 2 := by
    rw [div_le_iff₀ hnR]
    push_cast
    nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast hn]
  unfold extraVelocity
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, Complex.norm_exp]
  simp only [mul_one, norm_div, Complex.norm_real, Real.norm_eq_abs]
  rw [Complex.norm_natCast]
  rw [show (((((n + 1 : ℕ) : ℝ) * (t / n) : ℂ) * Complex.I).re) = 0 by
    simp [Complex.mul_re]]
  simp only [Real.exp_zero, mul_one]
  rw [abs_div, abs_sign, abs_of_pos (by positivity :
    0 < Real.sqrt (2 * n + 2 : ℝ)), abs_of_nonneg (by positivity :
      0 ≤ ((n + 1 : ℕ) : ℝ))]
  have hinv : 1 / Real.sqrt (2 * n + 2 : ℝ) ≤ 1 / Real.sqrt n :=
    one_div_le_one_div_of_le hsqrtN hsqrtCount
  calc
    1 / Real.sqrt (2 * n + 2 : ℝ) * (((n + 1 : ℕ) : ℝ) / n) ≤
        (1 / Real.sqrt n) * 2 :=
      mul_le_mul hinv hratio (by positivity) (by positivity)
    _ = 2 / Real.sqrt n := by ring
    _ ≤ 4 / Real.sqrt n := by
      gcongr
      norm_num

lemma velocity_appendSign (n : ℕ) (e : SignVector (2 * n))
    (b : Bool) (t : ℝ) :
    velocity n (appendSign n e b) t =
      (prefixScale n : ℂ) * rescaledCenteredVelocity n e t +
        extraVelocity n b t := by
  simp [velocity, extraVelocity]

def HasHighMeshVelocity (n : ℕ) (T : ℝ)
    (e : SignVector (2 * n + 1)) : Prop :=
  ∃ a : Fin (localMeshSize n),
    T ≤ ‖velocity n e (localMeshPoint n a)‖

def HasHighPrefixMeshVelocity (n : ℕ) (T : ℝ)
    (e : SignVector (2 * n + 1)) : Prop :=
  Erdos525.HasHighMeshVelocity n T (initialSegment n e)

lemma uniformProbability_highPrefixMeshVelocity (n : ℕ) (T : ℝ) :
    uniformProbability (HasHighPrefixMeshVelocity n T) =
      uniformProbability (Erdos525.HasHighMeshVelocity n T) := by
  rw [uniformProbability_split]
  simp only [HasHighPrefixMeshVelocity, initialSegment_appendSign]
  ring

lemma eventually_highMeshVelocity_subset_highPrefix :
    ∀ᶠ n : ℕ in atTop, ∀ e : SignVector (2 * n + 1),
      HasHighMeshVelocity n (growingVelocityCutoff n) e →
        HasHighPrefixMeshVelocity n (growingVelocityCutoff n / 2) e := by
  have hsmall : Tendsto (fun n : ℕ ↦
      4 / Real.sqrt n / growingVelocityCutoff n) atTop (𝓝 0) := by
    have h := (tendsto_rigidityPower_neg_zero
      (show (0 : ℝ) < 65 / 128 by norm_num)).const_mul 4
    have h' : Tendsto (fun n : ℕ ↦
        4 * rigidityPower n (-(65 / 128))) atTop (𝓝 0) := by
      simpa only [mul_zero] using h
    refine h'.congr' ?_
    filter_upwards [Nat.eventually_pos] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hsqrt : Real.sqrt (n : ℝ) = rigidityPower n (1 / 2) := by
      unfold rigidityPower
      rw [Real.sqrt_eq_rpow]
    unfold growingVelocityCutoff
    rw [hsqrt]
    unfold rigidityPower
    symm
    simp only [div_eq_mul_inv]
    rw [← Real.rpow_neg hnR.le, ← Real.rpow_neg hnR.le,
      show 4 * (n : ℝ) ^ (-((1 : ℝ) * (2 : ℝ)⁻¹)) *
          (n : ℝ) ^ (-((1 : ℝ) * (128 : ℝ)⁻¹)) =
        4 * ((n : ℝ) ^ (-((1 : ℝ) * (2 : ℝ)⁻¹)) *
          (n : ℝ) ^ (-((1 : ℝ) * (128 : ℝ)⁻¹))) by ring,
      ← Real.rpow_add hnR]
    congr 1
    norm_num
  have hratio := hsmall.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [Nat.eventually_pos, hratio] with n hn hratioN
  intro e hhigh
  rcases hhigh with ⟨site, hsite⟩
  refine ⟨site, ?_⟩
  by_contra hnot
  have hprefix : ‖rescaledCenteredVelocity n (initialSegment n e)
      (localMeshPoint n site)‖ < growingVelocityCutoff n / 2 :=
    lt_of_not_ge hnot
  have hlast := norm_extraVelocity_le_four_div_sqrt_nat n hn
    (lastSign n e) (localMeshPoint n site)
  have hcut : 0 < growingVelocityCutoff n :=
    rigidityPower_pos hn _
  have hsmallLast : 4 / Real.sqrt n < growingVelocityCutoff n / 2 := by
    have h := (div_lt_iff₀ hcut).1 hratioN
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  have hupper : ‖velocity n e (localMeshPoint n site)‖ <
      growingVelocityCutoff n := by
    rw [show e = appendSign n (initialSegment n e) (lastSign n e) by
      exact (appendSign_initialSegment_lastSign n e).symm,
      velocity_appendSign]
    calc
      _ ≤ ‖(prefixScale n : ℂ) *
            rescaledCenteredVelocity n (initialSegment n e)
              (localMeshPoint n site)‖ +
          ‖extraVelocity n (lastSign n e) (localMeshPoint n site)‖ :=
        norm_add_le _ _
      _ ≤ ‖rescaledCenteredVelocity n (initialSegment n e)
            (localMeshPoint n site)‖ + 4 / Real.sqrt n := by
        gcongr
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (prefixScale_pos n)]
        exact mul_le_of_le_one_left (norm_nonneg _) (prefixScale_le_one n)
      _ < growingVelocityCutoff n / 2 + growingVelocityCutoff n / 2 :=
        add_lt_add hprefix hsmallLast
      _ = growingVelocityCutoff n := by ring
  exact (not_lt_of_ge hsite) hupper

lemma highPrefixMeshVelocity_half_upper_tendsto_zero :
    Tendsto (fun n : ℕ ↦ uniformProbability
      (HasHighPrefixMeshVelocity n (growingVelocityCutoff n / 2)))
      atTop (𝓝 0) := by
  let U : ℕ → ℝ := fun n ↦
    (localMeshSize n : ℝ) *
      (4 * Real.exp (-((growingVelocityCutoff n / 2) / 2) ^ 2 / 2))
  have hU : Tendsto U atTop (𝓝 0) := by
    have hcore := (tendsto_rigidityPower_mul_exp_neg_power_test
      2 (1 / 64) (1 / 32) (by norm_num) (by norm_num)).const_mul 8
    refine squeeze_zero' (g := fun n : ℕ ↦
      8 * (rigidityPower n 2 *
        Real.exp (-(1 / 32) * rigidityPower n (1 / 64))))
      (Eventually.of_forall fun n ↦ by dsimp [U]; positivity) ?_
      (by simpa only [mul_zero] using hcore)
    filter_upwards [Nat.eventually_pos] with n hn
    have hsize : (localMeshSize n : ℝ) ≤ 2 * rigidityPower n 2 := by
      simp only [localMeshSize, rigidityPower]
      norm_num
      push_cast
      nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast hn]
    have hcutSq : growingVelocityCutoff n ^ 2 =
        rigidityPower n (1 / 64) := by
      unfold growingVelocityCutoff
      convert rigidityPower_nat_pow hn (1 / 128) 2 using 1 <;> norm_num
    have hexp : -((growingVelocityCutoff n / 2) / 2) ^ 2 / 2 =
        -(1 / 32) * rigidityPower n (1 / 64) := by
      rw [div_pow, div_pow, hcutSq]
      ring
    rw [show U n = (localMeshSize n : ℝ) *
        (4 * Real.exp (-(1 / 32) * rigidityPower n (1 / 64))) by
      dsimp [U]
      rw [hexp]]
    have hnonneg : 0 ≤ 4 * Real.exp
        (-(1 / 32) * rigidityPower n (1 / 64)) := by positivity
    calc
      _ ≤ (2 * rigidityPower n 2) *
          (4 * Real.exp (-(1 / 32) * rigidityPower n (1 / 64))) :=
        mul_le_mul_of_nonneg_right hsize hnonneg
      _ = 8 * (rigidityPower n 2 *
          Real.exp (-(1 / 32) * rigidityPower n (1 / 64))) := by ring
  apply squeeze_zero' (g := U)
    (Eventually.of_forall fun n ↦ uniformProbability_nonneg _)
  · filter_upwards [Nat.eventually_pos] with n hn
    rw [uniformProbability_highPrefixMeshVelocity]
    exact uniformProbability_highMeshVelocity_le n
      (growingVelocityCutoff n / 2) (half_pos (by
        unfold growingVelocityCutoff
        exact rigidityPower_pos hn _))
  · exact hU

theorem uniformProbability_highMeshVelocity_growing_tendsto_zero :
    Tendsto (fun n : ℕ ↦ uniformProbability
      (HasHighMeshVelocity n (growingVelocityCutoff n))) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun n ↦ uniformProbability_nonneg _)
  · filter_upwards [eventually_highMeshVelocity_subset_highPrefix] with n hsub
    apply uniformProbability_mono
    exact hsub
  · exact highPrefixMeshVelocity_half_upper_tendsto_zero

end Odd

end Erdos525
