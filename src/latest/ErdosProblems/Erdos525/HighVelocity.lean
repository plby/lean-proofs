import ErdosProblems.Erdos525.Quantitative

open scoped BigOperators ENNReal NNReal Topology Real ComplexConjugate
open MeasureTheory Filter Set

namespace Erdos525

/-!
## Removing the upper velocity cutoff

We use the slowly growing cutoff `n^(1/128)`.  The explicit local-CLT error
from `Quantitative` is small enough after multiplication by the volume of the
corresponding phase-space region.
-/

noncomputable def highVelocityOuterHeight (n : ℕ) (u V : ℝ) : ℝ :=
  blockOuterHeight n (u + 1) (2 * localMeshHalfWidth n) (V / 2)
    (2 * growingVelocityCutoff n) (phaseBoundaryRadius n)

noncomputable def highVelocityOuterWidth (n : ℕ) (u V : ℝ) : ℝ :=
  blockOuterHalfWidth n (u + 1) (2 * localMeshHalfWidth n) (V / 2)
    (2 * growingVelocityCutoff n) (phaseBoundaryRadius n)

lemma growingVelocityCutoff_div_nat_tendsto_zero :
    Tendsto (fun n : ℕ ↦ growingVelocityCutoff n / (n : ℝ))
      atTop (nhds 0) := by
  have h := tendsto_rigidityPower_neg_zero
    (show (0 : ℝ) < 127 / 128 by norm_num)
  apply h.congr'
  filter_upwards [Nat.eventually_pos] with n hn
  unfold growingVelocityCutoff rigidityPower
  rw [show (-(127 / 128 : ℝ)) = 1 / 128 - 1 by norm_num,
    Real.rpow_sub (by exact_mod_cast hn : (0 : ℝ) < n), Real.rpow_one]

lemma localMeshHalfWidth_mul_growingVelocityCutoff_tendsto_zero :
    Tendsto (fun n : ℕ ↦ localMeshHalfWidth n * growingVelocityCutoff n)
      atTop (nhds 0) := by
  have h := scaled_localMeshHalfWidth_tendsto_pi.mul
    growingVelocityCutoff_div_nat_tendsto_zero
  have h0 : Tendsto (fun n : ℕ ↦
      ((n : ℝ) * localMeshHalfWidth n) *
        (growingVelocityCutoff n / (n : ℝ))) atTop (nhds 0) := by
    simpa using h
  apply h0.congr'
  filter_upwards [Nat.eventually_pos] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

lemma highVelocity_scaled_outerError_tendsto_zero
    (u V : ℝ) (hV : 0 < V) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) *
      blockOuterPerturbationError n (u + 1) (2 * localMeshHalfWidth n)
        (V / 2) (2 * growingVelocityCutoff n) (phaseBoundaryRadius n))
      atTop (nhds 0) := by
  have hr := phaseBoundaryRadius_tendsto_zero
  have hnr := scaled_phaseBoundaryRadius_tendsto_zero
  have hhT := localMeshHalfWidth_mul_growingVelocityCutoff_tendsto_zero
  have huDiv : Tendsto (fun n : ℕ ↦ (u + 1) / (n : ℝ))
      atTop (nhds 0) := by
    have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ))⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa [div_eq_mul_inv] using hinv.const_mul (u + 1)
  have hbase : Tendsto (fun n : ℕ ↦
      (2 * localMeshHalfWidth n) * (2 * growingVelocityCutoff n) +
        (u + 1) / (n : ℝ) + phaseBoundaryRadius n) atTop (nhds 0) := by
    have hfirst : Tendsto (fun n : ℕ ↦
        (2 * localMeshHalfWidth n) * (2 * growingVelocityCutoff n))
        atTop (nhds 0) := by
      convert hhT.const_mul 4 using 1 <;> ring_nf
    simpa using (hfirst.add huDiv).add hr
  have hden : Tendsto (fun n : ℕ ↦ V / 2 - phaseBoundaryRadius n)
      atTop (nhds (V / 2)) := by
    simpa using tendsto_const_nhds.sub hr
  have hcoef : Tendsto (fun n : ℕ ↦
      2 / (V / 2 - phaseBoundaryRadius n)) atTop (nhds (2 / (V / 2))) := by
    exact tendsto_const_nhds.div hden (by positivity)
  have hprod := (hbase.mul hcoef).mul hnr
  have hsum := hnr.add hprod
  simp only [zero_mul, zero_add] at hsum
  apply hsum.congr'
  filter_upwards [] with n
  unfold blockOuterPerturbationError
  ring

lemma highVelocity_outerHeight_tendsto
    (u V : ℝ) (hV : 0 < V) :
    Tendsto (fun n : ℕ ↦ highVelocityOuterHeight n u V)
      atTop (nhds (u + 1)) := by
  have hconst : Tendsto (fun _ : ℕ ↦ u + 1) atTop (nhds (u + 1)) :=
    tendsto_const_nhds
  have h := hconst.add
    (highVelocity_scaled_outerError_tendsto_zero u V hV)
  simpa [highVelocityOuterHeight, blockOuterHeight] using h

lemma highVelocity_outerWidth_relative_tendsto_one
    (u V : ℝ) (hV : 0 < V) :
    Tendsto (fun n : ℕ ↦
      highVelocityOuterWidth n u V / localMeshHalfWidth n)
      atTop (nhds 2) := by
  have hr := phaseBoundaryRadius_tendsto_zero
  have hnr := scaled_phaseBoundaryRadius_tendsto_zero
  have hnh := scaled_localMeshHalfWidth_tendsto_pi
  have hE := highVelocity_scaled_outerError_tendsto_zero u V hV
  have hnum : Tendsto (fun n : ℕ ↦
      (2 * ((n : ℝ) * localMeshHalfWidth n)) * phaseBoundaryRadius n +
        (n : ℝ) * blockOuterPerturbationError n (u + 1)
          (2 * localMeshHalfWidth n) (V / 2)
          (2 * growingVelocityCutoff n) (phaseBoundaryRadius n))
      atTop (nhds 0) := by
    have hfirst := (hnh.const_mul 2).mul hr
    simpa using hfirst.add hE
  have hden : Tendsto (fun n : ℕ ↦
      (V / 2 - phaseBoundaryRadius n) *
        ((n : ℝ) * localMeshHalfWidth n))
      atTop (nhds ((V / 2) * Real.pi)) := by
    simpa using (tendsto_const_nhds.sub hr).mul hnh
  have hquot := hnum.div hden (by positivity : (V / 2) * Real.pi ≠ 0)
  simp only [zero_div] at hquot
  have hconst : Tendsto (fun _ : ℕ ↦ (2 : ℝ)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hadd := hconst.add hquot
  have hadd0 : Tendsto (fun n : ℕ ↦
      2 +
        (2 * ((n : ℝ) * localMeshHalfWidth n) * phaseBoundaryRadius n +
          (n : ℝ) * blockOuterPerturbationError n (u + 1)
            (2 * localMeshHalfWidth n) (V / 2)
            (2 * growingVelocityCutoff n) (phaseBoundaryRadius n)) /
        ((V / 2 - phaseBoundaryRadius n) *
          ((n : ℝ) * localMeshHalfWidth n))) atTop (nhds 2) := by
    simpa using hadd
  apply hadd0.congr'
  filter_upwards [Nat.eventually_pos,
      hr.eventually (Iio_mem_nhds (half_pos hV))] with n hn hrn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hh : localMeshHalfWidth n ≠ 0 := by
    unfold localMeshHalfWidth
    exact (div_pos (mul_pos Real.pi_pos (by exact_mod_cast hn))
      (by exact_mod_cast localMeshSize_pos n)).ne'
  have hden0 : V / 2 - phaseBoundaryRadius n ≠ 0 := (sub_pos.mpr hrn).ne'
  unfold highVelocityOuterWidth blockOuterHalfWidth
  field_simp [hn0, hh, hden0]

lemma eventually_highVelocity_outer_bounds
    (u V : ℝ) (hu : 0 ≤ u) (hV : 0 < V) :
    ∀ᶠ n : ℕ in atTop,
      0 ≤ highVelocityOuterHeight n u V ∧
      highVelocityOuterHeight n u V < u + 2 ∧
      0 ≤ highVelocityOuterWidth n u V ∧
      highVelocityOuterWidth n u V < 3 * localMeshHalfWidth n ∧
      V / 4 < V / 2 - phaseBoundaryRadius n ∧
      2 * growingVelocityCutoff n + phaseBoundaryRadius n <
        3 * growingVelocityCutoff n := by
  have hh := highVelocity_outerHeight_tendsto u V hV
  have hw := highVelocity_outerWidth_relative_tendsto_one u V hV
  have hr := phaseBoundaryRadius_tendsto_zero
  have hTr := growingVelocityCutoff_tendsto_atTop
  have hheightUpper := hh.eventually (Iio_mem_nhds (by linarith : u + 1 < u + 2))
  have hheightLower := hh.eventually (Ioi_mem_nhds (by linarith : 0 < u + 1))
  have hwidthRatioUpper := hw.eventually (Iio_mem_nhds (by norm_num : (2 : ℝ) < 3))
  have hwidthRatioLower := hw.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 2))
  have hrV := hr.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < V / 4))
  have hrT : ∀ᶠ n : ℕ in atTop,
      phaseBoundaryRadius n < growingVelocityCutoff n := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    unfold phaseBoundaryRadius growingVelocityCutoff rigidityPower
    exact Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast hn)
      (by norm_num)
  filter_upwards [Nat.eventually_pos, hheightUpper, hheightLower,
      hwidthRatioUpper, hwidthRatioLower, hrV, hrT]
    with n hn hhU hhL hwU hwL hrVN hrTN
  have hhalf : 0 < localMeshHalfWidth n := by
    unfold localMeshHalfWidth
    exact div_pos (mul_pos Real.pi_pos (by exact_mod_cast hn))
      (by exact_mod_cast localMeshSize_pos n)
  constructor
  · exact hhL.le
  constructor
  · exact hhU
  constructor
  · have hpos := mul_pos hwL hhalf
    rw [div_mul_cancel₀ _ hhalf.ne'] at hpos
    exact hpos.le
  constructor
  · exact (div_lt_iff₀ hhalf).mp hwU
  constructor <;> linarith

/-! The weighted velocity mass outside a fixed ball is the only limiting
contribution from large derivatives.  Its vanishing is a direct dominated
convergence consequence of the integrable Gaussian weight. -/

noncomputable def blockVelocityTailMass (V : ℝ) : ℝ :=
  ∫ b : ℂ in {b | V ≤ ‖b‖},
    ‖b‖ * Real.exp (-3 * Complex.normSq b)

lemma measurableSet_blockVelocityTail (V : ℝ) :
    MeasurableSet {b : ℂ | V ≤ ‖b‖} :=
  measurableSet_le measurable_const continuous_norm.measurable

lemma blockVelocityTailMass_nonneg (V : ℝ) :
    0 ≤ blockVelocityTailMass V := by
  unfold blockVelocityTailMass
  exact setIntegral_nonneg (measurableSet_blockVelocityTail V)
    (fun _ _ ↦ mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)

lemma blockVelocityMass_le_tailMass (L U : ℝ) :
    blockVelocityMass L U ≤ blockVelocityTailMass L := by
  unfold blockVelocityMass blockVelocityTailMass
  apply setIntegral_mono_set
    integrable_complex_norm_mul_exp_neg_three_normSq.integrableOn
  · exact Eventually.of_forall fun b ↦
      mul_nonneg (norm_nonneg b) (Real.exp_pos _).le
  · exact Eventually.of_forall fun b hb ↦ hb.1

lemma blockVelocityTailMass_tendsto_zero :
    Tendsto blockVelocityTailMass atTop (nhds 0) := by
  let f : ℂ → ℝ := fun b ↦
    ‖b‖ * Real.exp (-3 * Complex.normSq b)
  let F : ℝ → ℂ → ℝ := fun V ↦ {b : ℂ | V ≤ ‖b‖}.indicator f
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    f (F := F) (f := fun _ : ℂ ↦ (0 : ℝ))
    (Eventually.of_forall fun V ↦
      integrable_complex_norm_mul_exp_neg_three_normSq.aestronglyMeasurable.indicator
        (measurableSet_blockVelocityTail V))
    (Eventually.of_forall fun V ↦ Eventually.of_forall fun b ↦ by
      have hf0 : 0 ≤ f b := by dsimp [f]; positivity
      by_cases hb : V ≤ ‖b‖
      · rw [show F V b = f b by simp [F, hb]]
        simpa [Real.norm_eq_abs, abs_of_nonneg hf0]
      · rw [show F V b = 0 by simp [F, hb]]
        simpa [Real.norm_eq_abs] using hf0)
    integrable_complex_norm_mul_exp_neg_three_normSq
    (by
      filter_upwards [] with b
      have hev : ∀ᶠ V : ℝ in atTop, ‖b‖ < V := eventually_gt_atTop ‖b‖
      apply tendsto_const_nhds.congr'
      filter_upwards [hev] with V hV
      have hb : ¬ V ≤ ‖b‖ := not_le_of_gt hV
      simp [F, hb])
  have hz : (∫ _b : ℂ, (0 : ℝ)) = 0 := by simp
  rw [hz] at hDCT
  apply hDCT.congr'
  filter_upwards [] with V
  dsimp [blockVelocityTailMass, F, f]
  rw [integral_indicator (measurableSet_blockVelocityTail V)]

lemma volumeReal_complex_closedBall (U : ℝ) (hU : 0 ≤ U) :
    volume.real (Metric.closedBall (0 : ℂ) U) = Real.pi * U ^ 2 := by
  have hdim : Module.finrank ℝ ℂ = 2 * 1 := by simp
  rw [measureReal_def]
  rw [InnerProductSpace.volume_closedBall_of_dim_even hdim]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hU, ENNReal.toReal_ofReal (by positivity)]
  simp [Complex.finrank_real_complex]
  ring

lemma integral_norm_blockVelocityAnnulus_le
    (L U : ℝ) (hU : 0 ≤ U) :
    (∫ b : ℂ in blockVelocityAnnulus L U, ‖b‖) ≤
      Real.pi * U ^ 3 := by
  let s := blockVelocityAnnulus L U
  let B := Metric.closedBall (0 : ℂ) U
  have hsub : s ⊆ B := by
    intro b hb
    simpa [s, B, Metric.mem_closedBall, dist_zero_right] using hb.2
  have hBfinite : volume B < ⊤ := (isCompact_closedBall (0 : ℂ) U).measure_lt_top
  have hsfinite : volume s < ⊤ :=
    (measure_mono hsub).trans_lt hBfinite
  have hbound := norm_setIntegral_le_of_norm_le_const
    (μ := volume) (s := s) (f := fun b : ℂ ↦ ‖b‖) (C := U)
    hsfinite (fun b hb ↦ by
      have := hb.2
      simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg b)] using this)
  have hint0 : 0 ≤ ∫ b : ℂ in s, ‖b‖ :=
    setIntegral_nonneg (measurableSet_blockVelocityAnnulus L U)
      (fun _ _ ↦ norm_nonneg _)
  have hmeasure : volume.real s ≤ volume.real B :=
    measureReal_mono hsub hBfinite.ne
  calc
    (∫ b : ℂ in blockVelocityAnnulus L U, ‖b‖) ≤
        U * volume.real s := by
      simpa [s, Real.norm_eq_abs, abs_of_nonneg hint0] using hbound
    _ ≤ U * volume.real B := mul_le_mul_of_nonneg_left hmeasure hU
    _ = Real.pi * U ^ 3 := by
      rw [volumeReal_complex_closedBall U hU]
      ring

lemma localMeshSize_mul_halfWidth_div_nat_eq_pi
    (n : ℕ) (hn : 0 < n) :
    (localMeshSize n : ℝ) * localMeshHalfWidth n / (n : ℝ) = Real.pi := by
  unfold localMeshHalfWidth
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hM0 : (localMeshSize n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (localMeshSize_pos n))
  field_simp

lemma scaled_highVelocity_expanded_limiting_upper
    (n : ℕ) (hn : 0 < n) (u V : ℝ) (hu : 0 ≤ u) (hV : 0 < V) :
    (localMeshSize n : ℝ) *
        (∫ y in truncatedPhaseRegion (m := 1) n (u + 2)
          (3 * localMeshHalfWidth n) (V / 4)
          (3 * growingVelocityCutoff n), phaseLimitingDensity y) ≤
      (36 / Real.pi) * (u + 2) * blockVelocityTailMass (V / 4) := by
  have hhalf : 0 ≤ 3 * localMeshHalfWidth n := by
    unfold localMeshHalfWidth
    positivity
  have hheight : 0 ≤ u + 2 := by linarith
  have hlower : 0 < V / 4 := by positivity
  have hblock := blockLimitingDensity_truncatedBlockRegion_upper
    n hn (u + 2) (3 * localMeshHalfWidth n) (V / 4)
      (3 * growingVelocityCutoff n) hheight hhalf hlower
  have hlim :
      (∫ y in truncatedPhaseRegion (m := 1) n (u + 2)
          (3 * localMeshHalfWidth n) (V / 4)
          (3 * growingVelocityCutoff n), phaseLimitingDensity y) ≤
        (3 / Real.pi ^ 2) *
          (4 * (3 * localMeshHalfWidth n) * ((u + 2) / n)) *
            blockVelocityMass (V / 4) (3 * growingVelocityCutoff n) := by
    rw [integral_phaseLimitingDensity_truncatedPhaseRegion
      (m := 1) (by omega)]
    simpa only [truncatedBlockSet, pow_one] using hblock
  have hmass := blockVelocityMass_le_tailMass
    (V / 4) (3 * growingVelocityCutoff n)
  have hcoeff : 0 ≤ (3 / Real.pi ^ 2) *
      (4 * (3 * localMeshHalfWidth n) * ((u + 2) / n)) := by
    positivity
  have hlim' := hlim.trans (mul_le_mul_of_nonneg_left hmass hcoeff)
  have hM : 0 ≤ (localMeshSize n : ℝ) := by positivity
  calc
    (localMeshSize n : ℝ) *
        (∫ y in truncatedPhaseRegion (m := 1) n (u + 2)
          (3 * localMeshHalfWidth n) (V / 4)
          (3 * growingVelocityCutoff n), phaseLimitingDensity y) ≤
      (localMeshSize n : ℝ) *
        ((3 / Real.pi ^ 2) *
          (4 * (3 * localMeshHalfWidth n) * ((u + 2) / n)) *
            blockVelocityTailMass (V / 4)) :=
      mul_le_mul_of_nonneg_left hlim' hM
    _ = (36 / Real.pi) * (u + 2) * blockVelocityTailMass (V / 4) := by
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have hM0 : (localMeshSize n : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (localMeshSize_pos n))
      unfold localMeshHalfWidth
      field_simp [Real.pi_ne_zero]
      ring

lemma scaled_highVelocity_expanded_volume_upper
    (n : ℕ) (hn : 0 < n) (u V : ℝ) (hu : 0 ≤ u) (hV : 0 < V) :
    (localMeshSize n : ℝ) *
        volume.real (truncatedPhaseRegion (m := 1) n (u + 2)
          (3 * localMeshHalfWidth n) (V / 4)
          (3 * growingVelocityCutoff n)) ≤
      324 * Real.pi ^ 2 * (u + 2) * growingVelocityCutoff n ^ 3 := by
  have hhalf : 0 ≤ 3 * localMeshHalfWidth n := by
    unfold localMeshHalfWidth
    positivity
  have hheight : 0 ≤ u + 2 := by linarith
  have hlower : 0 < V / 4 := by positivity
  have hupper : 0 ≤ 3 * growingVelocityCutoff n := by
    exact mul_nonneg (by norm_num) (growingVelocityCutoff_nonneg n)
  have hnorm := integral_norm_blockVelocityAnnulus_le
    (V / 4) (3 * growingVelocityCutoff n) hupper
  have hvol := volumeReal_truncatedPhaseRegion 1 n (by omega) hn
    (u + 2) (3 * localMeshHalfWidth n) (V / 4)
      (3 * growingVelocityCutoff n) hheight hhalf hlower
  simp only [pow_one] at hvol
  have hbase : 0 ≤ 4 * (3 * localMeshHalfWidth n) * ((u + 2) / n) := by
    positivity
  have hvolBound :
      volume.real (truncatedPhaseRegion (m := 1) n (u + 2)
          (3 * localMeshHalfWidth n) (V / 4)
          (3 * growingVelocityCutoff n)) ≤
        (4 * (3 * localMeshHalfWidth n) * ((u + 2) / n)) *
          (Real.pi * (3 * growingVelocityCutoff n) ^ 3) := by
    rw [hvol]
    exact mul_le_mul_of_nonneg_left hnorm hbase
  have hM : 0 ≤ (localMeshSize n : ℝ) := by positivity
  calc
    (localMeshSize n : ℝ) *
        volume.real (truncatedPhaseRegion (m := 1) n (u + 2)
          (3 * localMeshHalfWidth n) (V / 4)
          (3 * growingVelocityCutoff n)) ≤
      (localMeshSize n : ℝ) *
        ((4 * (3 * localMeshHalfWidth n) * ((u + 2) / n)) *
          (Real.pi * (3 * growingVelocityCutoff n) ^ 3)) :=
      mul_le_mul_of_nonneg_left hvolBound hM
    _ = 324 * Real.pi ^ 2 * (u + 2) * growingVelocityCutoff n ^ 3 := by
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have hM0 : (localMeshSize n : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (localMeshSize_pos n))
      unfold localMeshHalfWidth
      field_simp [Real.pi_ne_zero]
      ring

lemma phaseBoundaryGaussianTail_one_tendsto_zero :
    Tendsto (phaseBoundaryGaussianTail 1) atTop (nhds 0) := by
  have hscaled := scaled_phaseBoundaryGaussianTail_tendsto_zero 1
  refine squeeze_zero'
    (f := phaseBoundaryGaussianTail 1)
    (g := fun n : ℕ ↦ (localMeshSize n : ℝ) *
      phaseBoundaryGaussianTail 1 n)
    (Eventually.of_forall fun n ↦ by
      unfold phaseBoundaryGaussianTail
      positivity)
    ?_ (by simpa only [pow_one] using hscaled)
  exact Eventually.of_forall fun n ↦ by
    have hone : (1 : ℝ) ≤ localMeshSize n := by
      exact_mod_cast localMeshSize_pos n
    have hnonneg : 0 ≤ phaseBoundaryGaussianTail 1 n := by
      unfold phaseBoundaryGaussianTail
      positivity
    nlinarith

theorem eventually_uniform_scaled_highVelocityPhaseProbability_upper
    (u V : ℝ) (hu : 0 ≤ u) (hV : 0 < V) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℝ,
      IsSmooth n (rigiditySmoothScale n) t →
      IsSpread n (rigiditySmoothScale n) (fun _ : Fin 1 ↦ t) →
      (localMeshSize n : ℝ) *
          uniformProbability (fun e : SignVector (2 * n) ↦
            normalizedPhaseEuclideanWalk n e (fun _ : Fin 1 ↦ t) ∈
              truncatedPhaseRegion (m := 1) n (u + 1)
                (2 * localMeshHalfWidth n) (V / 2)
                (2 * growingVelocityCutoff n)) ≤
        (72 / Real.pi) * (u + 2) * blockVelocityTailMass (V / 4) +
          648 * Real.pi ^ 2 * (u + 2) * growingVelocityCutoff n ^ 3 *
            quantitativePhaseDensityError 1 n := by
  have htail := phaseBoundaryGaussianTail_one_tendsto_zero.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [Nat.eventually_pos,
      eventually_highVelocity_outer_bounds u V hu hV,
      htail,
      eventually_uniform_phaseSmoothedDensity_le_explicit (m := 1) (by omega)]
    with n hn houterBounds htailN hdensity
  intro t hsmooth hspread
  rcases houterBounds with
    ⟨hOuterHeight0, hOuterHeight, hOuterWidth0, hOuterWidth,
      hOuterLower, hOuterUpper⟩
  let target := truncatedPhaseRegion (m := 1) n (u + 1)
    (2 * localMeshHalfWidth n) (V / 2) (2 * growingVelocityCutoff n)
  let expanded := truncatedPhaseRegion (m := 1) n (u + 2)
    (3 * localMeshHalfWidth n) (V / 4) (3 * growingVelocityCutoff n)
  let p := uniformProbability (fun e : SignVector (2 * n) ↦
    normalizedPhaseEuclideanWalk n e (fun _ : Fin 1 ↦ t) ∈ target)
  let err := quantitativePhaseDensityError 1 n
  have hhalf : 0 ≤ 2 * localMeshHalfWidth n := by
    unfold localMeshHalfWidth
    positivity
  have hrLower : phaseBoundaryRadius n < V / 2 := by
    linarith
  have hthick : Metric.thickening (phaseBoundaryRadius n) target ⊆ expanded := by
    have hfirst := thickening_truncatedPhaseRegion_subset_outer
      1 n hn (u + 1) (2 * localMeshHalfWidth n) (V / 2)
        (2 * growingVelocityCutoff n) (phaseBoundaryRadius n)
        (by linarith) hhalf (phaseBoundaryRadius_nonneg n) hrLower
    have hsecond := truncatedPhaseRegion_mono 1 n hn
      hOuterHeight.le hOuterWidth.le hOuterLower.le hOuterUpper.le
    exact hfirst.trans hsecond
  have hsigma : 0 < localCLTSmoothingScaleTest n := by
    unfold localCLTSmoothingScaleTest
    exact rigidityPower_pos hn _
  have hsandwich := uniformProbability_mul_gaussianLower_le_integral_thickening
    n (fun _ : Fin 1 ↦ t) (localCLTSmoothingScaleTest n)
      (phaseBoundaryRadius n) hsigma (phaseBoundaryRadius_nonneg n) target
  have hmono :
      (∫ y in Metric.thickening (phaseBoundaryRadius n) target,
          phaseSmoothedDensity n (fun _ : Fin 1 ↦ t)
            (localCLTSmoothingScaleTest n) y) ≤
        ∫ y in expanded,
          phaseSmoothedDensity n (fun _ : Fin 1 ↦ t)
            (localCLTSmoothingScaleTest n) y := by
    exact setIntegral_mono_set
      (integrable_phaseSmoothedDensity 1 n (fun _ : Fin 1 ↦ t)
        (localCLTSmoothingScaleTest n) hsigma).integrableOn
      (Eventually.of_forall fun y ↦ phaseSmoothedDensity_nonneg 1 n
        (fun _ : Fin 1 ↦ t) (localCLTSmoothingScaleTest n) y)
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
          (localCLTSmoothingScaleTest n) y - phaseLimitingDensity y| ≤ err := by
    intro y
    exact hdensity (fun _ : Fin 1 ↦ t) y (fun _ ↦ hsmooth) hspread
  have herror := abs_setIntegral_phaseSmoothedDensity_sub_limiting_le
    1 n (by omega) (fun _ : Fin 1 ↦ t) (localCLTSmoothingScaleTest n)
      err expanded hfinite (quantitativePhaseDensityError_nonneg 1 n) hclose
  have hsmoothUpper :
      (∫ y in expanded, phaseSmoothedDensity n (fun _ : Fin 1 ↦ t)
          (localCLTSmoothingScaleTest n) y) ≤
        (∫ y in expanded, phaseLimitingDensity y) + err * volume.real expanded := by
    linarith [le_abs_self
      ((∫ y in expanded, phaseSmoothedDensity n (fun _ : Fin 1 ↦ t)
          (localCLTSmoothingScaleTest n) y) -
        ∫ y in expanded, phaseLimitingDensity y)]
  have hp : 0 ≤ p := uniformProbability_nonneg _
  have hpHalf : p * (1 / 2) ≤
      ∫ y in expanded, phaseSmoothedDensity n (fun _ : Fin 1 ↦ t)
        (localCLTSmoothingScaleTest n) y := by
    have hfactor : (1 / 2 : ℝ) ≤ 1 - phaseBoundaryGaussianTail 1 n := by
      linarith
    calc
      p * (1 / 2) ≤ p * (1 - phaseBoundaryGaussianTail 1 n) :=
        mul_le_mul_of_nonneg_left hfactor hp
      _ ≤ (∫ y in Metric.thickening (phaseBoundaryRadius n) target,
          phaseSmoothedDensity n (fun _ : Fin 1 ↦ t)
            (localCLTSmoothingScaleTest n) y) := by
        simpa only [p, target, phaseBoundaryGaussianTail, one_mul] using hsandwich
      _ ≤ _ := hmono
  have hpUpper : p ≤ 2 *
      ((∫ y in expanded, phaseLimitingDensity y) +
        err * volume.real expanded) := by
    linarith [hpHalf, hsmoothUpper]
  have hM : 0 ≤ (localMeshSize n : ℝ) := by positivity
  have hlim := scaled_highVelocity_expanded_limiting_upper
    n hn u V hu hV
  have hvol := scaled_highVelocity_expanded_volume_upper
    n hn u V hu hV
  have herr : 0 ≤ err := quantitativePhaseDensityError_nonneg 1 n
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
            quantitativePhaseDensityError 1 n := by
      dsimp [err]
      ring

lemma growingVelocityCutoff_cube_mul_densityError_tendsto_zero :
    Tendsto (fun n : ℕ ↦ growingVelocityCutoff n ^ 3 *
      quantitativePhaseDensityError 1 n) atTop (nhds 0) := by
  have h := rigidityPower_three_over_128_mul_quantitativePhaseDensityError_one_tendsto_zero
  apply h.congr'
  filter_upwards [Nat.eventually_pos] with n hn
  unfold growingVelocityCutoff
  rw [rigidityPower_nat_pow hn]
  norm_num

lemma highMeshVelocity_growing_upper_tendsto_zero :
    Tendsto (fun n : ℕ ↦
      (localMeshSize n : ℝ) *
        (4 * Real.exp (-(growingVelocityCutoff n / 2) ^ 2 / 2)))
      atTop (nhds 0) := by
  have hcore := (tendsto_rigidityPower_mul_exp_neg_power_test
    2 (1 / 64) (1 / 8) (by norm_num) (by norm_num)).const_mul 8
  refine squeeze_zero'
    (g := fun n : ℕ ↦ 8 * (rigidityPower n 2 *
      Real.exp (-(1 / 8) * rigidityPower n (1 / 64))))
    (Eventually.of_forall fun n ↦ by positivity) ?_ (by simpa using hcore)
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
  have hexp : -(growingVelocityCutoff n / 2) ^ 2 / 2 =
      -(1 / 8) * rigidityPower n (1 / 64) := by
    rw [div_pow, hcutSq]
    ring
  rw [hexp]
  have hnonneg : 0 ≤ 4 * Real.exp
      (-(1 / 8) * rigidityPower n (1 / 64)) := by positivity
  calc
    (localMeshSize n : ℝ) *
        (4 * Real.exp (-(1 / 8) * rigidityPower n (1 / 64))) ≤
      (2 * rigidityPower n 2) *
        (4 * Real.exp (-(1 / 8) * rigidityPower n (1 / 64))) :=
      mul_le_mul_of_nonneg_right hsize hnonneg
    _ = 8 * (rigidityPower n 2 *
        Real.exp (-(1 / 8) * rigidityPower n (1 / 64))) := by ring

theorem uniformProbability_highMeshVelocity_growing_tendsto_zero :
    Tendsto (fun n : ℕ ↦ uniformProbability
      (HasHighMeshVelocity n (growingVelocityCutoff n))) atTop (nhds 0) := by
  apply squeeze_zero' (Eventually.of_forall fun n ↦ uniformProbability_nonneg _)
  · filter_upwards [Nat.eventually_pos] with n hn
    exact uniformProbability_highMeshVelocity_le n (growingVelocityCutoff n)
      (by unfold growingVelocityCutoff; exact rigidityPower_pos hn _)
  · exact highMeshVelocity_growing_upper_tendsto_zero

lemma highVelocity_minimumTransferWidthFactor_tendsto_one (u : ℝ) :
    Tendsto (fun n : ℕ ↦ minimumTransferWidthFactor n u
      (growingVelocityCutoff n / 2) (2 * growingVelocityCutoff n))
      atTop (nhds 1) := by
  have hInv : Tendsto (fun n : ℕ ↦ (growingVelocityCutoff n)⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp growingVelocityCutoff_tendsto_atTop
  have hfirst :=
    ((globalAccelerationBound_div_tendsto_zero.const_mul (4 * u)).mul
      (hInv.pow 2))
  have hsecond :=
    ((globalAccelerationBound_mul_halfWidth_tendsto_zero.const_mul 8).mul hInv)
  have hsum : Tendsto (fun n : ℕ ↦
      4 * u * (globalAccelerationBound n / (n : ℝ)) *
          (growingVelocityCutoff n)⁻¹ ^ 2 +
        8 * (globalAccelerationBound n * localMeshHalfWidth n) *
          (growingVelocityCutoff n)⁻¹) atTop (nhds 0) := by
    simpa using hfirst.add hsecond
  have hone :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1)).add hsum
  have hone' : Tendsto (fun n : ℕ ↦
      1 + (4 * u * (globalAccelerationBound n / (n : ℝ)) *
          (growingVelocityCutoff n)⁻¹ ^ 2 +
        8 * (globalAccelerationBound n * localMeshHalfWidth n) *
          (growingVelocityCutoff n)⁻¹)) atTop (nhds 1) := by
    simpa using hone
  apply hone'.congr'
  filter_upwards [Nat.eventually_pos] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hh0 : localMeshHalfWidth n ≠ 0 := by
    unfold localMeshHalfWidth
    exact div_ne_zero (mul_ne_zero Real.pi_ne_zero (by exact_mod_cast hn.ne'))
      (by exact_mod_cast (localMeshSize_pos n).ne')
  have hT0 : growingVelocityCutoff n ≠ 0 :=
    (by unfold growingVelocityCutoff; exact (rigidityPower_pos hn _).ne')
  unfold minimumTransferWidthFactor minimumAffineOffsetError
  field_simp [hn0, hh0, hT0]
  ring

lemma globalAccelerationBound_mul_halfWidth_mul_growingCutoff_tendsto_zero :
    Tendsto (fun n : ℕ ↦ globalAccelerationBound n * localMeshHalfWidth n *
      growingVelocityCutoff n) atTop (nhds 0) := by
  have hpower := tendsto_rigidityPower_neg_zero
    (show (0 : ℝ) < 111 / 128 by norm_num)
  have hfirstBase := scaled_localMeshHalfWidth_tendsto_pi.mul hpower
  have hfirstBase' : Tendsto (fun n : ℕ ↦
      (n : ℝ) * localMeshHalfWidth n * rigidityPower n (-(111 / 128 : ℝ)))
      atTop (nhds 0) := by simpa using hfirstBase
  have hfirst : Tendsto (fun n : ℕ ↦
      accelerationCutoff n * localMeshHalfWidth n * growingVelocityCutoff n)
      atTop (nhds 0) := by
    apply hfirstBase'.congr'
    filter_upwards [Nat.eventually_pos] with n hn
    unfold accelerationCutoff growingVelocityCutoff
    rw [show (n : ℝ) = rigidityPower n 1 by simp [rigidityPower]]
    calc
      rigidityPower n 1 * localMeshHalfWidth n *
          rigidityPower n (-(111 / 128 : ℝ)) =
        localMeshHalfWidth n *
          (rigidityPower n 1 * rigidityPower n (-(111 / 128 : ℝ))) := by ring
      _ = localMeshHalfWidth n * rigidityPower n (17 / 128) := by
        rw [← rigidityPower_add hn]
        congr 2
        norm_num
      _ = localMeshHalfWidth n *
          (rigidityPower n (1 / 8) * rigidityPower n (1 / 128)) := by
        rw [← rigidityPower_add hn]
        congr 2
        norm_num
      _ = rigidityPower n (1 / 8) * localMeshHalfWidth n *
          rigidityPower n (1 / 128) := by ring
  have hsqrt := sqrt_centeredCount_div_tendsto_zero
  have hsecondBase := ((hsqrt.mul scaled_localMeshHalfWidth_tendsto_pi).mul
    localMeshHalfWidth_mul_growingVelocityCutoff_tendsto_zero).const_mul 2
  have hsecondBase' : Tendsto (fun n : ℕ ↦
      2 * ((Real.sqrt (2 * n + 1 : ℝ) / n) *
        ((n : ℝ) * localMeshHalfWidth n) *
          (localMeshHalfWidth n * growingVelocityCutoff n)))
      atTop (nhds 0) := by simpa using hsecondBase
  have hsecond : Tendsto (fun n : ℕ ↦
      2 * Real.sqrt (2 * n + 1 : ℝ) * localMeshHalfWidth n ^ 2 *
        growingVelocityCutoff n) atTop (nhds 0) := by
    apply hsecondBase'.congr'
    filter_upwards [Nat.eventually_pos] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  have hsum := hfirst.add hsecond
  have hsum' : Tendsto (fun n : ℕ ↦
      accelerationCutoff n * localMeshHalfWidth n * growingVelocityCutoff n +
        2 * Real.sqrt (2 * n + 1 : ℝ) * localMeshHalfWidth n ^ 2 *
          growingVelocityCutoff n) atTop (nhds 0) := by simpa using hsum
  apply hsum'.congr'
  filter_upwards [] with n
  unfold globalAccelerationBound
  ring

lemma highVelocity_fixedLower_minimumTransferWidthFactor_tendsto_one
    (u V : ℝ) (hV : 0 < V) :
    Tendsto (fun n : ℕ ↦ minimumTransferWidthFactor n u (V / 2)
      (2 * growingVelocityCutoff n)) atTop (nhds 1) := by
  have hfirst := globalAccelerationBound_div_tendsto_zero.const_mul u
  have hsecond :=
    globalAccelerationBound_mul_halfWidth_mul_growingCutoff_tendsto_zero.const_mul 2
  have hnum : Tendsto (fun n : ℕ ↦
      u * (globalAccelerationBound n / (n : ℝ)) +
        2 * (globalAccelerationBound n * localMeshHalfWidth n *
          growingVelocityCutoff n)) atTop (nhds 0) := by
    simpa using hfirst.add hsecond
  have hdiv := hnum.div_const ((V / 2) ^ 2)
  have hone :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1)).add hdiv
  have hone' : Tendsto (fun n : ℕ ↦
      1 + (u * (globalAccelerationBound n / (n : ℝ)) +
        2 * (globalAccelerationBound n * localMeshHalfWidth n *
          growingVelocityCutoff n)) / (V / 2) ^ 2) atTop (nhds 1) := by
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

def HasHighVelocityMeshWitness
    (n : ℕ) (u V : ℝ) (e : SignVector (2 * n)) : Prop :=
  ∃ a : Fin (localMeshSize n),
    a ∈ halfLocalMeshSites n ∧
    IsSmooth n (rigiditySmoothScale n) (localMeshPoint n a) ∧
    IsSpread n (rigiditySmoothScale n)
      (fun _ : Fin 1 ↦ localMeshPoint n a) ∧
    IsFactoredTruncatedLocalRepresentative n 2 (u + 1)
      (V / 2) (2 * growingVelocityCutoff n) e a

lemma centeredMinimizer_orthogonal
    (n : ℕ) (e : SignVector (2 * n)) (t : ℝ)
    (hvalue : ‖rescaledCenteredEval n e t‖ = centeredMin n e) :
    (rescaledCenteredEval n e t *
      conj (rescaledCenteredVelocity n e t)).re = 0 := by
  have hlocal : IsLocalMin (centeredEnergy n e) t := by
    change ∀ᶠ s in nhds t, centeredEnergy n e t ≤ centeredEnergy n e s
    exact Eventually.of_forall fun s ↦ by
      have hle := centeredMin_le_rescaledCenteredEval n e s
      have hnonneg : 0 ≤ centeredMin n e := by
        rw [← hvalue]
        exact norm_nonneg _
      unfold centeredEnergy
      rw [hvalue]
      exact pow_le_pow_left₀ hnonneg hle 2
  have hzero : deriv (centeredEnergy n e) t = 0 := hlocal.deriv_eq_zero
  have hderiv := (hasDerivAt_centeredEnergy n e t).deriv
  rw [hzero] at hderiv
  linarith

theorem eventually_highVelocitySmallMinimum_subset_witness_or_exceptions
    (u V : ℝ) (hV : 0 < V) :
    ∀ᶠ n : ℕ in atTop, ∀ e : SignVector (2 * n),
      HasHighVelocitySmallMinimum n u V e →
        HasHighVelocityMeshWitness n u V e ∨
        HasHighMeshAcceleration n e ∨
        HasHighMeshVelocity n (growingVelocityCutoff n) e := by
  have hwidthDynamic : ∀ᶠ n : ℕ in atTop,
      minimumTransferWidthFactor n u (V / 2)
          (2 * growingVelocityCutoff n) < 2 :=
    (highVelocity_fixedLower_minimumTransferWidthFactor_tendsto_one u V hV).eventually
      (Iio_mem_nhds (by norm_num))
  have hheightDynamic : ∀ᶠ n : ℕ in atTop,
      minimumTransferHeight n u < u + 1 :=
    (minimumTransferHeight_tendsto u).eventually
      (Iio_mem_nhds (by linarith))
  have hvelocityError : ∀ᶠ n : ℕ in atTop,
      4 * minimumVelocityTransferError n < V := by
    have hleft := minimumVelocityTransferError_tendsto_zero.const_mul 4
    have hleft' : Tendsto (fun n : ℕ ↦
        4 * minimumVelocityTransferError n) atTop (nhds 0) := by
      simpa using hleft
    exact hleft'.eventually (Iio_mem_nhds hV)
  filter_upwards [Nat.eventually_pos,
      eventually_two_halfWidth_lt_pi_mul_rigiditySmoothScale,
      eventually_nearest_halfLocalMeshSite_smooth,
      hwidthDynamic, hheightDynamic, hvelocityError]
    with n hn hcell hnearest hwidthN hheightN hvelocityN
  intro e hhigh
  by_cases hacc : HasHighMeshAcceleration n e
  · exact Or.inr (Or.inl hacc)
  by_cases hmesh : HasHighMeshVelocity n (growingVelocityCutoff n) e
  · exact Or.inr (Or.inr hmesh)
  left
  rcases hhigh with ⟨t, ht, hvalue, hsmall, htSmooth, htVelocity⟩
  have htSmoothTwo : IsSmooth n (2 * rigiditySmoothScale n) t := by
    intro p hp1 hpFloor
    have hscale : 0 ≤ rigiditySmoothScale n := by
      unfold rigiditySmoothScale
      exact rigidityPower_nonneg n _
    have hpBound : p ≤ Nat.floor (4 * rigiditySmoothScale n) + 1 :=
      hpFloor.trans (Nat.add_le_add_right
        (Nat.floor_mono (by linarith)) 1)
    have hstrong := htSmooth p hp1 hpBound
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact (div_le_div_of_nonneg_right (by linarith) hnR.le).trans_lt hstrong
  rcases exists_halfLocalMeshSite_within_halfWidth n hn
      (2 * rigiditySmoothScale n) t hcell htSmoothTwo ht with
    ⟨a, haHalf, haNear⟩
  have haSmooth := hnearest t htSmoothTwo a haNear
  have haSpread := singleton_spread_of_near_four_smooth
    n hn t ht htSmooth a haHalf haNear hcell
  have hvelDiff := abs_norm_rescaledCenteredVelocity_sub_le_of_near
    n hn e hacc t ht a haNear
  rw [abs_le] at hvelDiff
  have hsiteNotHigh : ¬ growingVelocityCutoff n ≤
      ‖rescaledCenteredVelocity n e (localMeshPoint n a)‖ := by
    intro ha
    exact hmesh ⟨a, ha⟩
  have hTpos : 0 < growingVelocityCutoff n := by
    unfold growingVelocityCutoff
    exact rigidityPower_pos hn _
  have haLower : V / 2 ≤
      ‖rescaledCenteredVelocity n e (localMeshPoint n a)‖ := by
    have hsiteLower :
        ‖rescaledCenteredVelocity n e t‖ - minimumVelocityTransferError n ≤
          ‖rescaledCenteredVelocity n e (localMeshPoint n a)‖ := by
      linarith [hvelDiff.1]
    have hstrict : V / 2 <
        ‖rescaledCenteredVelocity n e t‖ - minimumVelocityTransferError n := by
      linarith
    exact hstrict.le.trans hsiteLower
  have haUpper :
      ‖rescaledCenteredVelocity n e (localMeshPoint n a)‖ ≤
        2 * growingVelocityCutoff n := by
    have hsite := lt_of_not_ge hsiteNotHigh
    linarith
  have hortho := centeredMinimizer_orthogonal n e t hvalue
  have hrep := isFactoredTruncatedLocalRepresentative_of_minimizer
    n hn e hacc u (V / 2)
      (2 * growingVelocityCutoff n) t ht
      (by simpa [hvalue] using hsmall) hortho a haHalf haNear
      (half_pos hV) haLower haUpper
  refine ⟨a, haHalf, haSmooth, haSpread, ?_⟩
  apply isFactoredTruncatedLocalRepresentative_mono_height n 2
    (minimumTransferHeight n u) (u + 1) (V / 2)
      (2 * growingVelocityCutoff n) hheightN.le e a
  exact isFactoredTruncatedLocalRepresentative_mono n
    (minimumTransferWidthFactor n u (V / 2)
      (2 * growingVelocityCutoff n)) 2 (minimumTransferHeight n u)
      (V / 2) (2 * growingVelocityCutoff n)
      hwidthN.le e a hrep

theorem eventually_highVelocityMeshWitness_probability_le
    (u V : ℝ) (hu : 0 ≤ u) (hV : 0 < V) :
    ∀ᶠ n : ℕ in atTop,
      uniformProbability (HasHighVelocityMeshWitness n u V) ≤
        (72 / Real.pi) * (u + 2) * blockVelocityTailMass (V / 4) +
          648 * Real.pi ^ 2 * (u + 2) * growingVelocityCutoff n ^ 3 *
            quantitativePhaseDensityError 1 n := by
  filter_upwards [Nat.eventually_pos,
      eventually_uniform_scaled_highVelocityPhaseProbability_upper u V hu hV]
    with n hn hphase
  let B : ℝ :=
    (72 / Real.pi) * (u + 2) * blockVelocityTailMass (V / 4) +
      648 * Real.pi ^ 2 * (u + 2) * growingVelocityCutoff n ^ 3 *
        quantitativePhaseDensityError 1 n
  have hB : 0 ≤ B := by
    have htail0 := blockVelocityTailMass_nonneg (V / 4)
    have herr0 := quantitativePhaseDensityError_nonneg 1 n
    have hcut0 := growingVelocityCutoff_nonneg n
    dsimp [B]
    positivity
  let P : Fin (localMeshSize n) → SignVector (2 * n) → Prop := fun a e ↦
    a ∈ halfLocalMeshSites n ∧
    IsSmooth n (rigiditySmoothScale n) (localMeshPoint n a) ∧
    IsSpread n (rigiditySmoothScale n)
      (fun _ : Fin 1 ↦ localMeshPoint n a) ∧
    IsFactoredTruncatedLocalRepresentative n 2 (u + 1)
      (V / 2) (2 * growingVelocityCutoff n) e a
  have hmeshPos : (0 : ℝ) < localMeshSize n := by
    exact_mod_cast localMeshSize_pos n
  have hsite : ∀ a : Fin (localMeshSize n),
      uniformProbability (P a) ≤ B / localMeshSize n := by
    intro a
    by_cases haHalf : a ∈ halfLocalMeshSites n
    · by_cases hsmooth :
        IsSmooth n (rigiditySmoothScale n) (localMeshPoint n a)
      · by_cases hspread : IsSpread n (rigiditySmoothScale n)
          (fun _ : Fin 1 ↦ localMeshPoint n a)
        · apply (le_div_iff₀ hmeshPos).2
          have hmono : uniformProbability (P a) ≤
              uniformProbability (fun e : SignVector (2 * n) ↦
                IsFactoredTruncatedLocalRepresentative n 2 (u + 1)
                  (V / 2) (2 * growingVelocityCutoff n) e a) := by
            apply uniformProbability_mono
            intro e he
            exact he.2.2.2
          have heq := factoredTruncatedLocalProbability_eq_phase_one
            n hn 2 (u + 1) (V / 2) (2 * growingVelocityCutoff n)
              (half_pos hV) a
          have hrep : (localMeshSize n : ℝ) *
              uniformProbability (fun e : SignVector (2 * n) ↦
                IsFactoredTruncatedLocalRepresentative n 2 (u + 1)
                  (V / 2) (2 * growingVelocityCutoff n) e a) ≤ B := by
            rw [heq]
            simpa only [factoredTruncatedPhaseProbability, B] using
              hphase (localMeshPoint n a) hsmooth hspread
          calc
            uniformProbability (P a) * (localMeshSize n : ℝ) ≤
                (localMeshSize n : ℝ) *
                  uniformProbability (fun e : SignVector (2 * n) ↦
                    IsFactoredTruncatedLocalRepresentative n 2 (u + 1)
                      (V / 2) (2 * growingVelocityCutoff n) e a) := by
              rw [mul_comm]
              exact mul_le_mul_of_nonneg_left hmono hmeshPos.le
            _ ≤ B := hrep
        · have hempty : ∀ e : SignVector (2 * n), ¬P a e := by
            intro e he
            exact hspread he.2.2.1
          have hzero : uniformProbability (P a) = 0 := by
            unfold uniformProbability
            simp [Finset.filter_eq_empty_iff, hempty]
          rw [hzero]
          exact div_nonneg hB hmeshPos.le
      · have hempty : ∀ e : SignVector (2 * n), ¬P a e := by
          intro e he
          exact hsmooth he.2.1
        have hzero : uniformProbability (P a) = 0 := by
          unfold uniformProbability
          simp [Finset.filter_eq_empty_iff, hempty]
        rw [hzero]
        exact div_nonneg hB hmeshPos.le
    · have hempty : ∀ e : SignVector (2 * n), ¬P a e := by
        intro e he
        exact haHalf he.1
      have hzero : uniformProbability (P a) = 0 := by
        unfold uniformProbability
        simp [Finset.filter_eq_empty_iff, hempty]
      rw [hzero]
      exact div_nonneg hB hmeshPos.le
  have hexists : uniformProbability (fun e : SignVector (2 * n) ↦
      ∃ a, P a e) ≤ ∑ a, uniformProbability (P a) :=
    uniformProbability_exists_le_sum P
  calc
    uniformProbability (HasHighVelocityMeshWitness n u V) =
        uniformProbability (fun e : SignVector (2 * n) ↦ ∃ a, P a e) := by
      apply congrArg uniformProbability
      funext e
      apply propext
      simp only [HasHighVelocityMeshWitness, P]
    _ ≤ ∑ a, uniformProbability (P a) := hexists
    _ ≤ ∑ _a : Fin (localMeshSize n), B / localMeshSize n := by
      exact Finset.sum_le_sum fun a _ha ↦ hsite a
    _ = B := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp only [nsmul_eq_mul]
      field_simp [hmeshPos.ne']
    _ = _ := rfl

theorem eventually_highVelocitySmallMinimum_probability_le
    (u V : ℝ) (hu : 0 ≤ u) (hV : 0 < V) :
    ∀ᶠ n : ℕ in atTop,
      uniformProbability (HasHighVelocitySmallMinimum n u V) ≤
        (72 / Real.pi) * (u + 2) * blockVelocityTailMass (V / 4) +
          648 * Real.pi ^ 2 * (u + 2) * growingVelocityCutoff n ^ 3 *
            quantitativePhaseDensityError 1 n +
          uniformProbability (HasHighMeshAcceleration n) +
          uniformProbability
            (HasHighMeshVelocity n (growingVelocityCutoff n)) := by
  filter_upwards [eventually_highVelocitySmallMinimum_subset_witness_or_exceptions
      u V hV,
    eventually_highVelocityMeshWitness_probability_le u V hu hV]
    with n hsubset hwitness
  let A : SignVector (2 * n) → Prop := HasHighVelocityMeshWitness n u V
  let B : SignVector (2 * n) → Prop := HasHighMeshAcceleration n
  let C : SignVector (2 * n) → Prop :=
    HasHighMeshVelocity n (growingVelocityCutoff n)
  calc
    uniformProbability (HasHighVelocitySmallMinimum n u V) ≤
        uniformProbability (fun e ↦ A e ∨ B e ∨ C e) := by
      apply uniformProbability_mono
      intro e he
      simpa only [A, B, C] using hsubset e he
    _ ≤ uniformProbability A + uniformProbability (fun e ↦ B e ∨ C e) :=
      uniformProbability_or_le_add _ _
    _ ≤ uniformProbability A +
        (uniformProbability B + uniformProbability C) := by
      gcongr
      exact uniformProbability_or_le_add _ _
    _ ≤ ((72 / Real.pi) * (u + 2) * blockVelocityTailMass (V / 4) +
          648 * Real.pi ^ 2 * (u + 2) * growingVelocityCutoff n ^ 3 *
            quantitativePhaseDensityError 1 n) +
        (uniformProbability B + uniformProbability C) := by gcongr
    _ = _ := by
      simp only [A, B, C]
      ring

theorem highVelocitySmallMinimum_eventually_lt
    (u V b : ℝ) (hu : 0 ≤ u) (hV : 0 < V)
    (hb : (72 / Real.pi) * (u + 2) *
      blockVelocityTailMass (V / 4) < b) :
    ∀ᶠ n : ℕ in atTop,
      uniformProbability (HasHighVelocitySmallMinimum n u V) < b := by
  let C := (72 / Real.pi) * (u + 2) * blockVelocityTailMass (V / 4)
  let E : ℕ → ℝ := fun n ↦
    648 * Real.pi ^ 2 * (u + 2) * growingVelocityCutoff n ^ 3 *
      quantitativePhaseDensityError 1 n
  have hE : Tendsto E atTop (nhds 0) := by
    have h := growingVelocityCutoff_cube_mul_densityError_tendsto_zero.const_mul
      (648 * Real.pi ^ 2 * (u + 2))
    convert h using 1 <;> simp [E] <;> ring_nf
  have hrem := (hE.add uniformProbability_highMeshAcceleration_tendsto_zero).add
    uniformProbability_highMeshVelocity_growing_tendsto_zero
  have hrem' : Tendsto (fun n : ℕ ↦
      E n + uniformProbability (HasHighMeshAcceleration n) +
        uniformProbability (HasHighMeshVelocity n (growingVelocityCutoff n)))
      atTop (nhds 0) := by simpa using hrem
  have hsmall := hrem'.eventually
    (Iio_mem_nhds (show (0 : ℝ) < b - C by dsimp [C]; linarith))
  filter_upwards [eventually_highVelocitySmallMinimum_probability_le u V hu hV,
      hsmall] with n hupper hsmallN
  dsimp [C, E] at hsmallN
  exact hupper.trans_lt (by linarith)

theorem highVelocitySmallMinimum_vanishes_after_cutoff
    (u eps : ℝ) (hu : 0 ≤ u) (heps : 0 < eps) :
    ∃ V : ℝ, 0 < V ∧ ∀ᶠ n : ℕ in atTop,
      uniformProbability (HasHighVelocitySmallMinimum n u V) < eps := by
  let c : ℝ := (72 / Real.pi) * (u + 2)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have htarget : 0 < eps / c := div_pos heps hc
  have htail := blockVelocityTailMass_tendsto_zero.eventually
    (Iio_mem_nhds htarget)
  rcases (htail.and (eventually_gt_atTop (0 : ℝ))).exists with ⟨L, hLtail, hL⟩
  refine ⟨4 * L, by positivity, ?_⟩
  apply highVelocitySmallMinimum_eventually_lt u (4 * L) eps hu (by positivity)
  have hcTail : c * blockVelocityTailMass L < eps := by
    simpa [mul_comm] using (lt_div_iff₀ hc).mp hLtail
  simpa [c] using hcTail

end Erdos525
