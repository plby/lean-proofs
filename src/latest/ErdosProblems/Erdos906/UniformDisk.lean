import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace CofiniteDerivatives

noncomputable section

/-- Lebesgue volume restricted to the closed unit disk, regarded as a finite measure. -/
def uniformDiskFinite : FiniteMeasure ℂ where
  val := volume.restrict (closedBall 0 1)
  property := by
    constructor
    rw [Measure.restrict_apply_univ, Complex.volume_closedBall]
    simp

/-- The normalized uniform probability measure on the closed unit disk in `ℂ`. -/
def uniformDisk : Measure ℂ :=
  (uniformDiskFinite.normalize : Measure ℂ)

@[simp]
theorem uniformDiskFinite_mass : uniformDiskFinite.mass = NNReal.pi := by
  apply ENNReal.coe_injective
  rw [FiniteMeasure.ennreal_mass]
  simp [uniformDiskFinite, Complex.volume_closedBall]

theorem uniformDiskFinite_ne_zero : uniformDiskFinite ≠ 0 := by
  apply uniformDiskFinite.mass_nonzero_iff.mp
  rw [uniformDiskFinite_mass]
  exact NNReal.pi_ne_zero

instance uniformDisk.isProbabilityMeasure : IsProbabilityMeasure uniformDisk := by
  unfold uniformDisk
  infer_instance

theorem uniformDisk_isProbabilityMeasure : IsProbabilityMeasure uniformDisk := inferInstance

theorem uniformDisk_ne_zero : uniformDisk ≠ 0 :=
  IsProbabilityMeasure.ne_zero uniformDisk

theorem uniformDisk_ae_mem_closedBall :
    ∀ᵐ z ∂uniformDisk, z ∈ closedBall (0 : ℂ) 1 := by
  rw [ae_iff]
  change uniformDisk ((closedBall (0 : ℂ) 1)ᶜ) = 0
  unfold uniformDisk
  rw [uniformDiskFinite.toMeasure_normalize_eq_of_nonzero uniformDiskFinite_ne_zero]
  rw [Measure.coe_nnreal_smul_apply]
  rw [ENNReal.coe_inv (uniformDiskFinite.mass_nonzero_iff.mpr uniformDiskFinite_ne_zero)]
  change (uniformDiskFinite.mass⁻¹ : ℝ≥0∞) *
    (volume.restrict (closedBall (0 : ℂ) 1)) ((closedBall 0 1)ᶜ) = 0
  rw [Measure.restrict_apply' measurableSet_closedBall]
  simp

theorem uniformDisk_singleton (z : ℂ) : uniformDisk ({z} : Set ℂ) = 0 := by
  unfold uniformDisk
  rw [uniformDiskFinite.toMeasure_normalize_eq_of_nonzero uniformDiskFinite_ne_zero]
  rw [Measure.coe_nnreal_smul_apply]
  rw [ENNReal.coe_inv (uniformDiskFinite.mass_nonzero_iff.mpr uniformDiskFinite_ne_zero)]
  change (uniformDiskFinite.mass⁻¹ : ℝ≥0∞) *
    (volume.restrict (closedBall (0 : ℂ) 1)) {z} = 0
  rw [Measure.restrict_apply (measurableSet_singleton z)]
  have hsingleton : volume ({z} : Set ℂ) = 0 := by
    simp
  rw [measure_mono_null inter_subset_left hsingleton, mul_zero]

/-- The normalized disk measure is bounded by Lebesgue volume divided by `π`. -/
theorem uniformDisk_le_normalized_volume (s : Set ℂ) :
    uniformDisk s ≤ (NNReal.pi : ℝ≥0∞)⁻¹ * volume s := by
  unfold uniformDisk
  rw [uniformDiskFinite.toMeasure_normalize_eq_of_nonzero uniformDiskFinite_ne_zero]
  rw [Measure.coe_nnreal_smul_apply]
  rw [ENNReal.coe_inv (uniformDiskFinite.mass_nonzero_iff.mpr uniformDiskFinite_ne_zero)]
  change (uniformDiskFinite.mass⁻¹ : ℝ≥0∞) *
    (volume.restrict (closedBall (0 : ℂ) 1)) s ≤ (NNReal.pi : ℝ≥0∞)⁻¹ * volume s
  rw [uniformDiskFinite_mass]
  simpa only [mul_comm] using!
    mul_le_mul_left (Measure.restrict_le_self (μ := volume) (s := closedBall (0 : ℂ) 1) s)
      (NNReal.pi : ℝ≥0∞)⁻¹

/-- Affine small-ball bound for the normalized uniform measure on the unit disk. -/
theorem uniformDisk_affine_smallBall {a : ℂ} (ha : a ≠ 0) (w : ℂ) {ε : ℝ} (hε : 0 ≤ ε) :
    uniformDisk {z | ‖a * z + w‖ < ε} ≤ ENNReal.ofReal ((ε / ‖a‖) ^ 2) := by
  let c : ℂ := -(a⁻¹ * w)
  let r : ℝ := ε / ‖a‖
  have hr : 0 ≤ r := div_nonneg hε (norm_nonneg a)
  have hsubset : {z : ℂ | ‖a * z + w‖ < ε} ⊆ ball c r := by
    intro z hz
    rw [mem_ball, dist_eq_norm]
    have hid : z - c = a⁻¹ * (a * z + w) := by
      dsimp [c]
      field_simp [ha]
      simp [sub_eq_add_neg, add_comm]
    rw [hid, norm_mul, norm_inv]
    rw [← div_eq_inv_mul]
    exact (div_lt_div_iff_of_pos_right (norm_pos_iff.mpr ha)).2 hz
  calc
    uniformDisk {z | ‖a * z + w‖ < ε} ≤ uniformDisk (ball c r) :=
      measure_mono hsubset
    _ ≤ (NNReal.pi : ℝ≥0∞)⁻¹ * volume (ball c r) :=
      uniformDisk_le_normalized_volume _
    _ = ENNReal.ofReal ((ε / ‖a‖) ^ 2) := by
      rw [Complex.volume_ball]
      simp only [r, ENNReal.ofReal_pow hr]
      rw [mul_comm (ENNReal.ofReal (ε / ‖a‖) ^ 2) (NNReal.pi : ℝ≥0∞)]
      exact ENNReal.inv_mul_cancel_left (ENNReal.coe_ne_zero.mpr NNReal.pi_ne_zero)
        ENNReal.coe_ne_top

end

end CofiniteDerivatives
