import Wikipedia.SmoothSixDPoincare.MorseHandleModel
import Mathlib.Topology.Order.IntermediateValue

/-!
# Radial change from belt coordinates to the positive handle face

Following the quadratic descent flow from the upper level to the positive
face multiplies the negative disk coordinate by `sqrt (1 + ‖u‖²) / sqrt 2`.
This is an actual homeomorphism of the whole closed disk, fixed on its sphere.
-/

noncomputable section

open Set Metric

namespace Wikipedia.SmoothSixDPoincare.MorseHandle

/-- The positive radial factor in the negative-coordinate change. -/
def beltFaceScale (r : ℝ) : ℝ := Real.sqrt (1 + r ^ 2) / Real.sqrt 2

theorem beltFaceScale_pos (r : ℝ) : 0 < beltFaceScale r :=
  div_pos (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_pos.mpr (by norm_num))

theorem continuous_beltFaceScale : Continuous beltFaceScale :=
  (Real.continuous_sqrt.comp (continuous_const.add (continuous_id.pow 2))).div_const _

theorem beltFaceScale_one : beltFaceScale 1 = 1 := by
  simp only [beltFaceScale, one_pow, one_add_one_eq_two]
  exact div_self (Real.sqrt_pos.mpr (by norm_num)).ne'

theorem beltFaceScale_monotone : MonotoneOn beltFaceScale (Ici 0) := by
  intro r hr s hs hrs
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg 2)
  apply Real.sqrt_le_sqrt
  have hsq : r ^ 2 ≤ s ^ 2 := (sq_le_sq₀ hr hs).mpr hrs
  linarith

theorem beltFaceRadius_strictMono :
    StrictMonoOn (fun r => beltFaceScale r * r) (Ici 0) := by
  intro r hr s hs hrs
  exact (mul_lt_mul_of_pos_left hrs (beltFaceScale_pos r)).trans_le
    (mul_le_mul_of_nonneg_right (beltFaceScale_monotone hr hs hrs.le) hs)

variable {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]

/-- Negative coordinates on the positive handle face. -/
def beltFaceMap (u : N) : N := beltFaceScale ‖u‖ • u

theorem continuous_beltFaceMap : Continuous (beltFaceMap (N := N)) :=
  (continuous_beltFaceScale.comp continuous_norm).smul continuous_id

theorem norm_beltFaceMap (u : N) :
    ‖beltFaceMap u‖ = beltFaceScale ‖u‖ * ‖u‖ := by
  rw [beltFaceMap, norm_smul, Real.norm_eq_abs, abs_of_pos (beltFaceScale_pos _)]

theorem beltFaceMap_zero : beltFaceMap (0 : N) = 0 := by
  simp only [beltFaceMap, smul_zero]

theorem beltFaceMap_eq_self_of_norm_eq_one {u : N} (hu : ‖u‖ = 1) :
    beltFaceMap u = u := by
  rw [beltFaceMap, hu, beltFaceScale_one, one_smul]

theorem norm_beltFaceMap_lt_one_iff (u : N) : ‖beltFaceMap u‖ < 1 ↔ ‖u‖ < 1 := by
  have hh := beltFaceRadius_strictMono.lt_iff_lt (norm_nonneg u) (show 0 ≤ (1 : ℝ) by norm_num)
  simpa only [beltFaceScale_one, mul_one, norm_beltFaceMap] using hh

theorem beltFaceMap_mem_disk {u : N} (hu : ‖u‖ ≤ 1) : ‖beltFaceMap u‖ ≤ 1 := by
  rw [norm_beltFaceMap]
  have hs : beltFaceScale ‖u‖ ≤ 1 := by
    rw [← beltFaceScale_one]
    exact beltFaceScale_monotone (norm_nonneg u) (by norm_num) hu
  exact (mul_le_mul_of_nonneg_right hs (norm_nonneg u)).trans (by simpa only [one_mul])

theorem beltFaceMap_injective : Function.Injective (beltFaceMap (N := N)) := by
  intro u v huv
  have hn : ‖u‖ = ‖v‖ := by
    apply beltFaceRadius_strictMono.injOn (norm_nonneg u) (norm_nonneg v)
    simpa only [norm_beltFaceMap] using congrArg norm huv
  change beltFaceScale ‖u‖ • u = beltFaceScale ‖v‖ • v at huv
  rw [hn] at huv
  exact (smul_right_injective N (beltFaceScale_pos ‖v‖).ne') huv

/-- Every closed-disk coordinate is reached by this radial change. -/
theorem beltFaceMap_surjOn_disk :
    SurjOn (beltFaceMap (N := N)) (closedBall 0 1) (closedBall 0 1) := by
  intro v hv
  by_cases hvzero : v = 0
  · subst v
    exact ⟨0, mem_closedBall_zero_iff.mpr (by norm_num), beltFaceMap_zero⟩
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hvzero
  have hvrange : ‖v‖ ∈ Icc
      (beltFaceScale 0 * 0) (beltFaceScale 1 * 1) := by
    simpa only [mul_zero, beltFaceScale_one, mul_one, mem_Icc] using
      And.intro hvpos.le (mem_closedBall_zero_iff.mp hv)
  obtain ⟨r, hr, hrv⟩ := intermediate_value_Icc (a := (0 : ℝ)) (b := 1) (by norm_num)
    (continuous_beltFaceScale.mul continuous_id).continuousOn hvrange
  change beltFaceScale r * r = ‖v‖ at hrv
  let u : N := (r / ‖v‖) • v
  have hnorm : ‖u‖ = r := by
    change ‖(r / ‖v‖) • v‖ = r
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr.1 hvpos.le),
      div_mul_cancel₀ _ hvpos.ne']
  refine ⟨u, mem_closedBall_zero_iff.mpr (hnorm ▸ hr.2), ?_⟩
  change beltFaceScale ‖u‖ • ((r / ‖v‖) • v) = v
  rw [hnorm, smul_smul, ← mul_div_assoc, hrv, div_self hvpos.ne', one_smul]

/-- The whole negative disk, expressed in positive-face coordinates. -/
def beltFaceDiskMap : UnitDisk N → UnitDisk N := fun u =>
  ⟨beltFaceMap u.val, mem_closedBall_zero_iff.mpr
    (beltFaceMap_mem_disk (mem_closedBall_zero_iff.mp u.property))⟩

theorem continuous_beltFaceDiskMap : Continuous (beltFaceDiskMap (N := N)) :=
  (continuous_beltFaceMap.comp continuous_subtype_val).subtype_mk _

theorem beltFaceDiskMap_bijective : Function.Bijective (beltFaceDiskMap (N := N)) := by
  constructor
  · intro u v huv
    exact Subtype.ext (beltFaceMap_injective (congrArg Subtype.val huv))
  · intro v
    obtain ⟨u, hu, huv⟩ := beltFaceMap_surjOn_disk v.property
    exact ⟨⟨u, hu⟩, Subtype.ext huv⟩

/-- The radial coordinate change is a homeomorphism, including at the center. -/
def beltFaceDiskHomeomorph [FiniteDimensional ℝ N] : UnitDisk N ≃ₜ UnitDisk N :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective beltFaceDiskMap beltFaceDiskMap_bijective)
    continuous_beltFaceDiskMap

theorem beltFaceDiskHomeomorph_apply [FiniteDimensional ℝ N] (u : UnitDisk N) :
    (beltFaceDiskHomeomorph u).val = beltFaceMap u.val := rfl

theorem beltFaceDiskHomeomorph_boundary [FiniteDimensional ℝ N]
    (u : UnitDisk N) (hu : ‖u.val‖ = 1) : beltFaceDiskHomeomorph u = u :=
  Subtype.ext (beltFaceMap_eq_self_of_norm_eq_one hu)

end Wikipedia.SmoothSixDPoincare.MorseHandle
