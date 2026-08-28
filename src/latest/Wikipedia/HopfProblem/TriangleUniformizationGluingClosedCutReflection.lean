import Wikipedia.HopfProblem.TriangleUniformizationGluingClosedSectors
import Wikipedia.HopfProblem.SpecialPeriodsTriangleTilingReflections

/-!
# Circle reflection preserves the closed cyclic sectors

The actual reflection in `‖z + 1‖ = 1` exchanges the two inequalities
defining each closed cyclic sector. Involutivity turns the real-coordinate
calculation into the complementary norm calculation, including equality
along the boundary. Consequently it preserves the closed circular double.
-/

noncomputable section

open Set UpperHalfPlane
open scoped ComplexConjugate

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

theorem circleReflection_re (z : ℍ) :
    (circleReflection z).re =
      -1 + (z.re + 1) / Complex.normSq ((z : ℂ) + 1) := by
  change (-1 + 1 / (conj (z : ℂ) + 1)).re = _
  rw [show conj (z : ℂ) + 1 = conj ((z : ℂ) + 1) by simp]
  simp only [one_div, Complex.add_re, Complex.neg_re, Complex.one_re,
    Complex.inv_re, Complex.conj_re, Complex.normSq_conj, UpperHalfPlane.coe_re]

/-- Reflection exchanges the first sector's straight and circular sides. -/
theorem circleReflection_re_le_neg_half_iff (z : ℍ) :
    (circleReflection z).re ≤ -(1 / 2) ↔ 1 ≤ ‖(z : ℂ)‖ := by
  have hd := Complex.normSq_pos.mpr (denominatorOne_ne_zero z)
  calc
    (circleReflection z).re ≤ -(1 / 2) ↔
        (z.re + 1) / Complex.normSq ((z : ℂ) + 1) ≤ 1 / 2 := by
      rw [circleReflection_re]
      constructor <;> intro h <;> linarith
    _ ↔ z.re + 1 ≤ (1 / 2) * Complex.normSq ((z : ℂ) + 1) :=
      div_le_iff₀ hd
    _ ↔ (1 : ℝ) ^ 2 ≤ ‖(z : ℂ)‖ ^ 2 := by
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re,
        Complex.one_re, Complex.add_im, Complex.one_im, add_zero,
        UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      constructor <;> intro h <;> nlinarith
    _ ↔ 1 ≤ ‖(z : ℂ)‖ := sq_le_sq₀ (by norm_num) (norm_nonneg _)

theorem one_le_circleReflection_norm_iff (z : ℍ) :
    1 ≤ ‖(circleReflection z : ℂ)‖ ↔ z.re ≤ -(1 / 2) := by
  simpa only [circleReflection_involutive z] using
    (circleReflection_re_le_neg_half_iff (circleReflection z)).symm

/-- The radius relation `stripRight² = 1/2` makes the second sector's
straight and circular inequalities exchange under the same reflection. -/
theorem circleReflection_re_ge_stripLeft_iff (z : ℍ) :
    stripLeft ≤ (circleReflection z).re ↔
      stripRight ≤ ‖(z : ℂ) - (stripLeft : ℂ)‖ := by
  have hd := Complex.normSq_pos.mpr (denominatorOne_ne_zero z)
  have hL : stripLeft = -stripRight - 1 := by
    linarith [stripLeft_add_stripRight]
  have he : stripRight *
      (‖(z : ℂ) - (stripLeft : ℂ)‖ ^ 2 - stripRight ^ 2) =
      z.re + 1 + stripRight * Complex.normSq ((z : ℂ) + 1) := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero,
      Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
      add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, hL]
    linear_combination (2 * z.re + 2) * stripRight_sq
  calc
    stripLeft ≤ (circleReflection z).re ↔
        -stripRight ≤ (z.re + 1) / Complex.normSq ((z : ℂ) + 1) := by
      rw [circleReflection_re, hL]
      constructor <;> intro h <;> linarith
    _ ↔ -stripRight * Complex.normSq ((z : ℂ) + 1) ≤ z.re + 1 :=
      le_div_iff₀ hd
    _ ↔ 0 ≤ z.re + 1 + stripRight * Complex.normSq ((z : ℂ) + 1) := by
      constructor <;> intro h <;> linarith
    _ ↔ 0 ≤ stripRight *
        (‖(z : ℂ) - (stripLeft : ℂ)‖ ^ 2 - stripRight ^ 2) := by rw [he]
    _ ↔ 0 ≤ ‖(z : ℂ) - (stripLeft : ℂ)‖ ^ 2 - stripRight ^ 2 :=
      mul_nonneg_iff_of_pos_left stripRight_pos
    _ ↔ stripRight ^ 2 ≤ ‖(z : ℂ) - (stripLeft : ℂ)‖ ^ 2 := sub_nonneg
    _ ↔ stripRight ≤ ‖(z : ℂ) - (stripLeft : ℂ)‖ :=
      sq_le_sq₀ stripRight_pos.le (norm_nonneg _)

theorem stripRight_le_circleReflection_sub_stripLeft_norm_iff (z : ℍ) :
    stripRight ≤ ‖(circleReflection z : ℂ) - (stripLeft : ℂ)‖ ↔
      stripLeft ≤ z.re := by
  simpa only [circleReflection_involutive z] using
    (circleReflection_re_ge_stripLeft_iff (circleReflection z)).symm

@[simp] theorem circleReflection_mem_closedFirstSector_iff (z : ℍ) :
    circleReflection z ∈ closedFirstSector ↔ z ∈ closedFirstSector := by
  change (circleReflection z).re ≤ -(1 / 2) ∧
      1 ≤ ‖(circleReflection z : ℂ)‖ ↔ z.re ≤ -(1 / 2) ∧ 1 ≤ ‖(z : ℂ)‖
  rw [circleReflection_re_le_neg_half_iff, one_le_circleReflection_norm_iff, and_comm]

@[simp] theorem circleReflection_mem_closedSecondSector_iff (z : ℍ) :
    circleReflection z ∈ closedSecondSector ↔ z ∈ closedSecondSector := by
  change stripLeft ≤ (circleReflection z).re ∧
      stripRight ≤ ‖(circleReflection z : ℂ) - (stripLeft : ℂ)‖ ↔
      stripLeft ≤ z.re ∧ stripRight ≤ ‖(z : ℂ) - (stripLeft : ℂ)‖
  rw [circleReflection_re_ge_stripLeft_iff,
    stripRight_le_circleReflection_sub_stripLeft_norm_iff, and_comm]

@[simp] theorem circleReflection_mem_circularDoubleRegion_iff (z : ℍ) :
    circleReflection z ∈ circularDoubleRegion ↔ z ∈ circularDoubleRegion := by
  simp only [circularDoubleRegion, mem_inter_iff,
    circleReflection_mem_closedFirstSector_iff, circleReflection_mem_closedSecondSector_iff]

theorem circleReflection_mapsTo_closedFirstSector :
    MapsTo circleReflection closedFirstSector closedFirstSector :=
  fun z hz => (circleReflection_mem_closedFirstSector_iff z).mpr hz

theorem circleReflection_mapsTo_closedSecondSector :
    MapsTo circleReflection closedSecondSector closedSecondSector :=
  fun z hz => (circleReflection_mem_closedSecondSector_iff z).mpr hz

theorem circleReflection_mapsTo_circularDoubleRegion :
    MapsTo circleReflection circularDoubleRegion circularDoubleRegion :=
  fun z hz => (circleReflection_mem_circularDoubleRegion_iff z).mpr hz

theorem circleReflection_image_closedFirstSector :
    circleReflection '' closedFirstSector = closedFirstSector := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact circleReflection_mapsTo_closedFirstSector hw
  · intro hz
    exact ⟨circleReflection z, circleReflection_mapsTo_closedFirstSector hz,
      circleReflection_involutive z⟩

theorem circleReflection_image_closedSecondSector :
    circleReflection '' closedSecondSector = closedSecondSector := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact circleReflection_mapsTo_closedSecondSector hw
  · intro hz
    exact ⟨circleReflection z, circleReflection_mapsTo_closedSecondSector hz,
      circleReflection_involutive z⟩

theorem circleReflection_image_circularDoubleRegion :
    circleReflection '' circularDoubleRegion = circularDoubleRegion := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact circleReflection_mapsTo_circularDoubleRegion hw
  · intro hz
    exact ⟨circleReflection z, circleReflection_mapsTo_circularDoubleRegion hz,
      circleReflection_involutive z⟩

/-- Circle reflection reciprocates distance from its real center `-1`. -/
@[simp] theorem circleReflection_add_one_norm (z : ℍ) :
    ‖(circleReflection z : ℂ) + 1‖ = 1 / ‖(z : ℂ) + 1‖ := by
  rw [circleReflection_coe]
  have he : (-1 : ℂ) + 1 / (conj (z : ℂ) + 1) + 1 =
      1 / (conj (z : ℂ) + 1) := by ring
  rw [he, norm_div, norm_one,
    show conj (z : ℂ) + 1 = conj ((z : ℂ) + 1) by simp, Complex.norm_conj]

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
