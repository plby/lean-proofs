import Wikipedia.HopfProblem.TrianglePeriodFamilyMeridiansBoundaryNormalizationCore
import Wikipedia.HopfProblem.TrianglePeriodFamilyMeridiansBoundaryParameter
import Mathlib.Topology.Order.IntermediateValue

/-!
# Actual normalized images of the three half-Ford boundary sides

The explicit finite-boundary parametrization is continuous and injective.
After the existing normalization its values are real, still continuous and
injective, and the two vertices have values zero and one.  The intermediate
value theorem therefore forces the real coordinate to be strictly increasing.
The three side images follow, without an additional orientation hypothesis.
-/

noncomputable section

open Set Topology UpperHalfPlane

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians

open SpecialPeriods SpecialPeriods.Triangle RiemannMapping

private theorem halfFordBoundaryParam_mem_boundary (t : ℝ) :
    (halfFordBoundaryParam t : ℍ) ∉ halfFordInterior := by
  change halfFordBoundaryParam t ∈ {z : halfFordRegion | (z : ℍ) ∉ halfFordInterior}
  rw [← halfFordBoundaryParam_range]
  exact mem_range_self t

/-- The actual normalized real coordinate along the explicit boundary. -/
def halfFordNormalizedBoundaryParam (t : ℝ) : ℝ :=
  halfFordBoundaryValue (halfFordBoundaryParam t)

theorem halfFordNormalizedBoundaryParam_continuous :
    Continuous halfFordNormalizedBoundaryParam :=
  halfFordBoundaryValue_continuous.comp continuous_halfFordBoundaryParam

theorem halfFordNormalizedBoundaryParam_injective :
    Function.Injective halfFordNormalizedBoundaryParam := by
  intro s t h
  apply halfFordBoundaryParam_injective
  exact halfFordBoundaryValue_injOn (halfFordBoundaryParam_mem_boundary s)
    (halfFordBoundaryParam_mem_boundary t) h

@[simp] theorem halfFordNormalizedBoundaryParam_zero :
    halfFordNormalizedBoundaryParam 0 = 0 := by
  rw [halfFordNormalizedBoundaryParam, halfFordBoundaryParam_zero,
    halfFordBoundaryValue_centerOne]

@[simp] theorem halfFordNormalizedBoundaryParam_one :
    halfFordNormalizedBoundaryParam 1 = 1 := by
  rw [halfFordNormalizedBoundaryParam, halfFordBoundaryParam_one,
    halfFordBoundaryValue_centerTwo]

/-- The marked values force the boundary order; no orientation of the
normalized half-plane is assumed. -/
theorem halfFordNormalizedBoundaryParam_strictMono :
    StrictMono halfFordNormalizedBoundaryParam := by
  apply (halfFordNormalizedBoundaryParam_continuous.strictMono_of_inj
    halfFordNormalizedBoundaryParam_injective).resolve_right
  intro h
  have hh := h (show (0 : ℝ) < 1 by norm_num)
  rw [halfFordNormalizedBoundaryParam_zero, halfFordNormalizedBoundaryParam_one] at hh
  linarith

theorem halfFordNormalizedBoundaryParam_surjective :
    Function.Surjective halfFordNormalizedBoundaryParam := by
  intro x
  have hx : halfFordRealPreimage x ∈ range halfFordBoundaryParam := by
    rw [halfFordBoundaryParam_range]
    exact halfFordRealPreimage_not_mem_interior x
  obtain ⟨t, ht⟩ := hx
  refine ⟨t, ?_⟩
  rw [halfFordNormalizedBoundaryParam, ht, halfFordBoundaryValue_realPreimage]

theorem halfFordRealPreimage_normalizedBoundaryParam (t : ℝ) :
    halfFordRealPreimage (halfFordNormalizedBoundaryParam t) = halfFordBoundaryParam t :=
  halfFordRealPreimage_boundaryValue _ (halfFordBoundaryParam_mem_boundary t)

/-- The right vertical boundary is exactly the nonpositive real ray. -/
theorem halfFordBoundaryValue_right_iff (z : halfFordRegion)
    (hz : (z : ℍ) ∉ halfFordInterior) :
    (z : ℍ).re = -(1 / 2) ↔ halfFordBoundaryValue z ≤ 0 := by
  have hm : z ∈ range halfFordBoundaryParam := by
    rw [halfFordBoundaryParam_range]
    exact hz
  obtain ⟨t, rfl⟩ := hm
  rw [halfFordBoundaryParam_re_eq_right_iff]
  change t ≤ 0 ↔ halfFordNormalizedBoundaryParam t ≤ 0
  simpa only [halfFordNormalizedBoundaryParam_zero] using
    (halfFordNormalizedBoundaryParam_strictMono.le_iff_le (a := t) (b := 0)).symm

/-- The left vertical boundary is exactly the real ray starting at one. -/
theorem halfFordBoundaryValue_left_iff (z : halfFordRegion)
    (hz : (z : ℍ) ∉ halfFordInterior) :
    (z : ℍ).re = stripLeft ↔ 1 ≤ halfFordBoundaryValue z := by
  have hm : z ∈ range halfFordBoundaryParam := by
    rw [halfFordBoundaryParam_range]
    exact hz
  obtain ⟨t, rfl⟩ := hm
  rw [halfFordBoundaryParam_re_eq_left_iff]
  change 1 ≤ t ↔ 1 ≤ halfFordNormalizedBoundaryParam t
  simpa only [halfFordNormalizedBoundaryParam_one] using
    (halfFordNormalizedBoundaryParam_strictMono.le_iff_le (a := 1) (b := t)).symm

/-- The circular boundary arc is exactly the real interval between the
two marked finite values. -/
theorem halfFordBoundaryValue_circle_iff (z : halfFordRegion)
    (hz : (z : ℍ) ∉ halfFordInterior) :
    ‖((z : ℍ) : ℂ) + 1‖ = 1 ↔ halfFordBoundaryValue z ∈ Icc (0 : ℝ) 1 := by
  have hm : z ∈ range halfFordBoundaryParam := by
    rw [halfFordBoundaryParam_range]
    exact hz
  obtain ⟨t, rfl⟩ := hm
  rw [halfFordBoundaryParam_norm_add_one_eq_one_iff]
  change (0 ≤ t ∧ t ≤ 1) ↔
    (0 ≤ halfFordNormalizedBoundaryParam t ∧ halfFordNormalizedBoundaryParam t ≤ 1)
  apply and_congr
  · simpa only [halfFordNormalizedBoundaryParam_zero] using
      (halfFordNormalizedBoundaryParam_strictMono.le_iff_le (a := 0) (b := t)).symm
  · simpa only [halfFordNormalizedBoundaryParam_one] using
      (halfFordNormalizedBoundaryParam_strictMono.le_iff_le (a := t) (b := 1)).symm

theorem halfFordRealPreimage_re_eq_right_iff (x : ℝ) :
    (halfFordRealPreimage x : ℍ).re = -(1 / 2) ↔ x ≤ 0 := by
  simpa only [halfFordBoundaryValue_realPreimage] using
    halfFordBoundaryValue_right_iff (halfFordRealPreimage x)
      (halfFordRealPreimage_not_mem_interior x)

theorem halfFordRealPreimage_re_eq_left_iff (x : ℝ) :
    (halfFordRealPreimage x : ℍ).re = stripLeft ↔ 1 ≤ x := by
  simpa only [halfFordBoundaryValue_realPreimage] using
    halfFordBoundaryValue_left_iff (halfFordRealPreimage x)
      (halfFordRealPreimage_not_mem_interior x)

theorem halfFordRealPreimage_norm_add_one_eq_one_iff (x : ℝ) :
    ‖((halfFordRealPreimage x : ℍ) : ℂ) + 1‖ = 1 ↔ x ∈ Icc (0 : ℝ) 1 := by
  simpa only [halfFordBoundaryValue_realPreimage] using
    halfFordBoundaryValue_circle_iff (halfFordRealPreimage x)
      (halfFordRealPreimage_not_mem_interior x)

/-- Removing the first vertex makes the right ray strictly negative. -/
theorem halfFordRealPreimage_mem_openRightSide_iff (x : ℝ) :
    ((halfFordRealPreimage x : ℍ) : ℂ) ∈ triangleOpenRightSide ↔ x < 0 := by
  constructor
  · intro h
    have hr : (halfFordRealPreimage x : ℍ).re = -(1 / 2) := by
      simpa only [UpperHalfPlane.coe_re, neg_div] using h.1
    have hx := (halfFordRealPreimage_re_eq_right_iff x).mp hr
    apply lt_of_le_of_ne hx
    intro he
    have hn := (halfFordRealPreimage_norm_add_one_eq_one_iff x).mpr
      (show x ∈ Icc (0 : ℝ) 1 by rw [he]; norm_num)
    exact (ne_of_gt h.2.2) hn
  · intro hx
    refine ⟨?_, (halfFordRealPreimage x : ℍ).im_pos, ?_⟩
    · simpa only [UpperHalfPlane.coe_re, neg_div] using
        (halfFordRealPreimage_re_eq_right_iff x).mpr hx.le
    · apply lt_of_le_of_ne (halfFordRealPreimage x).property.1.2.2.1
      intro hn
      have hh := (halfFordRealPreimage_norm_add_one_eq_one_iff x).mp hn.symm
      exact (not_le_of_gt hx) hh.1

/-- Removing the second vertex makes the left ray strictly greater than one. -/
theorem halfFordRealPreimage_mem_openLeftSide_iff (x : ℝ) :
    ((halfFordRealPreimage x : ℍ) : ℂ) ∈ triangleOpenLeftSide ↔ 1 < x := by
  constructor
  · intro h
    have hx := (halfFordRealPreimage_re_eq_left_iff x).mp h.1
    apply lt_of_le_of_ne hx
    intro he
    have hn := (halfFordRealPreimage_norm_add_one_eq_one_iff x).mpr
      (show x ∈ Icc (0 : ℝ) 1 by rw [← he]; norm_num)
    exact (ne_of_gt h.2.2) hn
  · intro hx
    refine ⟨(halfFordRealPreimage_re_eq_left_iff x).mpr hx.le,
      (halfFordRealPreimage x : ℍ).im_pos, ?_⟩
    apply lt_of_le_of_ne (halfFordRealPreimage x).property.1.2.2.1
    intro hn
    have hh := (halfFordRealPreimage_norm_add_one_eq_one_iff x).mp hn.symm
    exact (not_le_of_gt hx) hh.2

/-- The open circular side is exactly the open real interval `(0,1)`. -/
theorem halfFordRealPreimage_mem_openCircleSide_iff (x : ℝ) :
    ((halfFordRealPreimage x : ℍ) : ℂ) ∈ triangleOpenCircleSide ↔ x ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · intro h
    constructor
    · by_contra hx
      have he := (halfFordRealPreimage_re_eq_right_iff x).mpr (le_of_not_gt hx)
      have hh := h.2.1
      change (halfFordRealPreimage x : ℍ).re < -1 / 2 at hh
      rw [he] at hh
      linarith
    · by_contra hx
      have he := (halfFordRealPreimage_re_eq_left_iff x).mpr (le_of_not_gt hx)
      have hh := h.1
      change stripLeft < (halfFordRealPreimage x : ℍ).re at hh
      rw [he] at hh
      exact lt_irrefl _ hh
  · intro hx
    have hz := (coe_mem_triangleClosedRegion_iff_halfFordRegion
      (halfFordRealPreimage x : ℍ)).mpr (halfFordRealPreimage x).property
    refine ⟨?_, ?_, (halfFordRealPreimage x : ℍ).im_pos,
      (halfFordRealPreimage_norm_add_one_eq_one_iff x).mpr ⟨hx.1.le, hx.2.le⟩⟩
    · apply lt_of_le_of_ne hz.1
      intro he
      have hh := (halfFordRealPreimage_re_eq_left_iff x).mp he.symm
      exact (not_le_of_gt hx.2) hh
    · apply lt_of_le_of_ne hz.2.1
      intro he
      have hr : (halfFordRealPreimage x : ℍ).re = -(1 / 2) := by
        simpa only [UpperHalfPlane.coe_re, neg_div] using he
      have hh := (halfFordRealPreimage_re_eq_right_iff x).mp hr
      exact (not_le_of_gt hx.1) hh

private theorem halfFord_boundary_of_right (z : halfFordRegion)
    (hz : (z : ℍ).re = -(1 / 2)) : (z : ℍ) ∉ halfFordInterior := by
  intro h
  have hh := h.2
  change (z : ℍ).re < -(1 / 2) at hh
  rw [hz] at hh
  exact lt_irrefl _ hh

private theorem halfFord_boundary_of_left (z : halfFordRegion)
    (hz : (z : ℍ).re = stripLeft) : (z : ℍ) ∉ halfFordInterior := by
  intro h
  have hh := h.1.1
  rw [hz] at hh
  exact lt_irrefl _ hh

private theorem halfFord_boundary_of_circle (z : halfFordRegion)
    (hz : ‖((z : ℍ) : ℂ) + 1‖ = 1) : (z : ℍ) ∉ halfFordInterior := by
  intro h
  have hh := h.1.2.2.1
  rw [hz] at hh
  exact lt_irrefl _ hh

/-- Exact image of the actual right vertical ray, including its vertex. -/
theorem halfFordNormalization_image_right :
    (fun z : halfFordRegion => (halfFordNormalizationHomeomorph z : ℂ)) ''
      {z | (z : ℍ).re = -(1 / 2)} = Complex.ofReal '' Iic (0 : ℝ) := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hb := halfFord_boundary_of_right z hz
    exact ⟨halfFordBoundaryValue z, (halfFordBoundaryValue_right_iff z hb).mp hz,
      halfFordBoundaryValue_coe z hb⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨halfFordRealPreimage x, (halfFordRealPreimage_re_eq_right_iff x).mpr hx,
      halfFordRealPreimage_normalization x⟩

/-- Exact image of the actual left vertical ray, including its vertex. -/
theorem halfFordNormalization_image_left :
    (fun z : halfFordRegion => (halfFordNormalizationHomeomorph z : ℂ)) ''
      {z | (z : ℍ).re = stripLeft} = Complex.ofReal '' Ici (1 : ℝ) := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hb := halfFord_boundary_of_left z hz
    exact ⟨halfFordBoundaryValue z, (halfFordBoundaryValue_left_iff z hb).mp hz,
      halfFordBoundaryValue_coe z hb⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨halfFordRealPreimage x, (halfFordRealPreimage_re_eq_left_iff x).mpr hx,
      halfFordRealPreimage_normalization x⟩

/-- Exact image of the actual circular side between the two vertices. -/
theorem halfFordNormalization_image_circle :
    (fun z : halfFordRegion => (halfFordNormalizationHomeomorph z : ℂ)) ''
      {z | ‖((z : ℍ) : ℂ) + 1‖ = 1} = Complex.ofReal '' Icc (0 : ℝ) 1 := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hb := halfFord_boundary_of_circle z hz
    exact ⟨halfFordBoundaryValue z, (halfFordBoundaryValue_circle_iff z hb).mp hz,
      halfFordBoundaryValue_coe z hb⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨halfFordRealPreimage x, (halfFordRealPreimage_norm_add_one_eq_one_iff x).mpr hx,
      halfFordRealPreimage_normalization x⟩

theorem halfFordRealPreimage_rightReflection (x : ℝ) (hx : x ≤ 0) :
    rightReflection (halfFordRealPreimage x : ℍ) = (halfFordRealPreimage x : ℍ) :=
  (rightReflection_fixed_iff _).mpr ((halfFordRealPreimage_re_eq_right_iff x).mpr hx)

theorem halfFordRealPreimage_leftReflection (x : ℝ) (hx : 1 ≤ x) :
    leftReflection (halfFordRealPreimage x : ℍ) = (halfFordRealPreimage x : ℍ) :=
  (leftReflection_fixed_iff _).mpr ((halfFordRealPreimage_re_eq_left_iff x).mpr hx)

theorem halfFordRealPreimage_circleReflection (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    circleReflection (halfFordRealPreimage x : ℍ) = (halfFordRealPreimage x : ℍ) :=
  (circleReflection_fixed_iff _).mpr
    ((halfFordRealPreimage_norm_add_one_eq_one_iff x).mpr hx)

end Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians
