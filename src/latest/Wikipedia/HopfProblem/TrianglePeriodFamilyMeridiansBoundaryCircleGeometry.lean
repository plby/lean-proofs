import Wikipedia.HopfProblem.TrianglePeriodFamilyMeridiansSides
import Wikipedia.HopfProblem.TriangleClosedDomainBoundaryGeometry
import Wikipedia.HopfProblem.TriangleClosedDomainFinite

/-!
# The actual circular side of the half-Ford triangle

Linear interpolation of the real coordinates of the two elliptic centers,
with the positive semicircle height, gives a continuous injective path in
the actual closed half-Ford region.  Its image is exactly the circular
side, including both endpoints.
-/

noncomputable section

open Set UpperHalfPlane

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians

open SpecialPeriods SpecialPeriods.Triangle

private theorem circle_left_re_lt_right_re : centerTwo.re < centerOne.re := by
  change (centerTwo : ℂ).re < (centerOne : ℂ).re
  rw [centerTwo_coe_re, centerOne_coe_re]
  exact stripLeft_lt_right

/-- The real coordinate traverses the circular side from the first center
to the second center. -/
def halfFordCircleReal (t : unitInterval) : ℝ :=
  (1 - (t : ℝ)) * centerOne.re + (t : ℝ) * centerTwo.re

@[fun_prop] theorem halfFordCircleReal_continuous : Continuous halfFordCircleReal := by
  unfold halfFordCircleReal
  fun_prop

theorem halfFordCircleReal_strictAnti : StrictAnti halfFordCircleReal := by
  intro s t hst
  have ht : (s : ℝ) < (t : ℝ) := hst
  have hp := mul_pos (sub_pos.mpr ht) (sub_pos.mpr circle_left_re_lt_right_re)
  dsimp only [halfFordCircleReal]
  nlinarith

theorem halfFordCircleReal_mem (t : unitInterval) :
    halfFordCircleReal t ∈ Icc stripLeft (-1 / 2) := by
  have hbounds : centerTwo.re ≤ halfFordCircleReal t ∧
      halfFordCircleReal t ≤ centerOne.re := by
    constructor
    · dsimp only [halfFordCircleReal]
      nlinarith [mul_nonneg (sub_nonneg.mpr t.property.2)
        (sub_nonneg.mpr circle_left_re_lt_right_re.le)]
    · dsimp only [halfFordCircleReal]
      nlinarith [mul_nonneg t.property.1 (sub_nonneg.mpr circle_left_re_lt_right_re.le)]
  have h₁ : centerOne.re = -1 / 2 := centerOne_coe_re
  have h₂ : centerTwo.re = stripLeft := centerTwo_coe_re
  simpa only [mem_Icc, h₁, h₂] using hbounds

private theorem boundaryCircle_norm (x : ℝ) (hl : stripLeft ≤ x) (hr : x ≤ -1 / 2) :
    ‖(⟨x, boundaryHeight x⟩ : ℂ) + 1‖ = 1 := by
  have hs : boundaryHeight x ^ 2 = 1 - (x + 1) ^ 2 :=
    Real.sq_sqrt (Real.sqrt_pos.mp (boundaryHeight_pos_of_closed_bounds hl hr)).le
  apply (sq_eq_sq₀ (norm_nonneg _) (show (0 : ℝ) ≤ 1 by norm_num)).mp
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, add_zero, one_pow]
  nlinarith

/-- The actual point on the positive circular boundary, as a point of the
original closed half-Ford region. -/
def halfFordCirclePoint (t : unitInterval) : halfFordRegion :=
  ⟨⟨⟨halfFordCircleReal t, boundaryHeight (halfFordCircleReal t)⟩,
    boundaryHeight_pos_of_closed_bounds (halfFordCircleReal_mem t).1
      (halfFordCircleReal_mem t).2⟩, by
    apply (coe_mem_triangleClosedRegion_iff_halfFordRegion _).mp
    apply (mem_triangleClosedRegion_iff_epigraph _).mpr
    exact ⟨(halfFordCircleReal_mem t).1, (halfFordCircleReal_mem t).2, le_rfl⟩⟩

@[simp] theorem halfFordCirclePoint_coe (t : unitInterval) :
    ((halfFordCirclePoint t : ℍ) : ℂ) =
      ⟨halfFordCircleReal t, boundaryHeight (halfFordCircleReal t)⟩ := rfl

@[simp] theorem halfFordCirclePoint_re (t : unitInterval) :
    (halfFordCirclePoint t : ℍ).re =
      (1 - (t : ℝ)) * centerOne.re + (t : ℝ) * centerTwo.re := rfl

@[simp] theorem halfFordCirclePoint_im (t : unitInterval) :
    (halfFordCirclePoint t : ℍ).im = boundaryHeight (halfFordCirclePoint t : ℍ).re := rfl

theorem halfFordCirclePoint_continuous : Continuous halfFordCirclePoint := by
  have hc : Continuous (fun t : unitInterval =>
      (⟨halfFordCircleReal t, boundaryHeight (halfFordCircleReal t)⟩ : ℂ)) := by
    simp_rw [Complex.mk_eq_add_mul_I]
    exact (Complex.continuous_ofReal.comp halfFordCircleReal_continuous).add
      ((Complex.continuous_ofReal.comp
        (continuous_boundaryHeight.comp halfFordCircleReal_continuous)).mul continuous_const)
  exact (hc.upperHalfPlaneMk _).subtype_mk _

@[simp] theorem halfFordCirclePoint_norm_add_one (t : unitInterval) :
    ‖((halfFordCirclePoint t : ℍ) : ℂ) + 1‖ = 1 :=
  boundaryCircle_norm _ (halfFordCircleReal_mem t).1 (halfFordCircleReal_mem t).2

@[simp] theorem halfFordCirclePoint_zero :
    halfFordCirclePoint 0 =
      (⟨centerOne, centerOne_mem_halfFordRegion⟩ : halfFordRegion) := by
  apply Subtype.ext
  apply UpperHalfPlane.ext
  apply complex_eq_of_re_eq_norm_add_one_eq
  · change (1 - (0 : ℝ)) * centerOne.re + 0 * centerTwo.re = centerOne.re
    simp
  · exact (halfFordCirclePoint 0 : ℍ).im_pos
  · exact centerOne.im_pos
  · rw [halfFordCirclePoint_norm_add_one, centerOne_norm_add_one]

@[simp] theorem halfFordCirclePoint_one :
    halfFordCirclePoint 1 =
      (⟨centerTwo, centerTwo_mem_halfFordRegion⟩ : halfFordRegion) := by
  apply Subtype.ext
  apply UpperHalfPlane.ext
  apply complex_eq_of_re_eq_norm_add_one_eq
  · change (1 - (1 : ℝ)) * centerOne.re + 1 * centerTwo.re = centerTwo.re
    simp
  · exact (halfFordCirclePoint 1 : ℍ).im_pos
  · exact centerTwo.im_pos
  · rw [halfFordCirclePoint_norm_add_one, centerTwo_norm_add_one]

theorem halfFordCirclePoint_injective : Function.Injective halfFordCirclePoint := by
  intro s t h
  apply halfFordCircleReal_strictAnti.injective
  exact congrArg (fun z : halfFordRegion => (z : ℍ).re) h

/-- Every point of the circular side occurs, including the two elliptic
endpoints; no other boundary points occur. -/
theorem halfFordCirclePoint_range :
    range halfFordCirclePoint =
      {z : halfFordRegion | ‖((z : ℍ) : ℂ) + 1‖ = 1} := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact halfFordCirclePoint_norm_add_one t
  · intro hz
    have hclosed := (coe_mem_triangleClosedRegion_iff_halfFordRegion (z : ℍ)).mpr z.property
    have hl : centerTwo.re ≤ (z : ℍ).re := by
      change (centerTwo : ℂ).re ≤ ((z : ℍ) : ℂ).re
      rw [centerTwo_coe_re]
      exact hclosed.1
    have hr : (z : ℍ).re ≤ centerOne.re := by
      change ((z : ℍ) : ℂ).re ≤ (centerOne : ℂ).re
      rw [centerOne_coe_re]
      exact hclosed.2.1
    have hd : 0 < centerOne.re - centerTwo.re := sub_pos.mpr circle_left_re_lt_right_re
    let t : unitInterval :=
      ⟨(centerOne.re - (z : ℍ).re) / (centerOne.re - centerTwo.re),
        div_nonneg (sub_nonneg.mpr hr) hd.le,
        (div_le_one hd).mpr (by linarith)⟩
    have ht : halfFordCircleReal t = (z : ℍ).re := by
      dsimp only [halfFordCircleReal, t]
      field_simp [hd.ne']
      ring
    refine ⟨t, ?_⟩
    apply Subtype.ext
    apply UpperHalfPlane.ext
    apply complex_eq_of_re_eq_norm_add_one_eq
    · exact ht
    · exact (halfFordCirclePoint t : ℍ).im_pos
    · exact (z : ℍ).im_pos
    · exact (halfFordCirclePoint_norm_add_one t).trans hz.symm

/-- The complete circular boundary side as an actual path in the closed
half-Ford region, oriented from the order-three to the order-four center. -/
def halfFordCirclePath :
    Path (⟨centerOne, centerOne_mem_halfFordRegion⟩ : halfFordRegion)
      ⟨centerTwo, centerTwo_mem_halfFordRegion⟩ where
  toFun := halfFordCirclePoint
  continuous_toFun := halfFordCirclePoint_continuous
  source' := halfFordCirclePoint_zero
  target' := halfFordCirclePoint_one

@[simp] theorem halfFordCirclePath_apply (t : unitInterval) :
    halfFordCirclePath t = halfFordCirclePoint t := rfl

theorem halfFordCirclePath_injective : Function.Injective halfFordCirclePath :=
  halfFordCirclePoint_injective

theorem halfFordCirclePath_range :
    range halfFordCirclePath =
      {z : halfFordRegion | ‖((z : ℍ) : ℂ) + 1‖ = 1} :=
  halfFordCirclePoint_range

end Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians
