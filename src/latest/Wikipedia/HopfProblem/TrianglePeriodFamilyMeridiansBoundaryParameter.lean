import Wikipedia.HopfProblem.TrianglePeriodFamilyMeridiansBoundaryCircleGeometry
import Wikipedia.HopfProblem.TrianglePeriodFamilyMeridiansSides

/-!
# A global parameter of the actual finite half-Ford boundary

The parameter traverses the right vertical side down to the first
elliptic centre, follows the circular side to the second centre, and
then traverses the left vertical side upwards.  Its range is the whole
finite boundary in the original upper-half-plane topology.
-/

noncomputable section

open Set UpperHalfPlane

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians

open SpecialPeriods SpecialPeriods.Triangle

private def boundaryRise (t : ℝ) : ℝ := max (-t) 0 + max (t - 1) 0

private theorem boundaryRise_nonneg (t : ℝ) : 0 ≤ boundaryRise t :=
  add_nonneg (le_max_right _ _) (le_max_right _ _)

private theorem boundaryRise_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    boundaryRise t = -t := by
  rw [boundaryRise, max_eq_left (by linarith), max_eq_right (by linarith), add_zero]

private theorem boundaryRise_of_unit {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    boundaryRise t = 0 := by
  rw [boundaryRise, max_eq_right (by linarith), max_eq_right (by linarith), add_zero]

private theorem boundaryRise_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    boundaryRise t = t - 1 := by
  rw [boundaryRise, max_eq_right (by linarith), max_eq_left (by linarith), zero_add]

/-- A single explicit real parameter of the three finite sides. -/
def halfFordBoundaryParam (t : ℝ) : halfFordRegion :=
  let a : halfFordRegion := halfFordCirclePath.extend t
  let z : ℍ := ⟨⟨(a : ℍ).re, (a : ℍ).im + boundaryRise t⟩,
    lt_of_lt_of_le (a : ℍ).im_pos (le_add_of_nonneg_right (boundaryRise_nonneg t))⟩
  ⟨z, halfFordRegion_vertical_mono a z a.property rfl
    (le_add_of_nonneg_right (boundaryRise_nonneg t))⟩

private theorem halfFordBoundaryParam_re (t : ℝ) :
    (halfFordBoundaryParam t : ℍ).re = (halfFordCirclePath.extend t : ℍ).re := rfl

private theorem halfFordBoundaryParam_im (t : ℝ) :
    (halfFordBoundaryParam t : ℍ).im =
      (halfFordCirclePath.extend t : ℍ).im + boundaryRise t := rfl

/-- Continuity is in the inherited topology of the actual closed region. -/
@[fun_prop] theorem continuous_halfFordBoundaryParam : Continuous halfFordBoundaryParam := by
  have hbase : Continuous (fun t : ℝ => (halfFordCirclePath.extend t : ℍ)) :=
    continuous_subtype_val.comp halfFordCirclePath.continuous_extend
  have hr : Continuous (fun t : ℝ => boundaryRise t) := by
    unfold boundaryRise
    fun_prop
  apply Continuous.subtype_mk
  apply Continuous.upperHalfPlaneMk
  simp_rw [Complex.mk_eq_add_mul_I]
  exact (Complex.continuous_ofReal.comp (UpperHalfPlane.continuous_re.comp hbase)).add
    ((Complex.continuous_ofReal.comp
      ((UpperHalfPlane.continuous_im.comp hbase).add hr)).mul continuous_const)

/-- The first parameter ray lies vertically over the order-three centre. -/
theorem halfFordBoundaryParam_re_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    (halfFordBoundaryParam t : ℍ).re = centerOne.re := by
  rw [halfFordBoundaryParam_re, halfFordCirclePath.extend_of_le_zero ht]

theorem halfFordBoundaryParam_im_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    (halfFordBoundaryParam t : ℍ).im = centerOne.im - t := by
  rw [halfFordBoundaryParam_im, halfFordCirclePath.extend_of_le_zero ht,
    boundaryRise_of_nonpos ht]
  rfl

/-- The middle parameter interval is literally the circular side path. -/
theorem halfFordBoundaryParam_eq_circle {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    halfFordBoundaryParam t = halfFordCirclePoint ⟨t, ht0, ht1⟩ := by
  apply Subtype.ext
  apply UpperHalfPlane.ext_re_im
  · rw [halfFordBoundaryParam_re, Path.extend_apply _ ⟨ht0, ht1⟩]
    rfl
  · rw [halfFordBoundaryParam_im, Path.extend_apply _ ⟨ht0, ht1⟩,
      boundaryRise_of_unit ht0 ht1, add_zero]
    rfl

/-- The last parameter ray lies vertically over the order-four centre. -/
theorem halfFordBoundaryParam_re_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    (halfFordBoundaryParam t : ℍ).re = centerTwo.re := by
  rw [halfFordBoundaryParam_re, halfFordCirclePath.extend_of_one_le ht]

theorem halfFordBoundaryParam_im_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    (halfFordBoundaryParam t : ℍ).im = centerTwo.im + t - 1 := by
  rw [halfFordBoundaryParam_im, halfFordCirclePath.extend_of_one_le ht,
    boundaryRise_of_one_le ht]
  ring

@[simp] theorem halfFordBoundaryParam_zero :
    halfFordBoundaryParam 0 = (⟨centerOne, centerOne_mem_halfFordRegion⟩ : halfFordRegion) := by
  rw [halfFordBoundaryParam_eq_circle (by norm_num) (by norm_num)]
  exact halfFordCirclePoint_zero

@[simp] theorem halfFordBoundaryParam_one :
    halfFordBoundaryParam 1 = (⟨centerTwo, centerTwo_mem_halfFordRegion⟩ : halfFordRegion) := by
  rw [halfFordBoundaryParam_eq_circle (by norm_num) (by norm_num)]
  exact halfFordCirclePoint_one

private theorem centerTwo_re_lt_centerOne_re : centerTwo.re < centerOne.re := by
  change (centerTwo : ℂ).re < (centerOne : ℂ).re
  rw [centerOne_coe_re, centerTwo_coe_re]
  exact stripLeft_lt_right

theorem halfFordBoundaryParam_re_eq_centerOne_iff (t : ℝ) :
    (halfFordBoundaryParam t : ℍ).re = centerOne.re ↔ t ≤ 0 := by
  constructor
  · intro hr
    by_contra ht
    have ht0 : 0 < t := lt_of_not_ge ht
    by_cases ht1 : t ≤ 1
    · rw [halfFordBoundaryParam_eq_circle ht0.le ht1, halfFordCirclePoint_re] at hr
      have hp := mul_pos ht0 (sub_pos.mpr centerTwo_re_lt_centerOne_re)
      dsimp at hr
      nlinarith
    · rw [halfFordBoundaryParam_re_of_one_le (le_of_not_ge ht1)] at hr
      exact centerTwo_re_lt_centerOne_re.ne hr
  · exact halfFordBoundaryParam_re_of_nonpos

theorem halfFordBoundaryParam_re_eq_centerTwo_iff (t : ℝ) :
    (halfFordBoundaryParam t : ℍ).re = centerTwo.re ↔ 1 ≤ t := by
  constructor
  · intro hr
    by_contra ht
    have ht1 : t < 1 := lt_of_not_ge ht
    by_cases ht0 : t ≤ 0
    · rw [halfFordBoundaryParam_re_of_nonpos ht0] at hr
      exact centerTwo_re_lt_centerOne_re.ne' hr
    · rw [halfFordBoundaryParam_eq_circle (le_of_not_ge ht0) ht1.le,
        halfFordCirclePoint_re] at hr
      have hp := mul_pos (sub_pos.mpr ht1) (sub_pos.mpr centerTwo_re_lt_centerOne_re)
      dsimp at hr
      nlinarith
  · exact halfFordBoundaryParam_re_of_one_le

/-- The right vertical side corresponds exactly to the first parameter ray. -/
theorem halfFordBoundaryParam_re_eq_right_iff (t : ℝ) :
    (halfFordBoundaryParam t : ℍ).re = -(1 / 2) ↔ t ≤ 0 := by
  have h : centerOne.re = -(1 / 2) := by
    change (centerOne : ℂ).re = -(1 / 2)
    simpa only [neg_div] using centerOne_coe_re
  rw [← h]
  exact halfFordBoundaryParam_re_eq_centerOne_iff t

/-- The left vertical side corresponds exactly to the last parameter ray. -/
theorem halfFordBoundaryParam_re_eq_left_iff (t : ℝ) :
    (halfFordBoundaryParam t : ℍ).re = stripLeft ↔ 1 ≤ t := by
  rw [← centerTwo_coe_re]
  exact halfFordBoundaryParam_re_eq_centerTwo_iff t

/-- The circular side corresponds exactly to the closed middle interval. -/
theorem halfFordBoundaryParam_norm_add_one_eq_one_iff (t : ℝ) :
    ‖((halfFordBoundaryParam t : ℍ) : ℂ) + 1‖ = 1 ↔ 0 ≤ t ∧ t ≤ 1 := by
  constructor
  · intro hn
    by_cases ht0 : t ≤ 0
    · have he : ((halfFordBoundaryParam t : ℍ) : ℂ) = (centerOne : ℂ) :=
        complex_eq_of_re_eq_norm_add_one_eq
          (halfFordBoundaryParam_re_of_nonpos ht0)
          (halfFordBoundaryParam t : ℍ).im_pos centerOne.im_pos
          (hn.trans centerOne_norm_add_one.symm)
      have hi := congrArg Complex.im he
      change (halfFordBoundaryParam t : ℍ).im = centerOne.im at hi
      rw [halfFordBoundaryParam_im_of_nonpos ht0] at hi
      have ht : t = 0 := by linarith
      subst t
      norm_num
    · by_cases ht1 : 1 ≤ t
      · have he : ((halfFordBoundaryParam t : ℍ) : ℂ) = (centerTwo : ℂ) :=
          complex_eq_of_re_eq_norm_add_one_eq
            (halfFordBoundaryParam_re_of_one_le ht1)
            (halfFordBoundaryParam t : ℍ).im_pos centerTwo.im_pos
            (hn.trans centerTwo_norm_add_one.symm)
        have hi := congrArg Complex.im he
        change (halfFordBoundaryParam t : ℍ).im = centerTwo.im at hi
        rw [halfFordBoundaryParam_im_of_one_le ht1] at hi
        have ht : t = 1 := by linarith
        subst t
        norm_num
      · exact ⟨le_of_not_ge ht0, le_of_not_ge ht1⟩
  · rintro ⟨ht0, ht1⟩
    rw [halfFordBoundaryParam_eq_circle ht0 ht1]
    exact halfFordCirclePoint_norm_add_one _

/-- No point of the parameter lies in the open triangle. -/
theorem halfFordBoundaryParam_notMem_interior (t : ℝ) :
    (halfFordBoundaryParam t : ℍ) ∉ halfFordInterior := by
  intro hi
  have hI : ((halfFordBoundaryParam t : ℍ) : ℂ) ∈ triangleInterior := by
    simpa only [halfFordInterior_eq_preimage_triangleInterior, mem_preimage] using hi
  by_cases ht0 : t ≤ 0
  · have hr := halfFordBoundaryParam_re_eq_right_iff t |>.mpr ht0
    have hu := hI.2.1
    change (halfFordBoundaryParam t : ℍ).re < -1 / 2 at hu
    linarith
  · by_cases ht1 : 1 ≤ t
    · have hr := halfFordBoundaryParam_re_eq_left_iff t |>.mpr ht1
      have hl := hI.1
      change stripLeft < (halfFordBoundaryParam t : ℍ).re at hl
      linarith
    · have hn := (halfFordBoundaryParam_norm_add_one_eq_one_iff t).mpr
        ⟨le_of_not_ge ht0, le_of_not_ge ht1⟩
      have hgt := hI.2.2.2
      rw [hn] at hgt
      exact lt_irrefl _ hgt

/-- Different real parameters give different actual boundary points. -/
theorem halfFordBoundaryParam_injective : Function.Injective halfFordBoundaryParam := by
  intro s t he
  have hr := congrArg (fun z : halfFordRegion => (z : ℍ).re) he
  have hi := congrArg (fun z : halfFordRegion => (z : ℍ).im) he
  by_cases hs0 : s ≤ 0
  · have ht0 : t ≤ 0 := (halfFordBoundaryParam_re_eq_centerOne_iff t).mp
      (hr.symm.trans (halfFordBoundaryParam_re_of_nonpos hs0))
    rw [halfFordBoundaryParam_im_of_nonpos hs0,
      halfFordBoundaryParam_im_of_nonpos ht0] at hi
    linarith
  · by_cases hs1 : 1 ≤ s
    · have ht1 : 1 ≤ t := (halfFordBoundaryParam_re_eq_centerTwo_iff t).mp
        (hr.symm.trans (halfFordBoundaryParam_re_of_one_le hs1))
      rw [halfFordBoundaryParam_im_of_one_le hs1,
        halfFordBoundaryParam_im_of_one_le ht1] at hi
      linarith
    · have hs : 0 ≤ s ∧ s ≤ 1 := ⟨le_of_not_ge hs0, le_of_not_ge hs1⟩
      have ht : 0 ≤ t ∧ t ≤ 1 := by
        apply (halfFordBoundaryParam_norm_add_one_eq_one_iff t).mp
        rw [← he]
        exact (halfFordBoundaryParam_norm_add_one_eq_one_iff s).mpr hs
      rw [halfFordBoundaryParam_eq_circle hs.1 hs.2,
        halfFordBoundaryParam_eq_circle ht.1 ht.2] at he
      exact congrArg Subtype.val (halfFordCirclePoint_injective he)

private theorem centerOne_im_eq_boundaryHeight :
    centerOne.im = boundaryHeight centerOne.re := by
  simpa only [halfFordCirclePoint_zero] using halfFordCirclePoint_im 0

private theorem centerTwo_im_eq_boundaryHeight :
    centerTwo.im = boundaryHeight centerTwo.re := by
  simpa only [halfFordCirclePoint_one] using halfFordCirclePoint_im 1

/-- Every finite boundary point occurs, including both vertices and all
three closed sides. -/
theorem halfFordBoundaryParam_range :
    range halfFordBoundaryParam = {z : halfFordRegion | (z : ℍ) ∉ halfFordInterior} := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact halfFordBoundaryParam_notMem_interior t
  · intro hz
    have hclosed : ((z : ℍ) : ℂ) ∈ triangleClosedRegion :=
      (coe_mem_triangleClosedRegion_iff_halfFordRegion _).mpr z.property
    have hheight : boundaryHeight (z : ℍ).re ≤ (z : ℍ).im :=
      (mem_triangleClosedRegion_iff_epigraph _).mp hclosed |>.2.2
    by_cases hr : (z : ℍ).re = centerOne.re
    · have hi : centerOne.im ≤ (z : ℍ).im := by
        simpa only [hr, ← centerOne_im_eq_boundaryHeight] using hheight
      have ht : centerOne.im - (z : ℍ).im ≤ 0 := sub_nonpos.mpr hi
      refine ⟨centerOne.im - (z : ℍ).im, Subtype.ext (UpperHalfPlane.ext_re_im ?_ ?_)⟩
      · exact (halfFordBoundaryParam_re_of_nonpos ht).trans hr.symm
      · rw [halfFordBoundaryParam_im_of_nonpos ht]
        ring
    · by_cases hl : (z : ℍ).re = centerTwo.re
      · have hi : centerTwo.im ≤ (z : ℍ).im := by
          simpa only [hl, ← centerTwo_im_eq_boundaryHeight] using hheight
        have ht : 1 ≤ 1 + (z : ℍ).im - centerTwo.im := by linarith
        refine ⟨1 + (z : ℍ).im - centerTwo.im,
          Subtype.ext (UpperHalfPlane.ext_re_im ?_ ?_)⟩
        · exact (halfFordBoundaryParam_re_of_one_le ht).trans hl.symm
        · rw [halfFordBoundaryParam_im_of_one_le ht]
          ring
      · have hnorm : ‖((z : ℍ) : ℂ) + 1‖ = 1 := by
          by_contra hn
          have hleft : stripLeft < (z : ℍ).re := by
            have hc : centerTwo.re = stripLeft := centerTwo_coe_re
            have hne : (z : ℍ).re ≠ stripLeft := fun he => hl (he.trans hc.symm)
            exact lt_of_le_of_ne hclosed.1 hne.symm
          have hright : (z : ℍ).re < -1 / 2 := by
            have hc : centerOne.re = -1 / 2 := centerOne_coe_re
            have hne : (z : ℍ).re ≠ -1 / 2 := fun he => hr (he.trans hc.symm)
            exact lt_of_le_of_ne hclosed.2.1 hne
          apply hz
          rw [halfFordInterior_eq_preimage_triangleInterior]
          exact ⟨hleft, hright, (z : ℍ).im_pos,
            lt_of_le_of_ne hclosed.2.2.2 (fun he => hn he.symm)⟩
        have hc : z ∈ range halfFordCirclePoint := by
          rw [halfFordCirclePoint_range]
          exact hnorm
        obtain ⟨t, rfl⟩ := hc
        exact ⟨t, halfFordBoundaryParam_eq_circle t.property.1 t.property.2⟩

end Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians
