import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupOuterMeridianPaths
import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupOuterMeridianTransport
import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroup
import Wikipedia.HopfProblem.FundamentalGroupVanKampenTransport

/-!
# The exact free word of a large positive based circle

For every radius `R ≥ 2`, start at `1/2`, follow the vertical tail to
`1/2 - R*I`, traverse the positively oriented circle of radius `R` centered
at `1/2`, then retrace the tail. The actual free-covering transitions
show that its word is `of false * of true` in Mathlib's fundamental-group
multiplication convention. Reversing the loop gives the inverse word.

These are statements about the actual twice-punctured plane. No source
cusp loop or local cusp coordinate is identified here.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

section Subdivision

variable {X : Type*} [TopologicalSpace X] {x b : X}

private theorem three_subpaths_homotopic (C : Path x x) (a c : unitInterval) :
    (((C.subpath 0 a).trans ((C.subpath a c).trans (C.subpath c 1))).cast
      C.source.symm C.target.symm).Homotopic C := by
  have h : ((C.subpath 0 a).trans ((C.subpath a c).trans (C.subpath c 1))).Homotopic
      (C.subpath 0 1) :=
    ((Path.Homotopic.refl _).hcomp ⟨Path.Homotopy.subpathTransSubpath C a c 1⟩).trans
      ⟨Path.Homotopy.subpathTransSubpath C 0 a 1⟩
  have hcast : (C.cast C.source C.target).cast C.source.symm C.target.symm = C := by
    ext s
    rfl
  simpa only [Path.subpath_zero_one, hcast] using
    h.pathCast C.source.symm C.target.symm

private theorem basedLoop_subpaths (τ : Path b x) (C : Path x x) (a c : unitInterval) :
    Path.Homotopic.Quotient.mk ((τ.trans C).trans τ.symm) =
      Path.Homotopic.Quotient.mk
        ((τ.trans ((C.subpath 0 a).cast C.source.symm rfl)).trans
          ((C.subpath a c).trans
            (((C.subpath c 1).cast rfl C.target.symm).trans τ.symm))) := by
  have h : Path.Homotopic.Quotient.mk C =
      Path.Homotopic.Quotient.mk
        (((C.subpath 0 a).cast C.source.symm rfl).trans
          ((C.subpath a c).trans ((C.subpath c 1).cast rfl C.target.symm))) := by
    apply Path.Homotopic.Quotient.eq.mpr
    exact (three_subpaths_homotopic C a c).symm
  simp only [Path.Homotopic.Quotient.mk_trans]
  rw [h]
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.trans_assoc]

end Subdivision

variable (R : ℝ) (hR : 2 ≤ R)

/-- The vertical tail, the exact positive circle, and the reversed tail. -/
def positiveOuterMeridian : Path meridianBasepoint meridianBasepoint :=
  ((outerMeridianTail R hR).trans (outerPositiveCircle R hR)).trans
    (outerMeridianTail R hR).symm

theorem positiveOuterMeridian_eq_tail_circle_tail :
    positiveOuterMeridian R hR =
      ((outerMeridianTail R hR).trans (outerPositiveCircle R hR)).trans
        (outerMeridianTail R hR).symm := rfl

/-- The clockwise based outer meridian is the reverse of the positive one. -/
def negativeOuterMeridian : Path meridianBasepoint meridianBasepoint :=
  (positiveOuterMeridian R hR).symm

/-- The first piece follows the tail and the bottom-right quarter circle. -/
def outerLowerStart :
    Path meridianBasepoint (outerPositiveCircle R hR outerQuarter) :=
  (outerMeridianTail R hR).trans
    (((outerPositiveCircle R hR).subpath 0 outerQuarter).cast
      (outerPositiveCircle R hR).source.symm rfl)

/-- The middle piece is the whole upper semicircle, from right to left. -/
def outerUpperCross :
    Path (outerPositiveCircle R hR outerQuarter)
      (outerPositiveCircle R hR outerThreeQuarters) :=
  (outerPositiveCircle R hR).subpath outerQuarter outerThreeQuarters

/-- The last piece follows the bottom-left quarter circle and the reversed tail. -/
def outerLowerFinish :
    Path (outerPositiveCircle R hR outerThreeQuarters) meridianBasepoint :=
  (((outerPositiveCircle R hR).subpath outerThreeQuarters 1).cast
    rfl (outerPositiveCircle R hR).target.symm).trans (outerMeridianTail R hR).symm

theorem positiveOuterMeridian_subdivision :
    Path.Homotopic.Quotient.mk (positiveOuterMeridian R hR) =
      Path.Homotopic.Quotient.mk
        ((outerLowerStart R hR).trans
          ((outerUpperCross R hR).trans (outerLowerFinish R hR))) :=
  basedLoop_subpaths (outerMeridianTail R hR) (outerPositiveCircle R hR)
    outerQuarter outerThreeQuarters

attribute [local instance] discreteFreeGroup

theorem outerLowerStart_mem_lower (t : unitInterval) :
    outerLowerStart R hR t ∈ freeGroupCover.V := by
  apply SimplyConnectedCover.trans_mem
  · exact outerMeridianTail_mem_lowerSlitPlane R hR
  · intro s
    change (outerPositiveCircle R hR).subpath 0 outerQuarter s ∈ freeGroupCover.V
    apply FundamentalGroupVanKampen.subpath_mem_of_mem_Icc
      (outerPositiveCircle R hR) (show (0 : unitInterval) ≤ outerQuarter from bot_le) _ s
    intro u hu
    exact outerPositiveCircle_mem_lowerSlitPlane R hR u (Or.inl hu.2)

theorem outerUpperCross_mem_upper (t : unitInterval) :
    outerUpperCross R hR t ∈ freeGroupCover.U := by
  apply FundamentalGroupVanKampen.subpath_mem_of_mem_Icc
    (outerPositiveCircle R hR) (show outerQuarter ≤ outerThreeQuarters by
      norm_num [outerQuarter, outerThreeQuarters]) _ t
  intro u hu
  exact outerPositiveCircle_mem_upperSlitPlane R hR u hu.1 hu.2

theorem outerLowerFinish_mem_lower (t : unitInterval) :
    outerLowerFinish R hR t ∈ freeGroupCover.V := by
  apply SimplyConnectedCover.trans_mem
  · intro s
    change (outerPositiveCircle R hR).subpath outerThreeQuarters 1 s ∈ freeGroupCover.V
    apply FundamentalGroupVanKampen.subpath_mem_of_mem_Icc
      (outerPositiveCircle R hR)
      (show outerThreeQuarters ≤ (1 : unitInterval) from le_top) _ s
    intro u hu
    exact outerPositiveCircle_mem_lowerSlitPlane R hR u (Or.inr hu.1)
  · exact fun s => outerMeridianTail_mem_lowerSlitPlane R hR (unitInterval.symm s)

theorem outerQuarter_mem_overlap :
    outerPositiveCircle R hR outerQuarter ∈
      (freeGroupCover.U : Set TwicePuncturedPlane) ∩ freeGroupCover.V := by
  change (outerPositiveCircle R hR outerQuarter : ℂ) ∈ upperSlitPlane ∩ lowerSlitPlane
  rw [slitPlanes_inter]
  have h := outerPositiveCircle_quarter_re_gt_one R hR
  exact ⟨ne_of_gt (lt_trans zero_lt_one h), ne_of_gt h⟩

theorem outerThreeQuarters_mem_overlap :
    outerPositiveCircle R hR outerThreeQuarters ∈
      (freeGroupCover.U : Set TwicePuncturedPlane) ∩ freeGroupCover.V := by
  change (outerPositiveCircle R hR outerThreeQuarters : ℂ) ∈ upperSlitPlane ∩ lowerSlitPlane
  rw [slitPlanes_inter]
  have h := outerPositiveCircle_threeQuarters_re_lt_zero R hR
  exact ⟨ne_of_lt h, ne_of_lt (lt_trans h zero_lt_one)⟩

@[simp] theorem freeGroupTransition_outerQuarter :
    freeGroupTransition (outerPositiveCircle R hR outerQuarter) = FreeGroup.of true := by
  have h := outerPositiveCircle_quarter_re_gt_one R hR
  have hzero : ¬(outerPositiveCircle R hR outerQuarter : ℂ).re < 0 := by linarith
  have hone : ¬(outerPositiveCircle R hR outerQuarter : ℂ).re < 1 := not_lt.mpr h.le
  simp only [freeGroupTransition, if_neg hzero, if_neg hone]

@[simp] theorem freeGroupTransition_outerThreeQuarters :
    freeGroupTransition (outerPositiveCircle R hR outerThreeQuarters) =
      (FreeGroup.of false)⁻¹ := by
  simp only [freeGroupTransition,
    if_pos (outerPositiveCircle_threeQuarters_re_lt_zero R hR)]

/-- The exact word is computed from the actual sheet transitions. The
order is the one fixed by Mathlib's fundamental-group multiplication. -/
theorem meridianFreeWordHom_positiveOuterMeridian :
    meridianFreeWordHom (.mk (positiveOuterMeridian R hR)) =
      FreeGroup.of false * FreeGroup.of true := by
  rw [positiveOuterMeridian_subdivision]
  rw [meridianFreeWordHom_lower_upper_lower
    (outerQuarter_mem_overlap R hR) (outerThreeQuarters_mem_overlap R hR)
    (outerLowerStart R hR) (outerUpperCross R hR) (outerLowerFinish R hR)
    (outerLowerStart_mem_lower R hR) (outerUpperCross_mem_upper R hR)
    (outerLowerFinish_mem_lower R hR)]
  rw [freeGroupTransition_outerThreeQuarters, freeGroupTransition_outerQuarter, inv_inv]

/-- The actual based positive outer loop represents this product of the
two actual positive meridian classes. -/
theorem positiveOuterMeridian_class_eq :
    (.mk (positiveOuterMeridian R hR) :
      FundamentalGroup TwicePuncturedPlane meridianBasepoint) =
      meridianClass false * meridianClass true := by
  apply twicePuncturedFundamentalGroupFreeEquiv.injective
  change meridianFreeWordHom (.mk (positiveOuterMeridian R hR)) =
    meridianFreeWordHom (meridianClass false * meridianClass true)
  rw [meridianFreeWordHom_positiveOuterMeridian, map_mul,
    meridianFreeWordHom_meridianClass, meridianFreeWordHom_meridianClass]

/-- Reversing the actual based loop gives the inverse peripheral word. -/
theorem meridianFreeWordHom_negativeOuterMeridian :
    meridianFreeWordHom (.mk (negativeOuterMeridian R hR)) =
      (FreeGroup.of false * FreeGroup.of true)⁻¹ := by
  change meridianFreeWordHom
    ((.mk (positiveOuterMeridian R hR) :
      FundamentalGroup TwicePuncturedPlane meridianBasepoint)⁻¹) = _
  rw [map_inv, meridianFreeWordHom_positiveOuterMeridian]

theorem negativeOuterMeridian_class_eq :
    (.mk (negativeOuterMeridian R hR) :
      FundamentalGroup TwicePuncturedPlane meridianBasepoint) =
      (meridianClass false * meridianClass true)⁻¹ := by
  exact congrArg (fun γ : FundamentalGroup TwicePuncturedPlane meridianBasepoint => γ⁻¹)
    (positiveOuterMeridian_class_eq R hR)

/-- Increasing the radius moves the entire circle core outside any
fixed norm bound; no corresponding bound on the based tail is asserted. -/
theorem outerPositiveCircle_norm_lower_bound (t : unitInterval) :
    R - 1 / 2 ≤ ‖(outerPositiveCircle R hR t : ℂ)‖ := by
  have h := norm_sub_le (outerPositiveCircle R hR t : ℂ) (1 / 2 : ℂ)
  rw [outerPositiveCircle_norm_sub_center] at h
  norm_num [norm_div] at h
  change R - 1 / 2 ≤ ‖circleMap (1 / 2 : ℂ) R
    (-Real.pi / 2 + 2 * Real.pi * (t : ℝ))‖
  linarith

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
