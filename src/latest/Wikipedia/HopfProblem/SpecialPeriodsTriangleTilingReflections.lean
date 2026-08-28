import Wikipedia.HopfProblem.SpecialPeriodsTriangleFundamentalRegion

/-!
# Reflections and side pairings of the concrete Ford polygon

The three side reflections are genuine homeomorphisms of the upper half-plane.
Their products are the actual determinant-one matrix transformations already
used for the `(3,4,∞)` action.  In particular, the side-pairing statements below
concern the concrete circular arcs and vertical rays, not abstract labels.
-/

noncomputable section

open Set UpperHalfPlane Matrix
open scoped MatrixGroups Topology ComplexConjugate ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

/-- Reflection in the vertical geodesic whose real coordinate is `a / 2`. -/
def verticalReflection (a : ℝ) : ℍ ≃ₜ ℍ where
  toFun z := ⟨(a : ℂ) - conj (z : ℂ), by simpa using z.im_pos⟩
  invFun z := ⟨(a : ℂ) - conj (z : ℂ), by simpa using z.im_pos⟩
  left_inv z := by apply UpperHalfPlane.ext; simp
  right_inv z := by apply UpperHalfPlane.ext; simp
  continuous_toFun := by
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    change Continuous (fun z : ℍ => (a : ℂ) - conj (z : ℂ))
    fun_prop
  continuous_invFun := by
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    change Continuous (fun z : ℍ => (a : ℂ) - conj (z : ℂ))
    fun_prop

@[simp] theorem verticalReflection_coe (a : ℝ) (z : ℍ) :
    (verticalReflection a z : ℂ) = (a : ℂ) - conj (z : ℂ) := rfl

@[simp] theorem verticalReflection_re (a : ℝ) (z : ℍ) :
    (verticalReflection a z).re = a - z.re := by
  change ((a : ℂ) - conj (z : ℂ)).re = a - z.re
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.conj_re, UpperHalfPlane.coe_re]

@[simp] theorem verticalReflection_im (a : ℝ) (z : ℍ) :
    (verticalReflection a z).im = z.im := by
  change ((a : ℂ) - conj (z : ℂ)).im = z.im
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.conj_im, zero_sub,
    neg_neg, UpperHalfPlane.coe_im]

theorem verticalReflection_involutive (a : ℝ) :
    Function.Involutive (verticalReflection a) :=
  (verticalReflection a).left_inv

theorem verticalReflection_fixed_iff (a : ℝ) (z : ℍ) :
    verticalReflection a z = z ↔ z.re = a / 2 := by
  constructor
  · intro h
    have hr := congrArg UpperHalfPlane.re h
    rw [verticalReflection_re] at hr
    linarith
  · intro h
    apply UpperHalfPlane.ext
    apply Complex.ext
    · change (verticalReflection a z).re = z.re
      rw [verticalReflection_re]
      linarith
    · exact verticalReflection_im a z

/-- Reflection in the right side of the half-Ford triangle, `re z = -1/2`. -/
def rightReflection : ℍ ≃ₜ ℍ := verticalReflection (-1)

/-- Reflection in the left vertical side, `re z = stripLeft`. -/
def leftReflection : ℍ ≃ₜ ℍ := verticalReflection (-(width + 1))

@[simp] theorem rightReflection_coe (z : ℍ) :
    (rightReflection z : ℂ) = -1 - conj (z : ℂ) := by
  simp [rightReflection]

@[simp] theorem leftReflection_coe (z : ℍ) :
    (leftReflection z : ℂ) = -((width : ℂ) + 1) - conj (z : ℂ) := by
  simp [leftReflection]

@[simp] theorem rightReflection_re (z : ℍ) :
    (rightReflection z).re = -1 - z.re := by
  simp [rightReflection]

@[simp] theorem rightReflection_im (z : ℍ) :
    (rightReflection z).im = z.im := verticalReflection_im _ _

@[simp] theorem rightReflection_norm (z : ℍ) :
    ‖(rightReflection z : ℂ)‖ = ‖(z : ℂ) + 1‖ := by
  rw [rightReflection_coe]
  calc
    _ = ‖-conj ((z : ℂ) + 1)‖ := by congr 1; simp; ring
    _ = _ := by rw [norm_neg, Complex.norm_conj]

@[simp] theorem rightReflection_add_one_norm (z : ℍ) :
    ‖(rightReflection z : ℂ) + 1‖ = ‖(z : ℂ)‖ := by
  rw [rightReflection_coe]
  calc
    _ = ‖-conj (z : ℂ)‖ := by congr 1; ring
    _ = _ := by rw [norm_neg, Complex.norm_conj]

@[simp] theorem leftReflection_re (z : ℍ) :
    (leftReflection z).re = -(width + 1) - z.re := verticalReflection_re _ _

@[simp] theorem leftReflection_im (z : ℍ) :
    (leftReflection z).im = z.im := verticalReflection_im _ _

theorem rightReflection_involutive : Function.Involutive rightReflection :=
  verticalReflection_involutive _

theorem leftReflection_involutive : Function.Involutive leftReflection :=
  verticalReflection_involutive _

@[simp] theorem rightReflection_fixed_iff (z : ℍ) :
    rightReflection z = z ↔ z.re = -(1 / 2) := by
  simpa only [rightReflection, neg_div] using verticalReflection_fixed_iff (-1) z

@[simp] theorem leftReflection_fixed_iff (z : ℍ) :
    leftReflection z = z ↔ z.re = stripLeft :=
  verticalReflection_fixed_iff _ _

theorem conjugate_denominatorOne_ne_zero (z : ℍ) : conj (z : ℂ) + 1 ≠ 0 := by
  simpa only [map_add, map_one, map_ne_zero] using
    (map_ne_zero (starRingEnd ℂ)).mpr (denominatorOne_ne_zero z)

private def circleReflectionMap (z : ℍ) : ℍ :=
  ⟨-1 + 1 / (conj (z : ℂ) + 1), by
    simp only [one_div, Complex.add_im, Complex.neg_im, Complex.one_im,
      neg_zero, zero_add, Complex.inv_im, Complex.conj_im, add_zero,
      neg_neg, UpperHalfPlane.coe_im]
    exact div_pos z.im_pos (Complex.normSq_pos.mpr (conjugate_denominatorOne_ne_zero z))⟩

private theorem circleReflectionMap_involutive : Function.Involutive circleReflectionMap := by
  intro z
  apply UpperHalfPlane.ext
  change -1 + 1 / (conj (-1 + 1 / (conj (z : ℂ) + 1)) + 1) = (z : ℂ)
  simp

private theorem circleReflectionMap_continuous : Continuous circleReflectionMap := by
  apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
  change Continuous (fun z : ℍ => -1 + 1 / (conj (z : ℂ) + 1))
  exact continuous_const.add (continuous_const.div
    ((Complex.continuous_conj.comp continuous_coe).add continuous_const)
    conjugate_denominatorOne_ne_zero)

/-- Reflection in the semicircular geodesic `‖z + 1‖ = 1`. -/
def circleReflection : ℍ ≃ₜ ℍ where
  toFun := circleReflectionMap
  invFun := circleReflectionMap
  left_inv := circleReflectionMap_involutive
  right_inv := circleReflectionMap_involutive
  continuous_toFun := circleReflectionMap_continuous
  continuous_invFun := circleReflectionMap_continuous

@[simp] theorem circleReflection_coe (z : ℍ) :
    (circleReflection z : ℂ) = -1 + 1 / (conj (z : ℂ) + 1) := rfl

theorem circleReflection_involutive : Function.Involutive circleReflection :=
  circleReflectionMap_involutive

theorem circleReflection_im (z : ℍ) :
    (circleReflection z).im = z.im / Complex.normSq ((z : ℂ) + 1) := by
  change (-1 + 1 / (conj (z : ℂ) + 1)).im = _
  rw [show conj (z : ℂ) + 1 = conj ((z : ℂ) + 1) by simp]
  simp only [one_div, Complex.add_im, Complex.neg_im, Complex.one_im,
    neg_zero, zero_add, Complex.inv_im, Complex.normSq_conj,
    Complex.conj_im, add_zero, neg_neg, UpperHalfPlane.coe_im]

@[simp] theorem circleReflection_fixed_iff (z : ℍ) :
    circleReflection z = z ↔ ‖(z : ℂ) + 1‖ = 1 := by
  constructor
  · intro h
    have hi := congrArg UpperHalfPlane.im h
    rw [circleReflection_im] at hi
    have hd : Complex.normSq ((z : ℂ) + 1) ≠ 0 :=
      (Complex.normSq_pos.mpr (denominatorOne_ne_zero z)).ne'
    have hs : Complex.normSq ((z : ℂ) + 1) = 1 := by
      apply mul_left_cancel₀ z.im_ne_zero
      simpa only [mul_one] using ((div_eq_iff hd).mp hi).symm
    rw [Complex.normSq_eq_norm_sq] at hs
    nlinarith [norm_nonneg ((z : ℂ) + 1)]
  · intro h
    apply UpperHalfPlane.ext
    rw [circleReflection_coe]
    have hs : Complex.normSq (conj (z : ℂ) + 1) = 1 := by
      rw [show conj (z : ℂ) + 1 = conj ((z : ℂ) + 1) by simp,
        Complex.normSq_conj, Complex.normSq_eq_norm_sq, h]
      norm_num
    simp [one_div, Complex.inv_def, hs]

@[simp] theorem rightReflection_mem_fordRegion_iff (z : ℍ) :
    rightReflection z ∈ fordRegion ↔ z ∈ fordRegion := by
  simp only [fordRegion, mem_ofPred_eq, rightReflection_re,
    rightReflection_add_one_norm, rightReflection_norm]
  unfold stripLeft stripRight
  constructor
  · rintro ⟨hl, hr, hnorm, hadd⟩
    refine ⟨?_, ?_, hadd, hnorm⟩ <;> linarith
  · rintro ⟨hl, hr, hadd, hnorm⟩
    refine ⟨?_, ?_, hnorm, hadd⟩ <;> linarith

theorem rightReflection_mapsTo_fordRegion :
    MapsTo rightReflection fordRegion fordRegion :=
  fun z hz => (rightReflection_mem_fordRegion_iff z).mpr hz

theorem rightReflection_image_fordRegion :
    rightReflection '' fordRegion = fordRegion := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (rightReflection_mem_fordRegion_iff w).mpr hw
  · intro hz
    exact ⟨rightReflection z, (rightReflection_mem_fordRegion_iff z).mpr hz,
      rightReflection_involutive z⟩

/-- The left circular boundary arc of the actual Ford region. -/
def leftCircularArc : Set ℍ := {z | z ∈ fordRegion ∧ ‖(z : ℂ) + 1‖ = 1}

/-- The right circular boundary arc of the actual Ford region. -/
def rightCircularArc : Set ℍ := {z | z ∈ fordRegion ∧ ‖(z : ℂ)‖ = 1}

@[simp] theorem rightReflection_mem_rightCircularArc_iff (z : ℍ) :
    rightReflection z ∈ rightCircularArc ↔ z ∈ leftCircularArc := by
  simp only [leftCircularArc, rightCircularArc, mem_ofPred_eq,
    rightReflection_mem_fordRegion_iff, rightReflection_norm]

@[simp] theorem rightReflection_mem_leftCircularArc_iff (z : ℍ) :
    rightReflection z ∈ leftCircularArc ↔ z ∈ rightCircularArc := by
  simp only [leftCircularArc, rightCircularArc, mem_ofPred_eq,
    rightReflection_mem_fordRegion_iff, rightReflection_add_one_norm]

theorem rightReflection_mapsTo_leftCircularArc :
    MapsTo rightReflection leftCircularArc rightCircularArc :=
  fun z hz => (rightReflection_mem_rightCircularArc_iff z).mpr hz

theorem rightReflection_mapsTo_rightCircularArc :
    MapsTo rightReflection rightCircularArc leftCircularArc :=
  fun z hz => (rightReflection_mem_leftCircularArc_iff z).mpr hz

theorem rightReflection_image_leftCircularArc :
    rightReflection '' leftCircularArc = rightCircularArc := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (rightReflection_mem_rightCircularArc_iff w).mpr hw
  · intro hz
    exact ⟨rightReflection z, (rightReflection_mem_leftCircularArc_iff z).mpr hz,
      rightReflection_involutive z⟩

theorem rightReflection_image_rightCircularArc :
    rightReflection '' rightCircularArc = leftCircularArc := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (rightReflection_mem_leftCircularArc_iff w).mpr hw
  · intro hz
    exact ⟨rightReflection z, (rightReflection_mem_rightCircularArc_iff z).mpr hz,
      rightReflection_involutive z⟩

/-- The order-three generator is the product of the right and circle reflections. -/
theorem generatorOne_reflections (z : ℍ) :
    generatorOneSL • z = rightReflection (circleReflection z) := by
  apply UpperHalfPlane.ext
  simp [generatorOne_coe, neg_div, one_div]

/-- The order-four generator is the product of the circle and left reflections. -/
theorem generatorTwo_reflections (z : ℍ) :
    generatorTwoSL • z = circleReflection (leftReflection z) := by
  apply UpperHalfPlane.ext
  rw [generatorTwo_coe, circleReflection_coe, leftReflection_coe]
  simp only [map_sub, map_neg, map_add, Complex.conj_ofReal, map_one, Complex.conj_conj]
  rw [show -((width : ℂ) + 1) - (z : ℂ) + 1 = -(z : ℂ) - width by ring]
  have hd := denominatorTwo_ne_zero z
  field_simp [hd]
  ring

/-- The primitive cusp translation is the product of the two vertical reflections. -/
theorem cusp_reflections (z : ℍ) :
    cuspSL • z = leftReflection (rightReflection z) := by
  apply UpperHalfPlane.ext
  rw [cuspSL_apply]
  simp [UpperHalfPlane.coe_vadd]

/-- On the left circular side, the order-three pairing is the right reflection. -/
theorem generatorOne_eq_rightReflection_of_norm_add_one (z : ℍ)
    (hz : ‖(z : ℂ) + 1‖ = 1) : generatorOneSL • z = rightReflection z := by
  rw [generatorOne_reflections, (circleReflection_fixed_iff z).mpr hz]

theorem generatorOne_coe_of_norm_add_one (z : ℍ) (hz : ‖(z : ℂ) + 1‖ = 1) :
    ((generatorOneSL • z : ℍ) : ℂ) = -conj (z : ℂ) - 1 := by
  rw [generatorOne_eq_rightReflection_of_norm_add_one z hz, rightReflection_coe]
  ring

theorem generatorOne_mapsTo_leftCircularArc :
    MapsTo (fun z : ℍ => generatorOneSL • z) leftCircularArc rightCircularArc := by
  intro z hz
  change generatorOneSL • z ∈ rightCircularArc
  rw [generatorOne_eq_rightReflection_of_norm_add_one z hz.2]
  exact rightReflection_mapsTo_leftCircularArc hz

theorem generatorOne_image_leftCircularArc :
    (fun z : ℍ => generatorOneSL • z) '' leftCircularArc = rightCircularArc := by
  rw [← rightReflection_image_leftCircularArc]
  apply Set.image_congr
  intro z hz
  exact generatorOne_eq_rightReflection_of_norm_add_one z hz.2

/-- Conjugating the output of the right reflection gives a holomorphic map. -/
theorem rightReflection_antiholomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : ℍ => conj (rightReflection z : ℂ)) := by
  have he : (fun z : ℍ => conj (rightReflection z : ℂ)) =
      (fun z : ℍ => -1 - (z : ℂ)) := by
    funext z
    simp
  rw [he]
  exact contMDiff_const.sub UpperHalfPlane.contMDiff_coe

/-- Conjugating the output of the left reflection gives a holomorphic map. -/
theorem leftReflection_antiholomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : ℍ => conj (leftReflection z : ℂ)) := by
  have he : (fun z : ℍ => conj (leftReflection z : ℂ)) =
      (fun z : ℍ => -((width : ℂ) + 1) - (z : ℂ)) := by
    funext z
    simp
  rw [he]
  exact contMDiff_const.sub UpperHalfPlane.contMDiff_coe

/-- Conjugating the output of the circle reflection gives a holomorphic map. -/
theorem circleReflection_antiholomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : ℍ => conj (circleReflection z : ℂ)) := by
  have he : (fun z : ℍ => conj (circleReflection z : ℂ)) =
      (fun z : ℍ => -1 + 1 / ((z : ℂ) + 1)) := by
    funext z
    simp
  rw [he]
  exact contMDiff_const.add (contMDiff_const.div₀
    (UpperHalfPlane.contMDiff_coe.add contMDiff_const) denominatorOne_ne_zero)

theorem cusp_re (z : ℍ) : (cuspSL • z).re = z.re - width := by
  rw [cuspSL_apply, vadd_re]
  ring

theorem cusp_im (z : ℍ) : (cuspSL • z).im = z.im := by
  rw [cuspSL_apply, vadd_im]

/-- The cusp side-pairing sends the entire right vertical line to the left. -/
theorem cusp_re_eq_stripLeft_iff (z : ℍ) :
    (cuspSL • z).re = stripLeft ↔ z.re = stripRight := by
  rw [cusp_re]
  constructor <;> intro h <;> linarith [strip_width]

/-- Exact pairing of the vertical rays at any common height. -/
theorem cusp_image_verticalRay (height : ℝ) :
    (fun z : ℍ => cuspSL • z) '' {z | z.re = stripRight ∧ height ≤ z.im} =
      {z | z.re = stripLeft ∧ height ≤ z.im} := by
  ext z
  constructor
  · rintro ⟨w, ⟨hr, hi⟩, rfl⟩
    exact ⟨(cusp_re_eq_stripLeft_iff w).mpr hr, (cusp_im w).symm ▸ hi⟩
  · rintro ⟨hl, hi⟩
    refine ⟨cuspSL⁻¹ • z, ⟨?_, ?_⟩, smul_inv_smul _ _⟩
    · apply (cusp_re_eq_stripLeft_iff (cuspSL⁻¹ • z)).mp
      simpa only [smul_inv_smul] using hl
    · have hh : z.im = (cuspSL⁻¹ • z).im := by
        simpa only [smul_inv_smul] using cusp_im (cuspSL⁻¹ • z)
      exact hh ▸ hi

theorem mem_fordRegion_of_re_eq_stripRight (z : ℍ)
    (hr : z.re = stripRight) (hi : stripRight ≤ z.im) : z ∈ fordRegion := by
  have himsq : stripRight ^ 2 ≤ z.im ^ 2 :=
    (sq_le_sq₀ stripRight_pos.le z.im_pos.le).mpr hi
  have hnormsq : 1 ≤ Complex.normSq (z : ℂ) := by
    simp only [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, hr]
    nlinarith [stripRight_sq]
  have haddnormsq : 1 ≤ Complex.normSq ((z : ℂ) + 1) := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re,
      Complex.add_im, Complex.one_im, add_zero, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im, hr]
    nlinarith [stripRight_sq, stripRight_pos]
  refine ⟨?_, hr.le, ?_, ?_⟩
  · rw [hr]
    exact strip_left_lt_right.le
  · rw [Complex.normSq_eq_norm_sq] at haddnormsq
    nlinarith [norm_nonneg ((z : ℂ) + 1)]
  · rw [Complex.normSq_eq_norm_sq] at hnormsq
    nlinarith [norm_nonneg (z : ℂ)]

theorem mem_fordRegion_and_re_eq_stripRight_iff (z : ℍ) :
    z ∈ fordRegion ∧ z.re = stripRight ↔ z.re = stripRight ∧ stripRight ≤ z.im := by
  constructor
  · rintro ⟨hz, hr⟩
    exact ⟨hr, fordRegion_im_lower_bound z hz⟩
  · rintro ⟨hr, hi⟩
    exact ⟨mem_fordRegion_of_re_eq_stripRight z hr hi, hr⟩

@[simp] theorem rightReflection_re_eq_stripRight_iff (z : ℍ) :
    (rightReflection z).re = stripRight ↔ z.re = stripLeft := by
  rw [rightReflection_re]
  unfold stripLeft stripRight
  constructor <;> intro h <;> linarith

@[simp] theorem rightReflection_re_eq_stripLeft_iff (z : ℍ) :
    (rightReflection z).re = stripLeft ↔ z.re = stripRight := by
  rw [rightReflection_re]
  unfold stripLeft stripRight
  constructor <;> intro h <;> linarith

theorem mem_fordRegion_and_re_eq_stripLeft_iff (z : ℍ) :
    z ∈ fordRegion ∧ z.re = stripLeft ↔ z.re = stripLeft ∧ stripRight ≤ z.im := by
  simpa only [rightReflection_mem_fordRegion_iff, rightReflection_re_eq_stripRight_iff,
    rightReflection_im] using mem_fordRegion_and_re_eq_stripRight_iff (rightReflection z)

/-- The left vertical boundary ray of the Ford polygon. -/
def leftVerticalRay : Set ℍ := {z | z ∈ fordRegion ∧ z.re = stripLeft}

/-- The right vertical boundary ray of the Ford polygon. -/
def rightVerticalRay : Set ℍ := {z | z ∈ fordRegion ∧ z.re = stripRight}

theorem leftVerticalRay_eq :
    leftVerticalRay = {z | z.re = stripLeft ∧ stripRight ≤ z.im} :=
  Set.ext mem_fordRegion_and_re_eq_stripLeft_iff

theorem rightVerticalRay_eq :
    rightVerticalRay = {z | z.re = stripRight ∧ stripRight ≤ z.im} :=
  Set.ext mem_fordRegion_and_re_eq_stripRight_iff

/-- The exact primitive cusp pairing between the two Ford boundary rays. -/
theorem cusp_image_rightVerticalRay :
    (fun z : ℍ => cuspSL • z) '' rightVerticalRay = leftVerticalRay := by
  rw [rightVerticalRay_eq, leftVerticalRay_eq]
  exact cusp_image_verticalRay stripRight

theorem cusp_mapsTo_rightVerticalRay :
    MapsTo (fun z : ℍ => cuspSL • z) rightVerticalRay leftVerticalRay := by
  intro z hz
  rw [← cusp_image_rightVerticalRay]
  exact mem_image_of_mem _ hz

theorem cusp_eq_rightReflection_of_re_eq_stripRight (z : ℍ) (hz : z.re = stripRight) :
    cuspSL • z = rightReflection z := by
  rw [cusp_reflections]
  exact (leftReflection_fixed_iff (rightReflection z)).mpr
    ((rightReflection_re_eq_stripLeft_iff z).mpr hz)

theorem generatorOne_inv_eq_rightReflection_of_norm (z : ℍ) (hz : ‖(z : ℂ)‖ = 1) :
    generatorOneSL⁻¹ • z = rightReflection z := by
  have h := generatorOne_eq_rightReflection_of_norm_add_one (rightReflection z)
    (by simpa only [rightReflection_add_one_norm] using hz)
  rw [rightReflection_involutive z] at h
  simpa only [inv_smul_smul] using congrArg (fun w : ℍ => generatorOneSL⁻¹ • w) h.symm

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
