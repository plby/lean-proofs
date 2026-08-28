import Wikipedia.HopfProblem.TriangleRiemannNormalization

/-!
# Canonical real-boundary preimages of the actual normalized triangle

These are the inverse images under the already constructed half-Ford
normalization, with its existing topology and marked values.  No ordering
of the boundary pieces or orientation of the half-plane is assumed.
-/

noncomputable section

open Set Topology UpperHalfPlane

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians

open SpecialPeriods SpecialPeriods.Triangle RiemannMapping
open RiemannSphere RiemannSphere.MobiusCircle

/-- The canonical actual half-Ford point whose normalized value is the
specified real number. -/
def halfFordRealPreimage (x : ℝ) : halfFordRegion :=
  halfFordNormalizationHomeomorph.symm
    ⟨(x : ℂ), by simp [closedOrientedHalfPlane]⟩

@[simp] theorem halfFordRealPreimage_normalization (x : ℝ) :
    (halfFordNormalizationHomeomorph (halfFordRealPreimage x) : ℂ) = (x : ℂ) :=
  congrArg (fun w : closedOrientedHalfPlane normalizationOrientation => (w : ℂ))
    (halfFordNormalizationHomeomorph.apply_symm_apply _)

theorem halfFordRealPreimage_continuous : Continuous halfFordRealPreimage :=
  halfFordNormalizationHomeomorph.symm.continuous.comp
    (Complex.continuous_ofReal.subtype_mk _)

theorem halfFordRealPreimage_injective : Function.Injective halfFordRealPreimage := by
  intro x y h
  apply Complex.ofReal_injective
  rw [← halfFordRealPreimage_normalization, ← halfFordRealPreimage_normalization, h]

@[simp] theorem halfFordRealPreimage_zero :
    halfFordRealPreimage 0 =
      (⟨centerOne, centerOne_mem_halfFordRegion⟩ : halfFordRegion) := by
  apply halfFordNormalizationHomeomorph.injective
  apply Subtype.ext
  rw [halfFordRealPreimage_normalization, halfFordNormalizationHomeomorph_centerOne,
    Complex.ofReal_zero]

@[simp] theorem halfFordRealPreimage_one :
    halfFordRealPreimage 1 =
      (⟨centerTwo, centerTwo_mem_halfFordRegion⟩ : halfFordRegion) := by
  apply halfFordNormalizationHomeomorph.injective
  apply Subtype.ext
  rw [halfFordRealPreimage_normalization, halfFordNormalizationHomeomorph_centerTwo,
    Complex.ofReal_one]

/-- Every real normalized value is an actual boundary point. -/
theorem halfFordRealPreimage_not_mem_interior (x : ℝ) :
    (halfFordRealPreimage x : ℍ) ∉ halfFordInterior := by
  apply (halfFordNormalizationHomeomorph_boundary_iff _).mp
  rw [halfFordRealPreimage_normalization]
  exact Complex.ofReal_im x

/-- The real coordinate of the actual normalization.  It will be used
only on the proved real boundary when asserting injectivity. -/
def halfFordBoundaryValue (z : halfFordRegion) : ℝ :=
  (halfFordNormalizationHomeomorph z : ℂ).re

theorem halfFordBoundaryValue_continuous : Continuous halfFordBoundaryValue :=
  Complex.continuous_re.comp
    (continuous_subtype_val.comp halfFordNormalizationHomeomorph.continuous)

@[simp] theorem halfFordBoundaryValue_realPreimage (x : ℝ) :
    halfFordBoundaryValue (halfFordRealPreimage x) = x := by
  rw [halfFordBoundaryValue, halfFordRealPreimage_normalization, Complex.ofReal_re]

@[simp] theorem halfFordBoundaryValue_centerOne :
    halfFordBoundaryValue ⟨centerOne, centerOne_mem_halfFordRegion⟩ = 0 := by
  rw [halfFordBoundaryValue, halfFordNormalizationHomeomorph_centerOne, Complex.zero_re]

@[simp] theorem halfFordBoundaryValue_centerTwo :
    halfFordBoundaryValue ⟨centerTwo, centerTwo_mem_halfFordRegion⟩ = 1 := by
  rw [halfFordBoundaryValue, halfFordNormalizationHomeomorph_centerTwo, Complex.one_re]

/-- On the boundary the normalization equals the complex inclusion of
its real coordinate. -/
theorem halfFordBoundaryValue_coe (z : halfFordRegion)
    (hz : (z : ℍ) ∉ halfFordInterior) :
    (halfFordBoundaryValue z : ℂ) = (halfFordNormalizationHomeomorph z : ℂ) := by
  apply Complex.ext
  · exact Complex.ofReal_re _
  · rw [Complex.ofReal_im, (halfFordNormalizationHomeomorph_boundary_iff z).mpr hz]

theorem halfFordBoundaryValue_injOn :
    Set.InjOn halfFordBoundaryValue {z : halfFordRegion | (z : ℍ) ∉ halfFordInterior} := by
  intro z hz w hw he
  apply halfFordNormalizationHomeomorph.injective
  apply Subtype.ext
  rw [← halfFordBoundaryValue_coe z hz, ← halfFordBoundaryValue_coe w hw, he]

/-- The canonical real inverse recovers every finite boundary point. -/
theorem halfFordRealPreimage_boundaryValue (z : halfFordRegion)
    (hz : (z : ℍ) ∉ halfFordInterior) :
    halfFordRealPreimage (halfFordBoundaryValue z) = z := by
  apply halfFordNormalizationHomeomorph.injective
  apply Subtype.ext
  rw [halfFordRealPreimage_normalization]
  exact halfFordBoundaryValue_coe z hz

end Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians
