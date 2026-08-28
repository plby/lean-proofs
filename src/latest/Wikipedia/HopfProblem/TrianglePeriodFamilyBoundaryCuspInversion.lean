import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCuspNativeCoordinate
import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingMeridiansComparison

/-!
# A genuine cusp-circle homotopy through the reciprocal coordinate

Inversion is an actual homeomorphism of the twice-punctured plane.  Apply
it to the proved analytic meridian square with the loop parameter
reversed.  The original native cusp loop consequently deforms to the
literal clockwise radius-two circle about zero, with its actual
basepoint trajectory retained by the continuous square.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.Cusp

open SpecialPeriods SpecialPeriods.Triangle
open ThreefoldOverlapMappingTorus.Cusp SpecialPeriods.EllipticAttachingMeridians

/-- The genuine inversion homeomorphism of the twice-punctured plane. -/
def planeInverse : TwicePuncturedPlane ≃ₜ TwicePuncturedPlane where
  toFun z := ⟨(z : ℂ)⁻¹, inv_ne_zero z.property.1, fun h => z.property.2 (inv_eq_one.mp h)⟩
  invFun z := ⟨(z : ℂ)⁻¹, inv_ne_zero z.property.1, fun h => z.property.2 (inv_eq_one.mp h)⟩
  left_inv z := Subtype.ext (inv_inv (z : ℂ))
  right_inv z := Subtype.ext (inv_inv (z : ℂ))
  continuous_toFun :=
    (continuous_subtype_val.inv₀ (fun z : TwicePuncturedPlane => z.property.1)).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.inv₀ (fun z : TwicePuncturedPlane => z.property.1)).subtype_mk _

@[simp] theorem planeInverse_coe (z : TwicePuncturedPlane) :
    (planeInverse z : ℂ) = (z : ℂ)⁻¹ := rfl

/-- Invert the actual positive meridian about zero, without rechoosing its path class. -/
def inverseMeridian :
    Path (planeInverse meridianBasepoint) (planeInverse meridianBasepoint) :=
  ((fixedClockwiseMeridian false).symm).map planeInverse.continuous

/-- Its actual finite-plane circle is clockwise and has radius exactly two. -/
theorem inverseMeridian_coe (t : unitInterval) :
    (inverseMeridian t : ℂ) = 2 * clockwiseUnit t := by
  have hp : (fixedClockwiseMeridian false).symm = positiveMeridianZero := by
    simp only [fixedClockwiseMeridian, Bool.false_eq_true, if_false, Path.symm_symm]
  change (((fixedClockwiseMeridian false).symm t : ℂ))⁻¹ = _
  rw [hp, positiveMeridianZero_apply, mul_inv_rev, ← Complex.exp_neg]
  norm_num only [inv_div, inv_one, one_mul]
  unfold clockwiseUnit
  rw [show -((2 * Real.pi : ℂ) * Complex.I * ((t : ℝ) : ℂ)) =
    -(2 * Real.pi : ℂ) * Complex.I * ((t : ℝ) : ℂ) by ring]
  ring

/-- The same literal inverse circle in the original regular quotient. -/
def inverseRegularMeridian :
    Path (triangleRegularPlaneHomeomorph.symm (planeInverse meridianBasepoint))
      (triangleRegularPlaneHomeomorph.symm (planeInverse meridianBasepoint)) :=
  inverseMeridian.map triangleRegularPlaneHomeomorph.symm.continuous

@[simp] theorem inverseRegularMeridian_coordinate (t : unitInterval) :
    triangleRegularPlaneHomeomorph (inverseRegularMeridian t) = inverseMeridian t :=
  triangleRegularPlaneHomeomorph.apply_symm_apply _

/-- The reciprocal germ has precisely the actual zero-meridian center. -/
theorem reciprocalCoordinate_center : reciprocalCoordinate 0 = center false :=
  reciprocalCoordinate_zero

/-- The actual original analytic cusp loop deforms to that exact inverse
circle through a continuous family of closed loops in the regular base. -/
def nativeReciprocalSquare : LoopSquare (nativeLoop controlledHeight) inverseRegularMeridian := by
  let S := reciprocalControl.analyticMeridianSquare false reciprocalCoordinate_center
    (parameter controlledHeight) (parameter_ne_zero controlledHeight) parameter_controlled
  let rev : C(unitInterval × unitInterval, unitInterval × unitInterval) :=
    ⟨fun z => (z.1, unitInterval.symm z.2),
      continuous_fst.prodMk (unitInterval.continuous_symm.comp continuous_snd)⟩
  refine {
    map := (triangleRegularPlaneHomeomorph.symm : C(TwicePuncturedPlane, _)).comp
      ((planeInverse : C(TwicePuncturedPlane, TwicePuncturedPlane)).comp (S.map.comp rev))
    initial := ?_
    final := ?_
    closed := ?_ }
  · intro t
    change triangleRegularPlaneHomeomorph.symm
      (planeInverse (S.map (0, unitInterval.symm t))) = nativeLoop controlledHeight t
    apply triangleRegularPlaneHomeomorph.injective
    rw [Homeomorph.apply_symm_apply]
    apply Subtype.ext
    change ((S.map (0, unitInterval.symm t) : ℂ))⁻¹ = _
    rw [S.initial]
    exact (nativeLoop_coordinate controlledHeight t).symm
  · intro t
    change triangleRegularPlaneHomeomorph.symm
      (planeInverse (S.map (1, unitInterval.symm t))) = inverseRegularMeridian t
    rw [S.final]
    rfl
  · intro s
    change triangleRegularPlaneHomeomorph.symm
      (planeInverse (S.map (s, unitInterval.symm 0))) =
        triangleRegularPlaneHomeomorph.symm (planeInverse (S.map (s, unitInterval.symm 1)))
    simp only [unitInterval.symm_zero, unitInterval.symm_one]
    exact congrArg (fun z => triangleRegularPlaneHomeomorph.symm (planeInverse z)) (S.closed s).symm

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.Cusp
