import Wikipedia.HopfProblem.DegreeCollapseRadialHopfStableVanishing
import Wikipedia.NoExoticSixSphere.QuaternionicHopfPolynomial
import Wikipedia.NoExoticSixSphere.OrthogonalCompactness

/-!
# The explicit quaternionic polynomial is the orthogonal-family Hopf map

The unit quaternion a acts on b by a conjugate(b). This is a continuous
family of actual real orthogonal operators. Its radial extension is
literal quaternionic multiplication followed by conjugation, including
the zero first vector. The original polynomial Hopf map consequently
agrees exactly with the family construction in its existing coordinates.
-/

noncomputable section

open scoped Topology Quaternion
open NoExoticSixSphere GLOrthonormalization

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfFamily

open Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration
open HopfBlockCoordinates HopfBlockVanishing RadialSphereAction

abbrev quatCoordinates : ℍ ≃ₗᵢ[ℝ] Vector 4 := Quaternion.linearIsometryEquivTuple

def operator (a : Sphere 3) : Vector 4 →L[ℝ] Vector 4 :=
  quatCoordinates.toContinuousLinearMap.comp
    (((ContinuousLinearMap.mul ℝ ℍ (quatCoordinates.symm a.val)).comp
      QuaternionicHopf.conjugation).comp quatCoordinates.symm.toContinuousLinearMap)

theorem operator_apply (a : Sphere 3) (b : Vector 4) :
    operator a b = quatCoordinates (quatCoordinates.symm a.val * star (quatCoordinates.symm b)) :=
  rfl

theorem operator_norm (a : Sphere 3) (b : Vector 4) : ‖operator a b‖ = ‖b‖ := by
  simp only [operator_apply, quatCoordinates.norm_map, norm_mul, Quaternion.norm_star,
    quatCoordinates.symm.norm_map, mem_sphere_zero_iff_norm.mp a.property, one_mul]

theorem continuous_operator : Continuous operator := by
  apply continuous_clm_apply.mpr
  intro b
  change Continuous (fun a : Sphere 3 ↦
    quatCoordinates (quatCoordinates.symm a.val * star (quatCoordinates.symm b)))
  exact quatCoordinates.continuous.comp
    ((quatCoordinates.symm.continuous.comp continuous_subtype_val).mul continuous_const)

def orthogonal (a : Sphere 3) : OrthogonalOperators 4 :=
  ⟨⟨operator a, OrthogonalCompactness.normPreserving_isInvertible (operator a) (operator_norm a)⟩,
    operator_norm a⟩

def family : C(Sphere 3, OrthogonalOperators 4) :=
  ⟨orthogonal, (continuous_operator.subtype_mk _).subtype_mk _⟩

theorem family_apply (a : Sphere 3) (b : Vector 4) :
    (family a).val.val b =
      quatCoordinates (quatCoordinates.symm a.val * star (quatCoordinates.symm b)) := rfl

def sourceCoordinates : WithLp 2 (Vector 4 × Vector 4) ≃ₗᵢ[ℝ] Vector 8 :=
  (LinearIsometryEquiv.withLpProdCongr 2 quatCoordinates.symm quatCoordinates.symm).trans
    planeCoordinates

theorem first_sourceCoordinates (x : WithLp 2 (Vector 4 × Vector 4)) :
    QuaternionicHopf.first (sourceCoordinates x) = quatCoordinates.symm x.fst := by
  change (planeCoordinates.symm (planeCoordinates
    (WithLp.toLp 2 (quatCoordinates.symm x.fst, quatCoordinates.symm x.snd)))).fst = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem second_sourceCoordinates (x : WithLp 2 (Vector 4 × Vector 4)) :
    QuaternionicHopf.second (sourceCoordinates x) = quatCoordinates.symm x.snd := by
  change (planeCoordinates.symm (planeCoordinates
    (WithLp.toLp 2 (quatCoordinates.symm x.fst, quatCoordinates.symm x.snd)))).snd = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem radial_formula (a b : Vector 4) :
    value (OrthogonalHopfMap.action (parameterize family)) () a b =
      quatCoordinates (quatCoordinates.symm a * star (quatCoordinates.symm b)) := by
  by_cases ha : a = 0
  · subst a
    simp only [value_zero, map_zero, zero_mul]
  · rw [value_of_ne_zero _ _ _ _ ha]
    change ‖a‖ • quatCoordinates
      (quatCoordinates.symm (‖a‖⁻¹ • a) * star (quatCoordinates.symm b)) = _
    rw [quatCoordinates.symm.map_smul, smul_mul_assoc, ← quatCoordinates.map_smul,
      smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha), one_smul]

theorem polynomial_identity (x : WithLp 2 (Vector 4 × Vector 4)) :
    RadialJoinSuspension.leftCoordinates 3
      (OrthogonalHopfMap.vector (parameterize family) () x) =
        QuaternionicHopf.polynomial (sourceCoordinates x) := by
  symm
  rw [QuaternionicHopf.polynomial, first_sourceCoordinates, second_sourceCoordinates]
  simp only [← QuaternionicHopf.norm_sq_eq_normSq, quatCoordinates.symm.norm_map]
  change SphereCylinder.join 3 (‖x.fst‖ ^ 2 - ‖x.snd‖ ^ 2,
    quatCoordinates ((2 : ℝ) • (quatCoordinates.symm x.fst * star (quatCoordinates.symm x.snd)))) =
      SphereCylinder.join 3 (‖x.fst‖ ^ 2 - ‖x.snd‖ ^ 2,
        (2 : ℝ) • value (OrthogonalHopfMap.action (parameterize family)) () x.fst x.snd)
  rw [radial_formula, quatCoordinates.map_smul]

theorem sphereMap_square (x : UnitSphere (WithLp 2 (Vector 4 × Vector 4))) :
    unitSphereCoordinates (RadialJoinSuspension.leftCoordinates 3)
      (OrthogonalHopfMap.sphereMap family x) =
    QuaternionicHopf.sphereMap (unitSphereCoordinates sourceCoordinates x) :=
  Subtype.ext (polynomial_identity x.val)

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfFamily
