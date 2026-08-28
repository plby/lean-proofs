import Wikipedia.NoExoticSixSphere.SphereRadialFrameObstruction
import Wikipedia.NoExoticSixSphere.SphereLinearDiskExtension

/-!
# The inverse radial frame retains the nonzero extension obstruction

Quaternionic conjugation is a genuine linear sphere reparametrization.
The inverse radial coordinates are the radial coordinates at the conjugate
point, with two fixed reference-coordinate changes. These exact changes
transport the already proved obstruction without assuming anything about
extension of a sphere-dependent coordinate field.
-/

noncomputable section

open Function
open scoped Quaternion

namespace NoExoticSixSphere.SphereThreeTangentFrame

open GLOrthonormalization Stiefel DiskBoundary

local instance : StarModule ℝ ℍ where
  star_smul r q := by simp [Quaternion.star_smul]

def quaternionConjugationIsometry : ℍ ≃ₗᵢ[ℝ] ℍ where
  toLinearEquiv := (starL' ℝ : ℍ ≃L[ℝ] ℍ).toLinearEquiv
  norm_map' := norm_star

def sphereConjugationCoordinates : Vector 4 ≃ₗᵢ[ℝ] Vector 4 :=
  (Quaternion.linearIsometryEquivTuple.symm.trans quaternionConjugationIsometry).trans
    Quaternion.linearIsometryEquivTuple

def sphereConjugation : C(Sphere 3, Sphere 3) :=
  SphereLinearReparametrization.sphereMap sphereConjugationCoordinates

theorem sphereConjugation_quaternion (s : Sphere 3) :
    Quaternion.linearIsometryEquivTuple.symm (sphereConjugation s).val =
      star (Quaternion.linearIsometryEquivTuple.symm s.val) := by
  change Quaternion.linearIsometryEquivTuple.symm
    (Quaternion.linearIsometryEquivTuple
      (star (Quaternion.linearIsometryEquivTuple.symm s.val))) = _
  exact Quaternion.linearIsometryEquivTuple.symm_apply_apply _

theorem sphereQuaternion_mul_star (s : Sphere 3) :
    Quaternion.linearIsometryEquivTuple.symm s.val *
      star (Quaternion.linearIsometryEquivTuple.symm s.val) = 1 := by
  rw [Quaternion.self_mul_star, Quaternion.normSq_eq_norm_mul_self,
    Quaternion.linearIsometryEquivTuple.symm.norm_map, ClosedHemisphere.unit_norm,
    one_mul, Quaternion.coe_one]

def radialReference : Sphere 3 := QuaternionSphere.sphereHomeomorph QuaternionSphere.one

theorem radialReference_quaternion :
    Quaternion.linearIsometryEquivTuple.symm radialReference.val = 1 :=
  Quaternion.linearIsometryEquivTuple.symm_apply_apply 1

theorem radialCoordinates_quaternion (s : Sphere 3) (v : Vector 4) :
    Quaternion.linearIsometryEquivTuple.symm (radialCoordinates s v) =
      Quaternion.linearIsometryEquivTuple.symm s.val *
        imaginary (EuclideanSpace.finAddEquivProd (n := 3) (m := 1) v).1 +
      EuclideanTailCoordinates.scalar.symm
        (EuclideanSpace.finAddEquivProd (n := 3) (m := 1) v).2 •
          Quaternion.linearIsometryEquivTuple.symm s.val := by
  rw [radialCoordinates_apply, map_add, map_smul,
    operator_apply, LinearIsometryEquiv.symm_apply_apply]

theorem radialCoordinates_left_factorization (s : Sphere 3) (v : Vector 4) :
    Quaternion.linearIsometryEquivTuple.symm (radialCoordinates s v) =
      Quaternion.linearIsometryEquivTuple.symm s.val *
        Quaternion.linearIsometryEquivTuple.symm (radialCoordinates radialReference v) := by
  rw [radialCoordinates_quaternion, radialCoordinates_quaternion,
    radialReference_quaternion, one_mul, mul_add, mul_smul_comm, mul_one]

theorem inverse_radialCoordinates_formula (s : Sphere 3) (v : Vector 4) :
    (radialCoordinates s).symm v = (radialCoordinates radialReference).symm
      (radialCoordinates (sphereConjugation s) ((radialCoordinates radialReference).symm v)) := by
  apply (radialCoordinates s).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  symm
  apply Quaternion.linearIsometryEquivTuple.symm.injective
  rw [radialCoordinates_left_factorization s, ContinuousLinearEquiv.apply_symm_apply,
    radialCoordinates_left_factorization (sphereConjugation s),
    ContinuousLinearEquiv.apply_symm_apply, sphereConjugation_quaternion,
    ← mul_assoc, sphereQuaternion_mul_star, one_mul]

def liftedInverseRadialOperator (s : Sphere 3) : Vector 4 →L[ℝ] Vector 7 :=
  EuclideanSpace.finAddEquivProd.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.inl ℝ (Vector 4) (Vector 3)).comp
      (radialCoordinates s).symm.toContinuousLinearMap)

theorem liftedInverseRadialOperator_apply (s : Sphere 3) (v : Vector 4) :
    liftedInverseRadialOperator s v = EuclideanSpace.finAddEquivProd.symm
      ((radialCoordinates s).symm v, (0 : Vector 3)) := rfl

def liftedInverseRadialMap : C(Sphere 3, Monomorphism.Space 7 4) where
  toFun s := ⟨liftedInverseRadialOperator s, by
    intro v w h
    apply (radialCoordinates s).symm.injective
    have he := congrArg (fun z : Vector 7 ↦
      (EuclideanSpace.finAddEquivProd (n := 4) (m := 3) z).1) h
    simpa only [liftedInverseRadialOperator_apply,
      ContinuousLinearEquiv.apply_symm_apply] using he⟩
  continuous_toFun := by
    have h : Continuous liftedInverseRadialOperator := by
      apply continuous_clm_apply.mpr
      intro v
      simp only [liftedInverseRadialOperator_apply]
      exact EuclideanSpace.finAddEquivProd.symm.continuous.comp
        ((continuous_inverse_radialCoordinates.clm_apply continuous_const).prodMk continuous_const)
    exact h.subtype_mk _

def inverseRadialAmbientCoordinates : Vector 7 ≃L[ℝ] Vector 7 :=
  EuclideanSpace.finAddEquivProd.trans
    (((radialCoordinates radialReference).symm.prodCongr
      (ContinuousLinearEquiv.refl ℝ (Vector 3))).trans EuclideanSpace.finAddEquivProd.symm)

theorem inverseRadialAmbientCoordinates_apply (v : Vector 4) (w : Vector 3) :
    inverseRadialAmbientCoordinates (EuclideanSpace.finAddEquivProd.symm (v, w)) =
      EuclideanSpace.finAddEquivProd.symm ((radialCoordinates radialReference).symm v, w) := by
  change EuclideanSpace.finAddEquivProd.symm
    ((radialCoordinates radialReference).symm
      (EuclideanSpace.finAddEquivProd (EuclideanSpace.finAddEquivProd.symm (v, w))).1,
      (EuclideanSpace.finAddEquivProd (EuclideanSpace.finAddEquivProd.symm (v, w))).2) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]

theorem liftedInverseRadialMap_recoordinate (s : Sphere 3) :
    liftedInverseRadialMap s = Monomorphism.recoordinate inverseRadialAmbientCoordinates
      (radialCoordinates radialReference).symm (liftedRadialMap (sphereConjugation s)) := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro v
  change liftedInverseRadialOperator s v = inverseRadialAmbientCoordinates
    (liftedRadialOperator (sphereConjugation s) ((radialCoordinates radialReference).symm v))
  rw [liftedInverseRadialOperator_apply, liftedRadialOperator_apply,
    inverseRadialAmbientCoordinates_apply, inverse_radialCoordinates_formula]

theorem liftedInverseRadialMap_not_extends : ¬ Extends liftedInverseRadialMap := by
  have he : Extends liftedInverseRadialMap ↔ Extends (liftedRadialMap.comp sphereConjugation) :=
    Monomorphism.extends_recoordinate_iff (fun _ ↦ inverseRadialAmbientCoordinates)
      (fun _ ↦ (radialCoordinates radialReference).symm)
      continuous_const continuous_const continuous_const continuous_const
      (liftedRadialMap.comp sphereConjugation) liftedInverseRadialMap
      liftedInverseRadialMap_recoordinate
  intro h
  apply liftedRadialMap_not_extends
  exact (SphereLinearReparametrization.extends_precomp_iff
    sphereConjugationCoordinates liftedRadialMap).mp (he.mp h)

end NoExoticSixSphere.SphereThreeTangentFrame
