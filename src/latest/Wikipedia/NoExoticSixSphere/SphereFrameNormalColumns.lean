import Wikipedia.NoExoticSixSphere.SphereTwoCapFrameNormalization

/-!
# The actual normal columns survive the source-coordinate normalizations

The source Jacobian blocks and their inverses fix every normal input vector.
So do the pole-normalized localized changes. Consequently the two-cap frame
map and both input reference maps retain the original manifold normal frame
at their respective actual basepoints.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere

namespace SphereThreeTangentFrame

open GLOrthonormalization FrameBlockCoordinates

theorem sourceBlockJacobianEquiv_normal (k : ℕ) (u : Sphere 3 → Sphere 3) (x : Sphere 3)
    (hu : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ u x) (v : Vector k) :
    sourceBlockJacobianEquiv k u x hu (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3))) =
      EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3)) := by
  change sourceBlockJacobian k u x (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3))) = _
  rw [sourceBlockJacobian, identityBlockOperator_apply,
    ContinuousLinearEquiv.apply_symm_apply, map_zero]

theorem inverse_sourceBlockJacobianEquiv_normal (k : ℕ) (u : Sphere 3 → Sphere 3)
    (x : Sphere 3) (hu : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ u x) (v : Vector k) :
    (sourceBlockJacobianEquiv k u x hu).symm
        (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3))) =
      EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3)) := by
  apply (sourceBlockJacobianEquiv k u x hu).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, sourceBlockJacobianEquiv_normal]

end SphereThreeTangentFrame

namespace Stiefel.Monomorphism

open GLOrthonormalization SphereHemisphereRetraction SphereSumNeck

variable {N k : ℕ} (V W : North → Vector (k + 3) ≃L[ℝ] Vector (k + 3))
  (hV : Continuous (fun x ↦ (V x).toContinuousLinearMap))
  (hW : Continuous (fun x ↦ (W x).toContinuousLinearMap))

theorem basedSourceCoordinates_normal
    (hfix : ∀ x v, V x (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3))) =
      EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3))) (x : North) (v : Vector k) :
    basedSourceCoordinates V x (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3))) =
      EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3)) := by
  have hi : (V (ClosedHemisphere.center (spherePole 3))).symm
      (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3))) =
        EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3)) := by
    apply (V (ClosedHemisphere.center (spherePole 3))).injective
    rw [ContinuousLinearEquiv.apply_symm_apply, hfix]
  rw [basedSourceCoordinates_apply, hi, hfix]

theorem localizedSourceRecoordinateAlong_normal
    (hfix : ∀ x v, V x (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3))) =
      EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3)))
    (ρ : Sphere 3 ≃ₜ Sphere 3) (F : C(Sphere 3, Space N (k + 3)))
    (x : Sphere 3) (v : Vector k) :
    (localizedSourceRecoordinateAlong V hV ρ F x).val
        (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3))) =
      (F x).val (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3))) := by
  change (F x).val (basedSourceCoordinates V _
    (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3)))) = _
  rw [basedSourceCoordinates_normal V hfix]

theorem twoCapSourceRecoordinate_normal
    (hfixV : ∀ x v, V x (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3))) =
      EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3)))
    (hfixW : ∀ x v, W x (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3))) =
      EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3)))
    (F : C(Sphere 3, Space N (k + 3))) (x : Sphere 3) (v : Vector k) :
    (twoCapSourceRecoordinate V W hV hW F x).val
        (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3))) =
      (F x).val (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3))) := by
  unfold twoCapSourceRecoordinate
  rw [localizedSourceRecoordinateAlong_normal W hW hfixW,
    localizedSourceRecoordinateAlong_normal V hV hfixV]

end Stiefel.Monomorphism

namespace SphereSumNeck

open GLOrthonormalization SphereHemisphereRetraction SphereThreeTangentFrame

theorem northCapInverseJacobian_normal (k : ℕ) (ε : ℝ) (hε : 0 < ε)
    (x : North) (v : Vector k) :
    northCapInverseJacobian k ε hε x (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3))) =
      EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3)) :=
  inverse_sourceBlockJacobianEquiv_normal _ _ _ _ v

theorem southCapInverseJacobian_normal (k : ℕ) (ε : ℝ) (hε : 0 < ε)
    (x : North) (v : Vector k) :
    southCapInverseJacobian k ε hε x (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3))) =
      EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3)) :=
  inverse_sourceBlockJacobianEquiv_normal _ _ _ _ v

end SphereSumNeck

namespace EuclideanEmbedding

open GLOrthonormalization Stiefel SphereHemisphereRetraction SphereSumNeck SphereThreeTangentFrame

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (ν : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)

theorem sphereFrameOperator_normal (f : Sphere 3 → M) (x : Sphere 3)
    (v : Vector (e.ambientDimension - 6)) :
    e.sphereFrameOperator ν f x (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3))) =
      (ν.orthonormal (f x)).val v := by
  change OperatorSum.operator (ν.orthonormal (f x)).val _
    (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3))) = _
  rw [OperatorSum.operator_apply, ContinuousLinearEquiv.apply_symm_apply, map_zero, add_zero]

variable (K : C(Sphere 3, M)) (hK : ContMDiff (𝓡 3) (𝓡 6) ∞ K)
  (hKi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) K x)) (ε : ℝ) (hε : 0 < ε)

theorem twoCapNormalizedFrameMap_normal (x : Sphere 3) (v : Vector (e.ambientDimension - 6)) :
    (e.twoCapNormalizedFrameMap ν K hK hKi ε hε x).val
        (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3))) =
      (ν.orthonormal (K x)).val v := by
  change (Monomorphism.twoCapSourceRecoordinate _ _ _ _ _ x).val _ = _
  rw [Monomorphism.twoCapSourceRecoordinate_normal _ _ _ _
    (northCapInverseJacobian_normal _ ε hε) (southCapInverseJacobian_normal _ ε hε)]
  exact e.sphereFrameOperator_normal ν K x v

theorem northCapReferenceFrameMap_normal (x : Sphere 3) (v : Vector (e.ambientDimension - 6)) :
    (e.northCapReferenceFrameMap ν K hK hKi ε hε x).val
        (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3))) =
      (ν.orthonormal (K (northCapHomeomorph ε hε x))).val v := by
  have hi : (northCapInverseJacobian (e.ambientDimension - 6) ε hε
      (ClosedHemisphere.center (spherePole 3))).symm
        (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3))) =
      EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3)) := by
    apply (northCapInverseJacobian (e.ambientDimension - 6) ε hε _).injective
    rw [ContinuousLinearEquiv.apply_symm_apply, northCapInverseJacobian_normal]
  change e.sphereFrameOperator ν K (northCapHomeomorph ε hε x)
    ((northCapInverseJacobian (e.ambientDimension - 6) ε hε _).symm
      (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3)))) = _
  rw [hi]
  exact e.sphereFrameOperator_normal ν K _ v

theorem southCapReferenceFrameMap_normal (x : Sphere 3) (v : Vector (e.ambientDimension - 6)) :
    (e.southCapReferenceFrameMap ν K hK hKi ε hε x).val
        (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3))) =
      (ν.orthonormal (K (southCapHomeomorph ε hε x))).val v := by
  have hi : (southCapInverseJacobian (e.ambientDimension - 6) ε hε
      (ClosedHemisphere.center (spherePole 3))).symm
        (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3))) =
      EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3)) := by
    apply (southCapInverseJacobian (e.ambientDimension - 6) ε hε _).injective
    rw [ContinuousLinearEquiv.apply_symm_apply, southCapInverseJacobian_normal]
  change e.sphereFrameOperator ν K (southCapHomeomorph ε hε x)
    ((southCapInverseJacobian (e.ambientDimension - 6) ε hε _).symm
      (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3)))) = _
  rw [hi]
  exact e.sphereFrameOperator_normal ν K _ v

end EuclideanEmbedding
end NoExoticSixSphere
