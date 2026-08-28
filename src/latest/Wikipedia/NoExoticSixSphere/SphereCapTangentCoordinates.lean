import Wikipedia.NoExoticSixSphere.SphereTwoCapFrameNormalization

/-!
# Source-only tangent coordinates for the two cap normalizations

The actual normal-extended source Jacobians are identity-block extensions of
three-dimensional equivalences. Their inverses, pole corrections, and both
localized changes retain this form. Thus their tangent coordinate field is
independent of the target manifold and the number of normal columns.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere

namespace FrameBlockCoordinates

open GLOrthonormalization

theorem identityBlockOperator_comp (k : ℕ) {n m N : ℕ}
    (A : Vector m →L[ℝ] Vector N) (B : Vector n →L[ℝ] Vector m) :
    (identityBlockOperator k A).comp (identityBlockOperator k B) =
      identityBlockOperator k (A.comp B) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, identityBlockOperator_apply,
    ContinuousLinearEquiv.apply_symm_apply]

def identityBlockEquiv (k : ℕ) {n N : ℕ} (A : Vector n ≃L[ℝ] Vector N) :
    Vector (k + n) ≃L[ℝ] Vector (k + N) :=
  EuclideanSpace.finAddEquivProd.trans
    (((ContinuousLinearEquiv.refl ℝ (Vector k)).prodCongr A).trans
      EuclideanSpace.finAddEquivProd.symm)

theorem identityBlockEquiv_toContinuousLinearMap (k : ℕ) {n N : ℕ}
    (A : Vector n ≃L[ℝ] Vector N) :
    (identityBlockEquiv k A).toContinuousLinearMap =
      identityBlockOperator k A.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem identityBlockEquiv_symm (k : ℕ) {n N : ℕ} (A : Vector n ≃L[ℝ] Vector N) :
    (identityBlockEquiv k A).symm = identityBlockEquiv k A.symm := by
  apply ContinuousLinearEquiv.ext
  funext v
  apply (identityBlockEquiv k A).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  change v = identityBlockOperator k A.toContinuousLinearMap
    (identityBlockOperator k A.symm.toContinuousLinearMap v)
  simp only [identityBlockOperator_apply, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.coe_coe]
  exact (EuclideanSpace.finAddEquivProd.symm_apply_apply v).symm

theorem identityBlockEquiv_trans (k : ℕ) {n m N : ℕ}
    (A : Vector n ≃L[ℝ] Vector m) (B : Vector m ≃L[ℝ] Vector N) :
    (identityBlockEquiv k A).trans (identityBlockEquiv k B) =
      identityBlockEquiv k (A.trans B) := by
  apply ContinuousLinearEquiv.ext
  funext v
  change identityBlockOperator k B.toContinuousLinearMap
    (identityBlockOperator k A.toContinuousLinearMap v) =
      identityBlockOperator k (A.trans B).toContinuousLinearMap v
  simp only [identityBlockOperator_apply, ContinuousLinearEquiv.apply_symm_apply]
  rfl

end FrameBlockCoordinates

namespace HemisphereSourceCoordinates

open GLOrthonormalization SphereThreeTangentFrame SphereHemisphereRetraction FrameBlockCoordinates

variable (u ρ : Sphere 3 ≃ₜ Sphere 3)
  (hu : ∀ x : North, IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ u (ρ x.val))

def tangentInverseJacobian (x : North) : Vector 3 ≃L[ℝ] Vector 3 :=
  (sourceJacobianEquiv u (ρ x.val) (hu x)).symm

theorem inverseJacobian_eq_identityBlock (k : ℕ) (x : North) :
    inverseJacobian k u ρ hu x = identityBlockEquiv k (tangentInverseJacobian u ρ hu x) :=
  identityBlockEquiv_symm k (sourceJacobianEquiv u (ρ x.val) (hu x))

end HemisphereSourceCoordinates

namespace Stiefel.Monomorphism

open GLOrthonormalization SphereHemisphereRetraction FrameBlockCoordinates

theorem basedSourceCoordinates_identityBlock (k : ℕ) {n : ℕ}
    (V : North → Vector n ≃L[ℝ] Vector n) (x : North) :
    basedSourceCoordinates (fun y ↦ identityBlockEquiv k (V y)) x =
      identityBlockEquiv k (basedSourceCoordinates V x) := by
  unfold basedSourceCoordinates
  rw [identityBlockEquiv_symm, identityBlockEquiv_trans]

theorem localizedSourceRecoordinateAlong_apply {N n : ℕ}
    (V : North → Vector n ≃L[ℝ] Vector n)
    (hV : Continuous (fun x ↦ (V x).toContinuousLinearMap))
    (ρ : Sphere 3 ≃ₜ Sphere 3) (F : C(Sphere 3, Space N n)) (x : Sphere 3) :
    (localizedSourceRecoordinateAlong V hV ρ F x).val =
      (F x).val.comp (basedSourceCoordinates V
        (LocalizedHemisphereRetraction.retraction (ρ.symm x))).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro v
  rfl

end Stiefel.Monomorphism

namespace SphereSumNeck

open GLOrthonormalization SphereHemisphereRetraction HemisphereSourceCoordinates
open Stiefel.Monomorphism FrameBlockCoordinates

def northTangentInverseJacobian (ε : ℝ) (hε : 0 < ε) :
    North → Vector 3 ≃L[ℝ] Vector 3 :=
  tangentInverseJacobian (northCapHomeomorph ε hε) northRetainedCap
    (fun x ↦ isLocalDiffeomorphAt_northCapHomeomorph ε hε
      (half_lt_head_of_northRegion (northRetainedCap_mem_northRegion x)))

def southTangentInverseJacobian (ε : ℝ) (hε : 0 < ε) :
    North → Vector 3 ≃L[ℝ] Vector 3 :=
  tangentInverseJacobian (southCapHomeomorph ε hε) southRetainedCap
    (fun x ↦ isLocalDiffeomorphAt_southCapHomeomorph ε hε
      (southRetainedCap_mem_southRegion x))

theorem northCapInverseJacobian_eq_identityBlock (k : ℕ) (ε : ℝ) (hε : 0 < ε) (x : North) :
    northCapInverseJacobian k ε hε x =
      identityBlockEquiv k (northTangentInverseJacobian ε hε x) :=
  inverseJacobian_eq_identityBlock _ _ _ k x

theorem southCapInverseJacobian_eq_identityBlock (k : ℕ) (ε : ℝ) (hε : 0 < ε) (x : North) :
    southCapInverseJacobian k ε hε x =
      identityBlockEquiv k (southTangentInverseJacobian ε hε x) :=
  inverseJacobian_eq_identityBlock _ _ _ k x

def localizedTangentCoordinates (V : North → Vector 3 ≃L[ℝ] Vector 3)
    (ρ : Sphere 3 ≃ₜ Sphere 3) (x : Sphere 3) : Vector 3 ≃L[ℝ] Vector 3 :=
  basedSourceCoordinates V (LocalizedHemisphereRetraction.retraction (ρ.symm x))

def twoCapTangentCoordinates (ε : ℝ) (hε : 0 < ε) (x : Sphere 3) :
    Vector 3 ≃L[ℝ] Vector 3 :=
  (localizedTangentCoordinates (southTangentInverseJacobian ε hε) southRetainedCap x).trans
    (localizedTangentCoordinates (northTangentInverseJacobian ε hε) northRetainedCap x)

theorem twoCapSourceRecoordinate_apply {N : ℕ} (k : ℕ) (ε : ℝ) (hε : 0 < ε)
    (F : C(Sphere 3, Stiefel.Monomorphism.Space N (k + 3))) (x : Sphere 3) :
    (twoCapSourceRecoordinate (northCapInverseJacobian k ε hε)
        (southCapInverseJacobian k ε hε) (continuous_northCapInverseJacobian k ε hε)
        (continuous_southCapInverseJacobian k ε hε) F x).val =
      (F x).val.comp
        (identityBlockOperator k (twoCapTangentCoordinates ε hε x).toContinuousLinearMap) := by
  have hN : northCapInverseJacobian k ε hε =
      fun y ↦ identityBlockEquiv k (northTangentInverseJacobian ε hε y) :=
    funext (northCapInverseJacobian_eq_identityBlock k ε hε)
  have hS : southCapInverseJacobian k ε hε =
      fun y ↦ identityBlockEquiv k (southTangentInverseJacobian ε hε y) :=
    funext (southCapInverseJacobian_eq_identityBlock k ε hε)
  unfold twoCapSourceRecoordinate
  rw [localizedSourceRecoordinateAlong_apply, localizedSourceRecoordinateAlong_apply]
  rw [hN, hS, basedSourceCoordinates_identityBlock, basedSourceCoordinates_identityBlock]
  rw [identityBlockEquiv_toContinuousLinearMap, identityBlockEquiv_toContinuousLinearMap,
    ContinuousLinearMap.comp_assoc, identityBlockOperator_comp]
  rfl

end SphereSumNeck

end NoExoticSixSphere
