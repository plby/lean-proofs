import Wikipedia.NoExoticSixSphere.SphereLocalizedHemisphereRetraction
import Wikipedia.NoExoticSixSphere.ContractedFrameCoordinates

/-!
# Local source coordinate changes fixing the opposite cap

Normalize a continuous coordinate family by its value at the northern pole,
then extend it through the localized hemisphere retraction. The extended
change preserves frame parity, has the specified normalized values on the
retained cap, and is exactly the identity on the opposite cap.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.Monomorphism

open GLOrthonormalization SphereHemisphereRetraction

variable {N n : ℕ} (V : North → Vector n ≃L[ℝ] Vector n)
  (hV : Continuous (fun x ↦ (V x).toContinuousLinearMap))

def basedSourceCoordinates (x : North) : Vector n ≃L[ℝ] Vector n :=
  (V (ClosedHemisphere.center (spherePole 3))).symm.trans (V x)

theorem basedSourceCoordinates_apply (x : North) (v : Vector n) :
    basedSourceCoordinates V x v = V x ((V (ClosedHemisphere.center (spherePole 3))).symm v) :=
  rfl

theorem basedSourceCoordinates_toContinuousLinearMap (x : North) :
    (basedSourceCoordinates V x).toContinuousLinearMap = (V x).toContinuousLinearMap.comp
      (V (ClosedHemisphere.center (spherePole 3))).symm.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro v
  rfl

include hV in
theorem continuous_basedSourceCoordinates :
    Continuous (fun x ↦ (basedSourceCoordinates V x).toContinuousLinearMap) := by
  simp_rw [basedSourceCoordinates_toContinuousLinearMap]
  exact hV.clm_comp continuous_const

theorem basedSourceCoordinates_center :
    basedSourceCoordinates V (ClosedHemisphere.center (spherePole 3)) =
      ContinuousLinearEquiv.refl ℝ (Vector n) := by
  apply ContinuousLinearEquiv.ext
  funext v
  exact (V (ClosedHemisphere.center (spherePole 3))).apply_symm_apply v

def localizedSourceRecoordinateAlong (ρ : Sphere 3 ≃ₜ Sphere 3)
    (F : C(Sphere 3, Space N n)) : C(Sphere 3, Space N n) :=
  parameterRecoordinate (fun _ ↦ ContinuousLinearEquiv.refl ℝ (Vector N))
    (basedSourceCoordinates V) continuous_const (continuous_basedSourceCoordinates V hV)
    (LocalizedHemisphereRetraction.retraction.comp (ρ.symm : C(Sphere 3, Sphere 3))) F

theorem localizedSourceRecoordinateAlong_cap (ρ : Sphere 3 ≃ₜ Sphere 3)
    (F : C(Sphere 3, Space N n)) (x : North) :
    localizedSourceRecoordinateAlong V hV ρ F (ρ x.val) =
      recoordinate (ContinuousLinearEquiv.refl ℝ (Vector N))
        (basedSourceCoordinates V x) (F (ρ x.val)) := by
  change recoordinate _ (basedSourceCoordinates V
    (LocalizedHemisphereRetraction.retraction (ρ.symm (ρ x.val)))) (F (ρ x.val)) = _
  rw [ρ.symm_apply_apply, LocalizedHemisphereRetraction.retraction_north]

theorem localizedSourceRecoordinateAlong_opposite (ρ : Sphere 3 ≃ₜ Sphere 3)
    (F : C(Sphere 3, Space N n)) (x : Sphere 3)
    (hx : (ρ.symm x).val 0 ≤ -(1 / 2 : ℝ)) :
    localizedSourceRecoordinateAlong V hV ρ F x = F x := by
  change recoordinate _ (basedSourceCoordinates V
    (LocalizedHemisphereRetraction.retraction (ρ.symm x))) (F x) = F x
  rw [LocalizedHemisphereRetraction.retraction_south _ hx, basedSourceCoordinates_center]
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem sphereParityOfDimension_localizedSourceRecoordinateAlong
    (r : ℕ) (hN : N = 3 + (r + 2)) (hn : n = r + 2)
    (ρ : Sphere 3 ≃ₜ Sphere 3) (F : C(Sphere 3, Space N n)) :
    sphereParityOfDimension r hN hn (localizedSourceRecoordinateAlong V hV ρ F) =
      sphereParityOfDimension r hN hn F :=
  sphereParityOfDimension_parameterRecoordinate
    (fun _ ↦ ContinuousLinearEquiv.refl ℝ (Vector N))
    (basedSourceCoordinates V) continuous_const (continuous_basedSourceCoordinates V hV)
    r r hN hn hN hn
    (LocalizedHemisphereRetraction.retraction.comp (ρ.symm : C(Sphere 3, Sphere 3))) F
    (ClosedHemisphere.center (spherePole 3))
    (LocalizedHemisphereRetraction.contraction.compContinuousMap (ρ.symm : C(Sphere 3, Sphere 3)))

def fixedSourceRecoordinate (C : Vector n ≃L[ℝ] Vector n)
    (F : C(Sphere 3, Space N n)) : C(Sphere 3, Space N n) :=
  (recoordinateHomeomorph (ContinuousLinearEquiv.refl ℝ (Vector N)) C : C(_, _)).comp F

theorem sphereParityOfDimension_fixedSourceRecoordinate
    (r : ℕ) (hN : N = 3 + (r + 2)) (hn : n = r + 2)
    (C : Vector n ≃L[ℝ] Vector n) (F : C(Sphere 3, Space N n)) :
    sphereParityOfDimension r hN hn (fixedSourceRecoordinate C F) =
      sphereParityOfDimension r hN hn F := by
  apply zmodTwo_eq_of_zero_iff
  rw [sphereParityOfDimension_zero_iff, sphereParityOfDimension_zero_iff]
  exact extends_recoordinate_iff (fun _ ↦ ContinuousLinearEquiv.refl ℝ (Vector N))
    (fun _ ↦ C) continuous_const continuous_const continuous_const continuous_const F
    (fixedSourceRecoordinate C F) (fun _ ↦ rfl)

end NoExoticSixSphere.Stiefel.Monomorphism
