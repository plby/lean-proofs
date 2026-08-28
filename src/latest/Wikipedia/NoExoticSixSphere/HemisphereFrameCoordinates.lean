import Wikipedia.NoExoticSixSphere.SphereHemisphereRetraction
import Wikipedia.NoExoticSixSphere.ContractedFrameCoordinates

/-!
# Extending hemisphere coordinate changes without changing frame parity

The actual folding retraction extends a continuous coordinate family from
the closed northern hemisphere to the entire sphere. Its constructed
contraction proves that this recoordinating operation preserves the original
frame obstruction, while retaining the given coordinate values on the cap.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.Monomorphism

open GLOrthonormalization SphereHemisphereRetraction

variable {N n N' n' : ℕ}
  (U : North → Vector N ≃L[ℝ] Vector N') (V : North → Vector n' ≃L[ℝ] Vector n)
  (hU : Continuous (fun p ↦ (U p).toContinuousLinearMap))
  (hV : Continuous (fun p ↦ (V p).toContinuousLinearMap))

def hemisphereRecoordinate (F : C(Sphere 3, Space N n)) : C(Sphere 3, Space N' n') :=
  parameterRecoordinate U V hU hV retraction F

theorem hemisphereRecoordinate_north (F : C(Sphere 3, Space N n)) (x : North) :
    hemisphereRecoordinate U V hU hV F x.val = recoordinate (U x) (V x) (F x.val) := by
  change recoordinate (U (retraction x.val)) (V (retraction x.val)) (F x.val) = _
  rw [retraction_north]

theorem sphereParityOfDimension_hemisphereRecoordinate
    (r s : ℕ) (hN : N = 3 + (r + 2)) (hn : n = r + 2)
    (hN' : N' = 3 + (s + 2)) (hn' : n' = s + 2)
    (F : C(Sphere 3, Space N n)) :
    sphereParityOfDimension s hN' hn' (hemisphereRecoordinate U V hU hV F) =
      sphereParityOfDimension r hN hn F :=
  sphereParityOfDimension_parameterRecoordinate U V hU hV r s hN hn hN' hn'
    retraction F (ClosedHemisphere.center (spherePole 3)) contraction

def hemisphereRecoordinateAlong (c : Sphere 3 ≃ₜ Sphere 3) (F : C(Sphere 3, Space N n)) :
    C(Sphere 3, Space N' n') :=
  parameterRecoordinate U V hU hV (retraction.comp (c.symm : C(Sphere 3, Sphere 3))) F

theorem hemisphereRecoordinateAlong_cap (c : Sphere 3 ≃ₜ Sphere 3)
    (F : C(Sphere 3, Space N n)) (x : North) :
    hemisphereRecoordinateAlong U V hU hV c F (c x.val) =
      recoordinate (U x) (V x) (F (c x.val)) := by
  change recoordinate (U (retraction (c.symm (c x.val))))
    (V (retraction (c.symm (c x.val)))) (F (c x.val)) = _
  rw [c.symm_apply_apply, retraction_north]

theorem sphereParityOfDimension_hemisphereRecoordinateAlong
    (r s : ℕ) (hN : N = 3 + (r + 2)) (hn : n = r + 2)
    (hN' : N' = 3 + (s + 2)) (hn' : n' = s + 2)
    (c : Sphere 3 ≃ₜ Sphere 3) (F : C(Sphere 3, Space N n)) :
    sphereParityOfDimension s hN' hn' (hemisphereRecoordinateAlong U V hU hV c F) =
      sphereParityOfDimension r hN hn F :=
  sphereParityOfDimension_parameterRecoordinate U V hU hV r s hN hn hN' hn'
    (retraction.comp (c.symm : C(Sphere 3, Sphere 3))) F
    (ClosedHemisphere.center (spherePole 3))
    (contraction.compContinuousMap (c.symm : C(Sphere 3, Sphere 3)))

end NoExoticSixSphere.Stiefel.Monomorphism
