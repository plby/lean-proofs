import Wikipedia.NoExoticSixSphere.JamesSphereAttachingSmashHomology
import Wikipedia.NoExoticSixSphere.JamesSphereAttachingCubeGenerator
import Wikipedia.NoExoticSixSphere.SixthHurewiczNativeNaturality

/-!
# Exact pairing coordinates and the sixth Hurewicz comparison of the actual loop cubes

The ORIGINAL pairing of the two tail spheres equals the ORIGINAL
six-cube quotient, including all collapsed faces. Thus the corrected
smash map has exactly the corrected native six-cube. Naturality then
transfers the proved H6 map equality to the actual sixth Hurewicz
classes. Uncurrying the other cube is literally the Moore meridian
commutator's seven-cube. No equality in native homotopy is inferred
from equality of these Hurewicz classes.
-/

noncomputable section

open scoped Topology unitInterval OnePoint
open Wikipedia.HopfProblem

namespace NoExoticSixSphere.JamesSphere.AttachingSquare

theorem pairing_tail_cube (v : Parameter 3) :
    SecondStage.arrayPairing 3 (sphereParameters 3 v) =
      SmoothCube.quotient 6 (tailCoordinates 3 v) := by
  by_cases hv : v ∈ tailBoundary 3
  · have hp : sphereParameters 3 v ∈ SphereMooreCommutator.Boundary 3 := by
      obtain ⟨i, hi⟩ := hv
      exact ⟨i, SmoothCube.quotient_boundary 3 _ hi⟩
    rw [(SphereMooreCommutator.arrayPairing_pole_iff 3 _).mpr hp,
      SmoothCube.quotient_boundary 6 _ ((tailCoordinates_boundary 3 v).mp hv)]
  · have h₀ : v 0 ∉ Cube.boundary (Fin 3) := fun h ↦ hv ⟨0, h⟩
    have h₁ : v 1 ∉ Cube.boundary (Fin 3) := fun h ↦ hv ⟨1, h⟩
    have ht : tailCoordinates 3 v ∉ Cube.boundary (Fin 6) :=
      fun h ↦ hv ((tailCoordinates_boundary 3 v).mpr h)
    change euclideanOnePointSphere 6
      ((EuclideanFactorProduct.productCoordinates 3 3).onePointCongr
        (OnePointProduct.map ((euclideanOnePointSphere 3).symm (SmoothCube.quotient 3 (v 0)),
          (euclideanOnePointSphere 3).symm (SmoothCube.quotient 3 (v 1))))) = _
    rw [CubicalSphereSuspension.quotient_finite_coordinates 3 (v 0) h₀,
      CubicalSphereSuspension.quotient_finite_coordinates 3 (v 1) h₁, OnePointProduct.map_coe]
    change euclideanOnePointSphere 6
      (↑(EuclideanFactorProduct.productCoordinates 3 3
        (SmoothCube.coordinate 3 (SmoothCube.vectorOfCube 3 (v 0)),
          SmoothCube.coordinate 3 (SmoothCube.vectorOfCube 3 (v 1))))) = _
    have he : EuclideanFactorProduct.productCoordinates 3 3
        (SmoothCube.coordinate 3 (SmoothCube.vectorOfCube 3 (v 0)),
          SmoothCube.coordinate 3 (SmoothCube.vectorOfCube 3 (v 1))) =
        SmoothCube.coordinate 6 (SmoothCube.vectorOfCube 6 (tailCoordinates 3 v)) := by
      ext i
      fin_cases i <;> rfl
    rw [he]
    exact (congrArg (euclideanOnePointSphere 6)
      (CubicalSphereSuspension.quotient_finite_coordinates 6 _ ht)).symm.trans
        ((euclideanOnePointSphere 6).apply_symm_apply _)

theorem correctedSmashSphere_cube (u : Fin 6 → I) :
    correctedSmashSphere 3 (by decide) (SmoothCube.quotient 6 u) = correctedCube 3 u := by
  have hp := pairing_tail_cube ((tailCoordinates 3).symm u)
  rw [Homeomorph.apply_symm_apply] at hp
  rw [← hp, correctedSmashSphere_pairing, correctedSphereLoops_parameters]
  rfl

theorem correctedSmashSphere_toGenLoop :
    SmoothCube.toGenLoop ⟨correctedSmashSphere 3 (by decide),
      correctedSmashSphere_pole 3 (by decide)⟩ = correctedCube 3 := by
  apply Subtype.ext
  apply ContinuousMap.ext
  exact correctedSmashSphere_cube

theorem normalizedSmashSphere_pole (n : ℕ) :
    normalizedSmashSphere n (spherePole (n + n)) = Path.refl (spherePole (n + 1)) := by
  change reorderPaths n (Moore.Loop.toPath (MeridianCommutator.sphereMap n
    (spherePole (n + n)))) = _
  rw [MeridianCommutator.sphereMap_pole, Moore.Loop.toPath_one, reorderPaths_refl]

def normalizedSmashCube : GenLoop (Fin 6) (Path (spherePole 4) (spherePole 4))
    (Path.refl (spherePole 4)) :=
  SmoothCube.toGenLoop ⟨normalizedSmashSphere 3, normalizedSmashSphere_pole 3⟩

theorem normalizedSmashCube_uncurry :
    GeneralizedLoopCurrying.uncurry normalizedSmashCube = MeridianCommutator.fourLoop := rfl

theorem correctedCube_hurewicz :
    SixthHurewicz.hurewiczFunction (Path.refl (spherePole 4)) (Quotient.mk' (correctedCube 3)) =
      SixthHurewicz.hurewiczFunction (Path.refl (spherePole 4))
        (Quotient.mk' normalizedSmashCube) := by
  let c : π_ 6 (Sphere 6) (spherePole 6) :=
    SmoothCube.sphereClass ⟨ContinuousMap.id _, rfl⟩
  have hf := SixthHurewiczNative.natural (correctedSmashSphere 3 (by decide))
    (spherePole 6) (Path.refl (spherePole 4)) (correctedSmashSphere_pole 3 (by decide)) c
  have hg := SixthHurewiczNative.natural (normalizedSmashSphere 3)
    (spherePole 6) (Path.refl (spherePole 4)) (normalizedSmashSphere_pole 3) c
  have he := hf.symm.trans ((LinearMap.congr_fun correctedSmashSphere_homology
    (SixthHurewicz.hurewiczFunction (spherePole 6) c)).trans hg)
  change SixthHurewicz.hurewiczFunction (Path.refl (spherePole 4))
    (Quotient.mk' (SmoothCube.toGenLoop ⟨correctedSmashSphere 3 (by decide),
      correctedSmashSphere_pole 3 (by decide)⟩)) =
      SixthHurewicz.hurewiczFunction (Path.refl (spherePole 4))
        (Quotient.mk' normalizedSmashCube) at he
  rwa [correctedSmashSphere_toGenLoop] at he

end NoExoticSixSphere.JamesSphere.AttachingSquare
