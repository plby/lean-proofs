import Wikipedia.NoExoticSixSphere.PartialFrameSphereObstruction
import Wikipedia.HopfProblem.ThirdHurewiczNaturality
import Wikipedia.HopfProblem.CuspCentralHomologyAttachingCrossNull

/-!
# Frame-sphere parity is an actual singular homology evaluation

The sphere's fixed boundary-collapse cube gives an actual integral cycle
class. Naturality of the constructed Hurewicz map identifies its image with
the class defining frame parity. Consequently actual integral homology
relations among sphere maps give the corresponding parity relations.
No geometric relation between particular boundary spheres is assumed here.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel

open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology
open Wikipedia.HopfProblem.DegreeCollapse

def sphereThirdClass : SingularHomology (Sphere 3) 3 :=
  Wikipedia.HopfProblem.ThirdHurewicz.cubeHomologyClass
    (SphereCube.basedCube (ContinuousMap.id (Sphere 3)))

theorem sphereThirdClass_map {X : Type} [TopologicalSpace X] (f : C(Sphere 3, X)) :
    singularHomologyMap f 3 sphereThirdClass =
      Wikipedia.HopfProblem.ThirdHurewicz.cubeHomologyClass (SphereCube.basedCube f) :=
  Wikipedia.HopfProblem.ThirdHurewicz.cubeHomologyClass_natural f (SphereCube.point 3)
    (SphereCube.basedCube (ContinuousMap.id (Sphere 3)))

theorem sphereThirdObstruction_eq_homology (r : ℕ)
    (f : C(Sphere 3, Space (3 + (r + 2)) (r + 2))) :
    sphereThirdObstruction r f = stableThirdHomologyEquivZModTwo r
      (singularHomologyMap f 3 sphereThirdClass) := by
  rw [sphereThirdClass_map]
  rfl

theorem sphereThirdObstruction_zero_iff_homology (r : ℕ)
    (f : C(Sphere 3, Space (3 + (r + 2)) (r + 2))) :
    sphereThirdObstruction r f = 0 ↔ singularHomologyMap f 3 sphereThirdClass = 0 := by
  rw [sphereThirdObstruction_eq_homology, LinearEquiv.map_eq_zero_iff]

theorem sphereThirdObstruction_zero_iff_homologyMap (r : ℕ)
    (f : C(Sphere 3, Space (3 + (r + 2)) (r + 2))) :
    sphereThirdObstruction r f = 0 ↔ singularHomologyMap f 3 = 0 := by
  constructor
  · intro h
    obtain ⟨H⟩ := (sphereThirdObstruction_zero_iff r f).mp h
    exact Wikipedia.HopfProblem.CuspCentralHomology.singularHomologyMap_eq_zero_of_nullhomotopic
      f ⟨_, ⟨H.toHomotopy⟩⟩ 3 (by decide)
  · intro h
    rw [sphereThirdObstruction_zero_iff_homology, h, LinearMap.zero_apply]

theorem sphereThirdObstruction_precomp_homeomorph (r : ℕ)
    (f : C(Sphere 3, Space (3 + (r + 2)) (r + 2))) (e : Sphere 3 ≃ₜ Sphere 3) :
    sphereThirdObstruction r (f.comp (e : C(Sphere 3, Sphere 3))) =
      sphereThirdObstruction r f := by
  apply zmodTwo_eq_of_zero_iff
  rw [sphereThirdObstruction_zero_iff_homologyMap,
    sphereThirdObstruction_zero_iff_homologyMap, singularHomologyMap_comp]
  constructor
  · intro h
    apply LinearMap.ext
    intro b
    obtain ⟨a, ha⟩ := (homeomorphHomologyEquiv e 3).surjective b
    have he := LinearMap.congr_fun h a
    change singularHomologyMap f 3 (homeomorphHomologyEquiv e 3 a) = 0 at he
    rw [ha] at he
    exact he
  · intro h
    rw [h, LinearMap.zero_comp]

theorem sphereThirdObstruction_eq_of_homology {X : Type} [TopologicalSpace X]
    (r : ℕ) (F : C(X, Space (3 + (r + 2)) (r + 2))) (f g : C(Sphere 3, X))
    (h : singularHomologyMap f 3 sphereThirdClass =
      singularHomologyMap g 3 sphereThirdClass) :
    sphereThirdObstruction r (F.comp f) = sphereThirdObstruction r (F.comp g) := by
  rw [sphereThirdObstruction_eq_homology, sphereThirdObstruction_eq_homology,
    singularHomologyMap_comp, singularHomologyMap_comp, LinearMap.comp_apply,
    LinearMap.comp_apply, h]

theorem sphereThirdObstruction_sum_of_homology {X : Type} [TopologicalSpace X]
    {ι : Type*} [Fintype ι] (r : ℕ) (F : C(X, Space (3 + (r + 2)) (r + 2)))
    (f : ι → C(Sphere 3, X)) (a : ι → ℤ)
    (h : ∑ i, a i • singularHomologyMap (f i) 3 sphereThirdClass = 0) :
    ∑ i, a i • sphereThirdObstruction r (F.comp (f i)) = 0 := by
  simp_rw [sphereThirdObstruction_eq_homology, singularHomologyMap_comp, LinearMap.comp_apply]
  have he := congrArg (fun b ↦ stableThirdHomologyEquivZModTwo r (singularHomologyMap F 3 b)) h
  simpa only [map_sum, map_zsmul, map_zero] using he

end NoExoticSixSphere.Stiefel
