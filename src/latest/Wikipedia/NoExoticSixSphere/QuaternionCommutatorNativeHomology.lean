import Wikipedia.NoExoticSixSphere.QuaternionCommutatorNativeLocalHomeomorph
import Wikipedia.NoExoticSixSphere.LocalHomeomorphMapHomology
import Wikipedia.SmoothSixDPoincare.SpherePointConnecting
import Wikipedia.HomotopyGroupsOfSpheres.SphereSevenDegreeMagnitude

/-!
# The explicit quaternionic seven-sphere map has absolute degree one

Its proved singleton fiber and local homeomorphism give an isomorphism
on actual local homology. The complements of the two points are genuinely
contractible by stereographic projection, so the original global map
induces a top-homology isomorphism. The literal quaternion-coordinate
change then gives degree of absolute value one on the standard sphere.
-/

noncomputable section

namespace NoExoticSixSphere.QuaternionCommutatorNativeSphere

open Wikipedia.HomotopyGroupsOfSpheres QuaternionicFibration
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology
open Wikipedia.SmoothSixDPoincare
open QuaternionCommutatorNativeCharts QuaternionCommutatorNativeLocalHomeomorph

theorem sphereMap_mapsTo_puncture :
    Set.MapsTo sphereMap ({sourcePoint}ᶜ : Set (Sphere 7))
      ({localModel sourcePoint}ᶜ : Set BaseSphere) := by
  intro x hx
  change sphereMap x ≠ localModel sourcePoint
  rw [localModel_sourcePoint]
  exact fun h ↦ hx ((sphereMap_fiber_iff x).mp h)

theorem sphereMap_homology_bijective (n : ℕ) :
    Function.Bijective (singularHomologyMap sphereMap (n + 2)) := by
  let : Fact (Module.finrank ℝ QuaternionPlane = 7 + 1) :=
    ⟨by simpa using planeCoordinates.toLinearEquiv.finrank_eq⟩
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 8)) = 7 + 1) := ⟨by simp⟩
  let : ContractibleSpace ({sourcePoint}ᶜ : Set (Sphere 7)) :=
    SpherePoint.puncture_contractible (n := 7) sourcePoint
  let : ContractibleSpace ({localModel sourcePoint}ᶜ : Set BaseSphere) :=
    SpherePoint.puncture_contractible (n := 7) (localModel sourcePoint)
  exact RelativeSingularHomology.localModel_singularHomologyMap_bijective sphereMap
    localModel sourcePoint sourcePoint_mem_localModel localModel_eq_sphereMap
    sphereMap_mapsTo_puncture n

def degreeMap : C(Sphere 7, Sphere 7) :=
  (baseSphereHomeomorph : C(BaseSphere, Sphere 7)).comp sphereMap

theorem degreeMap_homology_bijective :
    Function.Bijective (singularHomologyMap degreeMap 7) := by
  change Function.Bijective (singularHomologyMap
    ((baseSphereHomeomorph : C(BaseSphere, Sphere 7)).comp sphereMap) 7)
  rw [singularHomologyMap_comp]
  exact (homotopyEquivHomologyEquiv baseSphereHomeomorph.toHomotopyEquiv 7).bijective.comp
    (sphereMap_homology_bijective 5)

def degreeHomologyEquiv :
    SingularHomology (Sphere 7) 7 ≃ₗ[ℤ] SingularHomology (Sphere 7) 7 :=
  LinearEquiv.ofBijective (singularHomologyMap degreeMap 7) degreeMap_homology_bijective

theorem degreeHomologyEquiv_apply (a : SingularHomology (Sphere 7) 7) :
    degreeHomologyEquiv a = singularHomologyMap degreeMap 7 a := rfl

theorem degreeMap_degree_natAbs : Int.natAbs (sphereSevenDegree degreeMap) = 1 :=
  sphereSevenDegree_natAbs_of_homology_smul degreeMap 1 degreeHomologyEquiv
    (fun a ↦ by rw [one_smul, degreeHomologyEquiv_apply])

end NoExoticSixSphere.QuaternionCommutatorNativeSphere
