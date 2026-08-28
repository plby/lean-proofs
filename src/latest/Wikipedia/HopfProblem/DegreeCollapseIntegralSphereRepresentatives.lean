import Wikipedia.NoExoticSixSphere.IntegralSphereHomotopyClass
import Wikipedia.HopfProblem.SphereHomologySimplyConnectedPiTwo

/-!
# Every original third-homology class has a sphere representative with the original marking

Surjectivity of the original third Hurewicz map on the actual three-sphere
proves that its cubical sphere class is an integer unit times the original
suspension-marked top class. This is proved integrally, not inferred from
nonzero mod-two reduction. Applying Hurewicz to the corresponding unit
multiple of any target class gives an actual continuous sphere map whose
image of the original surgery top class is exactly that target class.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralSphereRepresentatives

open NoExoticSixSphere NoExoticSixSphere.SmoothCube
open SingularMayerVietoris SphereHomology

theorem cubeClass_unit_multiple :
    ∃ k : ℤ, IsUnit k ∧ k • unitSphereTopClass 2 = integralCubeSphereClass := by
  obtain ⟨k, hk⟩ := unitSphereTopClass_generates 2 integralCubeSphereClass
  let x : Sphere 3 := spherePole 3
  let : Subsingleton (π_ 2 (Sphere 3) x) := unitSphere_piTwo_subsingleton 0 x
  let f := (integralClassRepresentative x (unitSphereTopClass 2)).val
  have hf := integralSphereClass_representative x (unitSphereTopClass 2)
  change singularHomologyMap f 3 integralCubeSphereClass = unitSphereTopClass 2 at hf
  rw [← hk, map_zsmul] at hf
  have hm := congrArg (unitSphereHomologyTopEquiv 2) hf
  rw [map_zsmul, unitSphereHomologyTopEquiv_topClass, zsmul_eq_mul, Int.cast_id] at hm
  exact ⟨k, isUnit_iff_dvd_one.mpr
    ⟨unitSphereHomologyTopEquiv 2 (singularHomologyMap f 3 (unitSphereTopClass 2)), hm.symm⟩, hk⟩

theorem exists_sphereMap_of_piTwo {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] (c : SingularHomology X 3) :
    ∃ f : C(Sphere 3, X), singularHomologyMap f 3 (unitSphereTopClass 2) = c := by
  obtain ⟨k, hunit, hk⟩ := cubeClass_unit_multiple
  let f := (integralClassRepresentative x (k • c)).val
  have hf := integralSphereClass_representative x (k • c)
  change singularHomologyMap f 3 integralCubeSphereClass = k • c at hf
  rw [← hk, map_zsmul] at hf
  refine ⟨f, ?_⟩
  rcases Int.isUnit_iff.mp hunit with hk | hk
  · simpa only [hk, one_smul] using hf
  · simpa only [hk, neg_one_zsmul, neg_inj] using hf

theorem exists_sphereMap {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    [Subsingleton (SingularHomology X 2)] (x : X) (c : SingularHomology X 3) :
    ∃ f : C(Sphere 3, X), singularHomologyMap f 3 (unitSphereTopClass 2) = c := by
  let : Subsingleton (π_ 2 X x) :=
    (SecondHurewicz.SimplyConnected.hurewiczPi2Equiv x).injective.subsingleton
  exact exists_sphereMap_of_piTwo x c

end Wikipedia.HopfProblem.DegreeCollapse.IntegralSphereRepresentatives
