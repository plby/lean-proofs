import Wikipedia.NoExoticSixSphere.SmoothSphereCubeHomotopy
import Wikipedia.HopfProblem.SphereHomologySimplyConnectedPiTwo
import Wikipedia.HopfProblem.SecondHurewiczNaturality

/-!

# Exact integral two-sphere representatives in a simply connected space

The actual native square class descends through the original cube-boundary
quotient. Naturality identifies it with the image of one class of the
literal two-sphere. Hurewicz surjectivity on that sphere proves that this
class is an integer unit times the original suspension-marked top class.
Thus every original H2 class has a sphere representative with that exact
integral marking, without any H2-vanishing assumption.
-/

noncomputable section

open Function
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralTwoSphereRepresentatives

open NoExoticSixSphere NoExoticSixSphere.SmoothCube
open SingularMayerVietoris SphereHomology SecondHurewicz

def squareSphereClass : SingularHomology (Sphere 2) 2 :=
  squareHomologyClass (toGenLoop
    (⟨ContinuousMap.id (Sphere 2), rfl⟩ : BasedMap 2 (Sphere 2) (spherePole 2)))

theorem squareHomologyClass_toGenLoop {X : Type} [TopologicalSpace X] {x : X}
    (f : BasedMap 2 X x) :
    squareHomologyClass (toGenLoop f) = singularHomologyMap f.val 2 squareSphereClass := by
  rcases f with ⟨f, hf⟩
  subst x
  let i : BasedMap 2 (Sphere 2) (spherePole 2) := ⟨ContinuousMap.id _, rfl⟩
  have he : mapGenLoop f (spherePole 2) (toGenLoop i) =
      toGenLoop (⟨f, rfl⟩ : BasedMap 2 X (f (spherePole 2))) := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro u
    rfl
  have h := squareHomologyClass_natural f (spherePole 2) (toGenLoop i)
  rw [he] at h
  exact h.symm

theorem exists_basedMap_squareClass {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) (c : SingularHomology X 2) :
    ∃ f : BasedMap 2 X x, singularHomologyMap f.val 2 squareSphereClass = c := by
  obtain ⟨u, hu⟩ := (SecondHurewicz.SimplyConnected.hurewiczLinearEquiv x).surjective c
  obtain ⟨f, hf⟩ := sphereClass_surjective (by decide : 0 < 2) u.toMul
  refine ⟨f, ?_⟩
  rw [← squareHomologyClass_toGenLoop]
  change hurewiczMap x (Additive.ofMul (sphereClass f)) = c
  rw [hf]
  exact hu

theorem squareClass_unit_multiple :
    ∃ k : ℤ, IsUnit k ∧ k • unitSphereTopClass 1 = squareSphereClass := by
  obtain ⟨k, hk⟩ := unitSphereTopClass_generates 1 squareSphereClass
  obtain ⟨f, hf⟩ := exists_basedMap_squareClass (spherePole 2) (unitSphereTopClass 1)
  rw [← hk, map_zsmul] at hf
  have hm := congrArg (unitSphereHomologyTopEquiv 1) hf
  rw [map_zsmul, unitSphereHomologyTopEquiv_topClass, zsmul_eq_mul, Int.cast_id] at hm
  exact ⟨k, isUnit_iff_dvd_one.mpr
    ⟨unitSphereHomologyTopEquiv 1 (singularHomologyMap f.val 2 (unitSphereTopClass 1)),
      hm.symm⟩, hk⟩

theorem exists_basedMap {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) (c : SingularHomology X 2) :
    ∃ f : BasedMap 2 X x, singularHomologyMap f.val 2 (unitSphereTopClass 1) = c := by
  obtain ⟨k, hunit, hk⟩ := squareClass_unit_multiple
  obtain ⟨f, hf⟩ := exists_basedMap_squareClass x (k • c)
  rw [← hk, map_zsmul] at hf
  refine ⟨f, ?_⟩
  rcases Int.isUnit_iff.mp hunit with hk | hk
  · simpa only [hk, one_smul] using hf
  · simpa only [hk, neg_one_zsmul, neg_inj] using hf

theorem exists_sphereMap {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) (c : SingularHomology X 2) :
    ∃ f : C(Sphere 2, X), singularHomologyMap f 2 (unitSphereTopClass 1) = c := by
  obtain ⟨f, hf⟩ := exists_basedMap x c
  exact ⟨f.val, hf⟩

end Wikipedia.HopfProblem.DegreeCollapse.IntegralTwoSphereRepresentatives
