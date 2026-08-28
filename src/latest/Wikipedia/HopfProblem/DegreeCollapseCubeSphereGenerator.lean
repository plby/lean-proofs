import Wikipedia.NoExoticSixSphere.IntegralSphereHomotopyClass
import Wikipedia.NoExoticSixSphere.SphereHomotopyGroups
import Wikipedia.NoExoticSixSphere.Topology.SimplyConnectedSphere
import Wikipedia.HopfProblem.SphereHomologyTop
import Wikipedia.HopfProblem.DegreeCollapseSurgeryOriginalEndHomology
import Mathlib.Algebra.Group.Int.Units

/-!
# The genuine cubical S3 class is an integral generator

Third Hurewicz realizes every actual H3(S3) class by a self-map evaluated
on the cubical class. The independently marked H3(S3) is cyclic. Combining
these two facts proves that the cubical class itself generates; it is
the standard marked class up to sign. The spans of their images under
every actual sphere map are therefore equal. No orientation sign is fixed.
-/

noncomputable section

open Function Set Topology ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.CubeSphereGenerator

open NoExoticSixSphere NoExoticSixSphere.SmoothCube
open SingularMayerVietoris SphereHomology

theorem generates (c : SingularHomology (Sphere 3) 3) :
    ∃ k : ℤ, k • integralCubeSphereClass = c := by
  let : SimplyConnectedSpace (Sphere 3) := EuclideanSphere.simplyConnectedSpace 1
  let : Subsingleton (π_ 2 (Sphere 3) (spherePole 3)) :=
    subsingleton_sphereHomotopyGroup (by decide) (spherePole 3)
  let g := (integralClassRepresentative (spherePole 3) c).val
  have hc : singularHomologyMap g 3 integralCubeSphereClass = c :=
    integralSphereClass_representative (spherePole 3) c
  obtain ⟨k, hk⟩ := unitSphereTopClass_generates 2 integralCubeSphereClass
  obtain ⟨j, hj⟩ := unitSphereTopClass_generates 2 (singularHomologyMap g 3 (unitSphereTopClass 2))
  refine ⟨j, ?_⟩
  calc
    j • integralCubeSphereClass = j • (k • unitSphereTopClass 2) := by rw [hk]
    _ = k • (j • unitSphereTopClass 2) := smul_comm j k _
    _ = k • singularHomologyMap g 3 (unitSphereTopClass 2) := by rw [hj]
    _ = singularHomologyMap g 3 (k • unitSphereTopClass 2) := (map_zsmul _ k _).symm
    _ = c := by rw [hk, hc]

theorem marking_unit (L : SingularHomology (Sphere 3) 3 ≃ₗ[ℤ] ℤ) :
    IsUnit (L integralCubeSphereClass) := by
  obtain ⟨k, hk⟩ := generates (L.symm 1)
  have h := congrArg L hk
  rw [map_zsmul, LinearEquiv.apply_symm_apply] at h
  exact IsUnit.of_mul_eq_one k (by simpa only [smul_eq_mul, mul_comm] using h)

theorem standard_or_negative : integralCubeSphereClass = unitSphereTopClass 2 ∨
    integralCubeSphereClass = -unitSphereTopClass 2 := by
  rcases Int.isUnit_iff.mp (marking_unit (unitSphereHomologyTopEquiv 2)) with hp | hn
  · left
    apply (unitSphereHomologyTopEquiv 2).injective
    exact hp.trans (unitSphereHomologyTopEquiv_topClass 2).symm
  · right
    apply (unitSphereHomologyTopEquiv 2).injective
    rw [map_neg, unitSphereHomologyTopEquiv_topClass]
    exact hn

theorem image_span {X : Type} [TopologicalSpace X] (f : C(Sphere 3, X)) :
    Submodule.span ℤ {integralSphereClass f} =
      Submodule.span ℤ {TraceCoreAttachment.originalSphereClass f} := by
  rcases standard_or_negative with hp | hn
  · unfold integralSphereClass TraceCoreAttachment.originalSphereClass
    rw [hp]
  · unfold integralSphereClass TraceCoreAttachment.originalSphereClass
    rw [hn, map_neg]
    simpa only [Set.neg_singleton] using
      (Submodule.span_neg (R := ℤ) {singularHomologyMap f 3 (unitSphereTopClass 2)})

end Wikipedia.HopfProblem.DegreeCollapse.CubeSphereGenerator
