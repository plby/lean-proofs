import Wikipedia.NoExoticSixSphere.JamesSphereHopfHurewiczSix

/-!
# The original second James cell gives a primitive sixth-homology class

The actual bottom S6 of J(S3)/S3 and the actual quotient homology map
identify its integral top class with a primitive class in H6(J(S3)).
Its Hopf-compatible integer coordinate has absolute value one; no sign
is assigned to the constructed homeomorphisms. Consequently a geometric
calculation as k times this class would give absolute Hopf coordinate
abs(k). No such numerical calculation for the S4 attachment is assumed.
-/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris SphereHomology

namespace NoExoticSixSphere.SphereFourHopfHomology.SecondCell

open JamesSphere

def sphereToWords : SingularHomology (Sphere 6) 6 ≃ₗ[ℤ]
    SingularHomology (WordHomology.Words 3) 6 :=
  (LinearEquiv.ofBijective (singularHomologyMap (FirstStageQuotient.bottomSphere 3) 6)
    (FirstStageQuotient.bottomSphere_homology_bijective_range 3 (by decide) 6
      (by decide) (by decide))).trans
    (FirstStageQuotient.aboveHomologyEquiv 3 5 (by decide) (by decide)).symm

def generator : SingularHomology (WordHomology.Words 3) 6 :=
  sphereToWords (unitSphereTopClass 5)

theorem quotient_generator :
    singularHomologyMap (FirstStageQuotient.quotientMap 3) 6 generator =
      singularHomologyMap (FirstStageQuotient.bottomSphere 3) 6 (unitSphereTopClass 5) := by
  change FirstStageQuotient.aboveHomologyEquiv 3 5 (by decide) (by decide)
    ((FirstStageQuotient.aboveHomologyEquiv 3 5 (by decide) (by decide)).symm
      (singularHomologyMap (FirstStageQuotient.bottomSphere 3) 6 (unitSphereTopClass 5))) = _
  exact LinearEquiv.apply_symm_apply _ _

theorem generator_generates : Function.Surjective (fun k : ℤ ↦ k • generator) := by
  intro c
  obtain ⟨k, hk⟩ := unitSphereTopClass_generates 5 (sphereToWords.symm c)
  refine ⟨k, ?_⟩
  change k • sphereToWords (unitSphereTopClass 5) = c
  rw [← map_zsmul, hk, LinearEquiv.apply_symm_apply]

theorem integerLinearEquiv_natAbs_one (e : ℤ ≃ₗ[ℤ] ℤ) : Int.natAbs (e 1) = 1 := by
  have h : e 1 * e.symm 1 = 1 := by
    simpa only [smul_eq_mul, mul_one, one_mul, LinearEquiv.apply_symm_apply, mul_comm]
      using (e.map_smul (e.symm 1) (1 : ℤ)).symm
  have hn := congrArg Int.natAbs h
  rw [Int.natAbs_mul] at hn
  exact Nat.eq_one_of_mul_eq_one_right hn

theorem integer_coordinate_natAbs : Int.natAbs (wordIntegerEquiv generator) = 1 := by
  let e : ℤ ≃ₗ[ℤ] ℤ := (unitSphereHomologyTopEquiv 5).symm.trans
    (sphereToWords.trans wordIntegerEquiv)
  have hu := integerLinearEquiv_natAbs_one e
  have hg : (unitSphereHomologyTopEquiv 5).symm 1 = unitSphereTopClass 5 := by
    apply (unitSphereHomologyTopEquiv 5).injective
    rw [LinearEquiv.apply_symm_apply, unitSphereHomologyTopEquiv_topClass]
  change Int.natAbs
    (wordIntegerEquiv (sphereToWords ((unitSphereHomologyTopEquiv 5).symm 1))) = 1 at hu
  rw [hg] at hu
  exact hu

theorem multiple_coordinate_natAbs (k : ℤ) :
    Int.natAbs (wordIntegerEquiv (k • generator)) = Int.natAbs k := by
  rw [map_zsmul, Int.zsmul_eq_mul, Int.natAbs_mul, integer_coordinate_natAbs, mul_one]

theorem attaching_coordinate_natAbs_of_multiple (k : ℤ)
    (h : adjointClass SphereFourAttaching.attachingClass = k • generator) :
    Int.natAbs SphereFiveEighth.relation.1.toAdd = Int.natAbs k := by
  rw [attaching_coordinate, h, multiple_coordinate_natAbs]

end NoExoticSixSphere.SphereFourHopfHomology.SecondCell
