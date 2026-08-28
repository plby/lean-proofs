import Wikipedia.HomotopyGroupsOfSpheres.SphereSevenDegree

/-! # Absolute degree from a multiple of a top-homology automorphism -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres

open Wikipedia.HopfProblem.SphereHomology
open Wikipedia.HopfProblem.SingularMayerVietoris

attribute [local irreducible] unitSphereHomologyTopEquiv

private theorem integerLinearEquiv_natAbs_one (e : ℤ ≃ₗ[ℤ] ℤ) :
    Int.natAbs (e 1) = 1 := by
  have h : e 1 * e.symm 1 = 1 := by
    simpa only [smul_eq_mul, mul_one, one_mul, LinearEquiv.apply_symm_apply, mul_comm]
      using (e.map_smul (e.symm 1) (1 : ℤ)).symm
  have hn := congrArg Int.natAbs h
  rw [Int.natAbs_mul] at hn
  exact Nat.eq_one_of_mul_eq_one_right hn

/-- An actual homology map equal to `n` times an automorphism has absolute degree `n`. -/
theorem sphereSevenDegree_natAbs_of_homology_smul
    (f : C(Sphere 7, Sphere 7)) (n : ℕ)
    (e : SingularHomology (Sphere 7) 7 ≃ₗ[ℤ] SingularHomology (Sphere 7) 7)
    (h : ∀ a, singularHomologyMap f 7 a = n • e a) :
    Int.natAbs (sphereSevenDegree f) = n := by
  let m := unitSphereHomologyTopEquiv 6
  let ez : ℤ ≃ₗ[ℤ] ℤ := m.symm.trans (e.trans m)
  have ha : m.symm 1 = unitSphereTopClass 6 := by
    apply m.injective
    rw [LinearEquiv.apply_symm_apply]
    exact (unitSphereHomologyTopEquiv_topClass 6).symm
  have hu : Int.natAbs (m (e (unitSphereTopClass 6))) = 1 := by
    have hz := integerLinearEquiv_natAbs_one ez
    change Int.natAbs (m (e (m.symm 1))) = 1 at hz
    rwa [ha] at hz
  change Int.natAbs (m (singularHomologyMap f 7 (unitSphereTopClass 6))) = n
  rw [h, map_nsmul, nsmul_eq_mul, Int.natAbs_mul, Int.natAbs_natCast, hu, mul_one]

end Wikipedia.HomotopyGroupsOfSpheres
