import Wikipedia.NoExoticSixSphere.ThirdStemSmashParity

/-!
# The sixth-stem square of maps with original Hopf coordinate of absolute value one

The coordinate is the ORIGINAL native James--Hopf homomorphism on
pi7(S4), measured through the checked pi7(S7) marking. Either sign gives
an odd suspended third-stem class. Its literal product suspension and
actual smash square therefore represent the already constructed class
in pi16(S10). No particular geometric map is assigned Hopf coordinate
one here, and no nontriviality or Arf detection is inferred.
-/

noncomputable section

open scoped Topology

namespace NoExoticSixSphere.OriginalHopfSixthSquare

open SmoothCube SphereComposition

def hopfCoordinate (c : π_ 7 (Sphere 4) (spherePole 4)) : ℤ :=
  (Wikipedia.HomotopyGroupsOfSpheres.pi7_sphere_seven_mulEquiv (spherePole 7)
    (SphereFourSeventh.hopf c)).toAdd

theorem hopfCoordinate_eq (c : π_ 7 (Sphere 4) (spherePole 4)) :
    hopfCoordinate c = (SphereFourSeventh.groupEquiv c).1.toAdd :=
  (congrArg Multiplicative.toAdd (SphereFourSeventh.groupEquiv_hopf c)).symm

theorem suspended_twelfth_power_ne_one_of_positive
    (c : π_ 7 (Sphere 4) (spherePole 4))
    (hc : (SphereFourSeventh.groupEquiv c).1.toAdd = 1) :
    SphereFourAttaching.suspension c ^ 12 ≠ 1 := by
  let b : ZMod 12 := (SphereFourSeventh.groupEquiv c).2.toAdd
  have he : SphereFourSeventh.groupEquiv c =
      (Multiplicative.ofAdd 1, Multiplicative.ofAdd b) := by
    apply Prod.ext
    · exact congrArg Multiplicative.ofAdd hc
    · rfl
  rw [← SphereFiveEighth.projection_coordinates, he,
    SphereFiveEighth.projection_twelfth_power]
  exact SphereFiveEighth.integerLift_twelfth_power_ne_one

theorem suspended_twelfth_power_ne_one (c : π_ 7 (Sphere 4) (spherePole 4))
    (hc : (hopfCoordinate c).natAbs = 1) : SphereFourAttaching.suspension c ^ 12 ≠ 1 := by
  rw [hopfCoordinate_eq] at hc
  rcases Int.natAbs_eq_iff.mp hc with h | h
  · exact suspended_twelfth_power_ne_one_of_positive c h
  · have hi : (SphereFourSeventh.groupEquiv c⁻¹).1.toAdd = 1 := by
      rw [map_inv]
      change -(SphereFourSeventh.groupEquiv c).1.toAdd = 1
      rw [h]
      rfl
    have hn := suspended_twelfth_power_ne_one_of_positive c⁻¹ hi
    rw [map_inv, inv_pow] at hn
    exact fun he ↦ hn (by rw [he, inv_one])

theorem sphereClass_square (f : Based 7 4)
    (hf : (hopfCoordinate (sphereClass f)).natAbs = 1) :
    sphereClass (SphereSmash.basedSquare (CubicalSphereSuspension.productBasedMap f)) =
      SixthStemSmashSquare.nativeClass := by
  apply SphereSmashNative.sphereClass_square_eq_of_twelfth_power_ne_one
  rw [← CubicalSphereSuspension.hom_sphereClass]
  exact suspended_twelfth_power_ne_one (sphereClass f) hf

theorem stableClass_square (f : Based 7 4)
    (hf : (hopfCoordinate (sphereClass f)).natAbs = 1) :
    CubicalStableSix.ofNative (sphereClass
      (SphereSmash.basedSquare (CubicalSphereSuspension.productBasedMap f))) =
        SixthStemSmashSquare.stableClass := by
  rw [sphereClass_square f hf]
  rfl

end NoExoticSixSphere.OriginalHopfSixthSquare
