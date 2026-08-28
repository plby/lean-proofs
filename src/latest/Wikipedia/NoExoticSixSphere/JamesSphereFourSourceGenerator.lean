import Wikipedia.NoExoticSixSphere.JamesSphereAttachingSourceSphere
import Wikipedia.NoExoticSixSphere.SphereFourAttachingClass

/-!
# The source comparison retains the actual seventh-sphere generator up to sign

Combine the original round-boundary coordinates, the actual face
collapse, and the constructed source-sphere homeomorphism. This gives
an automorphism of the native seventh sphere group. Its value on the
proved integral generator has coefficient of absolute value one.
The original attaching class is therefore the new source-sphere class
or its inverse. This does not yet identify that class with the chosen
Moore smash commutator: their prescribed boundary tracks still matter.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem.OrbitPair Wikipedia.HomotopyGroupsOfSpheres

namespace NoExoticSixSphere.JamesSphere.AttachingSquare

def fourBoundaryHomeomorph : Sphere 7 ≃ₜ fullBoundary 3 :=
  (RoundCell.boundaryHomeomorph 4 (by decide)).trans (fullBoundaryHomeomorph 3).symm

theorem fourBoundaryHomeomorph_pole : fourBoundaryHomeomorph (spherePole 7) = fullPoint 3 := by
  change (fullBoundaryHomeomorph 3).symm
    (RoundCell.boundaryHomeomorph 4 (by decide) (spherePole 7)) = _
  rw [RoundCell.boundaryHomeomorph_pole, ← fullBoundaryHomeomorph_point 3,
    Homeomorph.symm_apply_apply]

def fourBoundaryPiEquiv (d : ℕ) [NeZero d] :
    π_ d (Sphere 7) (spherePole 7) ≃* π_ d (fullBoundary 3) (fullPoint 3) :=
  (HigherHomotopyCoordinates.homeomorphMulEquiv (Fin d) fourBoundaryHomeomorph
    (spherePole 7)).trans (NativeHomotopyTargetEquality.equiv d fourBoundaryHomeomorph_pole)

theorem fourBoundaryPiEquiv_apply (d : ℕ) [NeZero d] (c : π_ d (Sphere 7) (spherePole 7)) :
    fourBoundaryPiEquiv d c = HigherHomotopy.map (N := Fin d)
      (fourBoundaryHomeomorph : C(_, _)) fourBoundaryHomeomorph_pole c :=
  NativeHomotopyTargetEquality.equiv_map d
    (fourBoundaryHomeomorph : C(Sphere 7, fullBoundary 3))
    fourBoundaryHomeomorph_pole c

def fourSourceComparison (d : ℕ) [NeZero d] :
    π_ d (Sphere 7) (spherePole 7) ≃* π_ d (Sphere 7) (spherePole 7) :=
  (fourBoundaryPiEquiv d).trans (sourceComparison 3 d)

theorem four_fullAttaching_comp :
    (fullAttaching 3).comp (fourBoundaryHomeomorph : C(_, _)) =
      EHPCell.attachingMap 4 (by decide) := by
  apply ContinuousMap.ext
  intro x
  change CellBoundary.attaching 4 (fullBoundaryHomeomorph 3
    ((fullBoundaryHomeomorph 3).symm (RoundCell.boundaryHomeomorph 4 (by decide) x))) = _
  rw [Homeomorph.apply_symm_apply]
  rfl

theorem fourAttaching_comparison (d : ℕ) [NeZero d] (c : π_ d (Sphere 7) (spherePole 7)) :
    EHPCell.attachingHom 4 (by decide) d c =
      sourceSphereAttachingHom 3 d (fourSourceComparison d c) := by
  have hmap : HigherHomotopy.map (N := Fin d) (fullAttaching 3) (fullAttaching_point 3)
      (fourBoundaryPiEquiv d c) = EHPCell.attachingHom 4 (by decide) d c := by
    rw [fourBoundaryPiEquiv_apply, HigherHomotopy.map_comp]
    simp only [four_fullAttaching_comp]
    rfl
  exact hmap.symm.trans (sourceAttaching_comparison 3 d (fourBoundaryPiEquiv d c))

theorem generating_integer_coordinate {G : Type*} [Group G] (e : G ≃* Multiplicative ℤ)
    (g : G) (hg : Function.Surjective (fun k : ℤ ↦ g ^ k)) : Int.natAbs (e g).toAdd = 1 := by
  obtain ⟨k, hk⟩ := hg (e.symm (Multiplicative.ofAdd 1))
  have he := congrArg (fun a ↦ (e a).toAdd) hk
  rw [map_zpow, MulEquiv.apply_symm_apply] at he
  change k • (e g).toAdd = 1 at he
  rw [Int.zsmul_eq_mul] at he
  have hn := congrArg Int.natAbs he
  rw [Int.natAbs_mul] at hn
  exact Nat.eq_one_of_mul_eq_one_left hn

def fourSourceSign : ℤ :=
  (pi7_sphere_seven_mulEquiv (spherePole 7)
    (fourSourceComparison 7 (sphereSevenGenerator (spherePole 7)))).toAdd

theorem fourSourceSign_natAbs : Int.natAbs fourSourceSign = 1 :=
  generating_integer_coordinate (pi7_sphere_seven_mulEquiv (spherePole 7)) _
    ((CyclicGenerators.equiv_generates_iff (fourSourceComparison 7) _).mpr
      (sphereSevenGenerator_generates (spherePole 7)))

theorem fourSourceSign_eq_one_or_neg_one : fourSourceSign = 1 ∨ fourSourceSign = -1 :=
  Int.isUnit_iff.mp (Int.isUnit_iff_natAbs_eq.mpr fourSourceSign_natAbs)

theorem fourSourceComparison_generator :
    fourSourceComparison 7 (sphereSevenGenerator (spherePole 7)) =
      sphereSevenGenerator (spherePole 7) ^ fourSourceSign := by
  apply (pi7_sphere_seven_mulEquiv (spherePole 7)).injective
  rw [map_zpow]
  change Multiplicative.ofAdd fourSourceSign =
    ((pi7_sphere_seven_mulEquiv (spherePole 7))
      ((pi7_sphere_seven_mulEquiv (spherePole 7)).symm (Multiplicative.ofAdd 1))) ^ fourSourceSign
  rw [MulEquiv.apply_symm_apply]
  change Multiplicative.ofAdd fourSourceSign = Multiplicative.ofAdd (fourSourceSign • (1 : ℤ))
  rw [Int.zsmul_eq_mul, mul_one]

def sourceFourAttachingClass : π_ 7 (Sphere 4) (spherePole 4) :=
  sourceSphereAttachingHom 3 7 (sphereSevenGenerator (spherePole 7))

theorem originalAttachingClass_eq_power :
    SphereFourAttaching.attachingClass = sourceFourAttachingClass ^ fourSourceSign := by
  change EHPCell.attachingHom 4 (by decide) 7 (sphereSevenGenerator (spherePole 7)) = _
  rw [fourAttaching_comparison, fourSourceComparison_generator, map_zpow]
  rfl

theorem originalAttachingClass_eq_or_inv :
    SphereFourAttaching.attachingClass = sourceFourAttachingClass ∨
      SphereFourAttaching.attachingClass = sourceFourAttachingClass⁻¹ := by
  rcases fourSourceSign_eq_one_or_neg_one with h | h
  · left
    simpa only [h, zpow_one] using originalAttachingClass_eq_power
  · right
    simpa only [h, zpow_neg, zpow_one] using originalAttachingClass_eq_power

end NoExoticSixSphere.JamesSphere.AttachingSquare
