import Wikipedia.HopfProblem.SpecialPeriodsTriangleTilingFirstSector
import Wikipedia.HopfProblem.SpecialPeriodsTriangleTilingSecondSector
import Wikipedia.HopfProblem.SpecialPeriodsTriangleTilingWords

/-!
# Disjoint translates of the circularly doubled triangle

The explicit cyclic-sector inequalities feed the actual reduced-word
normal form.  No freeness or fundamental-domain hypothesis is assumed:
returning an interior point to this polygon forces the abstract triangle
word itself to be the identity.
-/

noncomputable section

open Set UpperHalfPlane
open scoped MatrixGroups Pointwise

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

theorem generatorOnePerm_firstSector :
    MapsTo (fun z : ℍ => generatorOnePerm z) firstSector firstExcluded :=
  generatorOne_firstSector

theorem generatorOnePerm_sq_firstSector :
    MapsTo (fun z : ℍ => (generatorOnePerm ^ 2) z) firstSector firstExcluded := by
  intro z hz
  change (generatorOnePerm ^ 2) z ∈ firstExcluded
  rw [generatorOnePerm_pow_apply]
  exact generatorOne_sq_firstSector hz

theorem generatorTwoPerm_secondSector :
    MapsTo (fun z : ℍ => generatorTwoPerm z) secondSector secondExcluded :=
  generatorTwo_secondSector

theorem generatorTwoPerm_sq_secondSector :
    MapsTo (fun z : ℍ => (generatorTwoPerm ^ 2) z) secondSector secondExcluded := by
  intro z hz
  change (generatorTwoPerm ^ 2) z ∈ secondExcluded
  rw [generatorTwoPerm_pow_apply]
  exact generatorTwo_sq_secondSector hz

theorem generatorTwoPerm_cube_secondSector :
    MapsTo (fun z : ℍ => (generatorTwoPerm ^ 3) z) secondSector secondExcluded := by
  intro z hz
  change (generatorTwoPerm ^ 3) z ∈ secondExcluded
  rw [generatorTwoPerm_pow_apply]
  exact generatorTwo_cube_secondSector hz

/-- Identity detection for the actual geometric representation on the
open polygon cut along the circular side. -/
theorem eq_one_of_circularDoubleInterior_mem (g : TriangleGroup) {z : ℍ}
    (hz : z ∈ circularDoubleInterior)
    (hgz : triangleGeometricRepresentation g z ∈ circularDoubleInterior) : g = 1 := by
  exact triangleLift_eq_one_of_domain_mem
    generatorOnePerm generatorTwoPerm generatorOnePerm_cube generatorTwoPerm_fourth
    firstExcluded secondExcluded circularDoubleInterior
    (fun _ hw => generatorOnePerm_firstSector (secondExcluded_subset_firstSector hw))
    (fun _ hw => generatorOnePerm_sq_firstSector (secondExcluded_subset_firstSector hw))
    (fun _ hw => generatorTwoPerm_secondSector (firstExcluded_subset_secondSector hw))
    (fun _ hw => generatorTwoPerm_sq_secondSector (firstExcluded_subset_secondSector hw))
    (fun _ hw => generatorTwoPerm_cube_secondSector (firstExcluded_subset_secondSector hw))
    (fun _ hw => generatorOnePerm_firstSector hw.1)
    (fun _ hw => generatorOnePerm_sq_firstSector hw.1)
    (fun _ hw => generatorTwoPerm_secondSector hw.2)
    (fun _ hw => generatorTwoPerm_sq_secondSector hw.2)
    (fun _ hw => generatorTwoPerm_cube_secondSector hw.2)
    circularDoubleInterior_disjoint_firstExcluded circularDoubleInterior_disjoint_secondExcluded
    g hz hgz

theorem eq_one_of_circularDoubleInterior_eq (g : TriangleGroup) {z w : ℍ}
    (hz : z ∈ circularDoubleInterior) (hw : w ∈ circularDoubleInterior)
    (hzw : triangleGeometricRepresentation g z = w) : g = 1 :=
  eq_one_of_circularDoubleInterior_mem g hz (hzw ▸ hw)

/-- Distinct actual triangle translates of the circularly doubled open
triangle are disjoint. -/
theorem circularDoubleInterior_translates_pairwiseDisjoint :
    Pairwise fun g h : TriangleGroup =>
      Disjoint (triangleGeometricRepresentation g '' circularDoubleInterior)
        (triangleGeometricRepresentation h '' circularDoubleInterior) := by
  intro g h hgh
  apply Set.disjoint_left.mpr
  rintro w ⟨z, hz, rfl⟩ ⟨u, hu, he⟩
  have hreturn : triangleGeometricRepresentation (h⁻¹ * g) z = u := by
    rw [map_mul, map_inv]
    change (triangleGeometricRepresentation h).symm (triangleGeometricRepresentation g z) = u
    rw [← he]
    exact (triangleGeometricRepresentation h).symm_apply_apply u
  have hid := eq_one_of_circularDoubleInterior_eq (h⁻¹ * g) hz hu hreturn
  exact hgh ((inv_mul_eq_one.mp hid).symm)

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
