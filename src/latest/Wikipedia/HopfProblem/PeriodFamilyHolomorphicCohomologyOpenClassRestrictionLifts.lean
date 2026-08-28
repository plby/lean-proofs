import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionBasic
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionSplittingLocal

/-!
# Original local extension lifts after genuine open restriction

Restrict the actual degree-one local sections of the original Čech
extension sheaf to the actual inverse-image cover. Their projections
are the same original constant integer sections, and their differences
are exactly the inclusion of the literal restricted cocycle values.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction

open HolomorphicFunctionSheaf.SphereH1
open HolomorphicSheafCohomology
open HolomorphicPicard.CechExtension

variable {X : TopCat.{0}} (A : Opens X)
  {F : TopCat.Sheaf AddCommGrpCat.{0} X} {ι : Type} {U : ι → Opens X}
  (c : CechOneCocycle F U)

/-- The literal restriction of the original local degree-one section,
as a section of the actual restricted extension sheaf. -/
def restrictedLocalSection (i : ι) :
    Section ((OpenRestriction.restriction A).obj (extensionSheaf c)) (restrictedCover A U i) :=
  res (extensionSheaf c) (imagePreimage_le A (U i)) (localDegreeOneSection c i)

/-- Its actual projected degree is the original constant integer one
on the literal ambient image open. -/
theorem restrictedLocalSection_projection (i : ι) :
    ((OpenRestriction.restriction A).map (projection c)).hom.app
        (op (restrictedCover A U i)) (restrictedLocalSection A c i) =
      (degreeUnit X).app (op ((OpenRestriction.openImage A).obj (restrictedCover A U i)))
        (ULift.up (1 : ℤ)) := by
  change (projection c).hom.app
      (op ((OpenRestriction.openImage A).obj (restrictedCover A U i)))
      (res (extensionSheaf c) (imagePreimage_le A (U i)) (localDegreeOneSection c i)) = _
  rw [← res_map, projection_localDegreeOneSection, res_degreeUnit]

/-- The actual restricted local sections have exactly the literal
restricted Čech difference, retaining the original second-minus-first sign. -/
theorem restrictedLocalSection_difference (i j : ι) :
    res ((OpenRestriction.restriction A).obj (extensionSheaf c)) inf_le_right
        (restrictedLocalSection A c j) -
      res ((OpenRestriction.restriction A).obj (extensionSheaf c)) inf_le_left
        (restrictedLocalSection A c i) =
      ((OpenRestriction.restriction A).map (inclusion c)).hom.app
        (op (restrictedCover A U i ⊓ restrictedCover A U j))
          ((restrictedCocycle A c).value i j) := by
  have h := congrArg (res (extensionSheaf c) (imagePreimage_le A (U i ⊓ U j)))
    (localDegreeOneSection_difference c i j)
  let ri : restrictedCover A U i ⊓ restrictedCover A U j ⟶ restrictedCover A U i :=
    homOfLE inf_le_left
  let rj : restrictedCover A U i ⊓ restrictedCover A U j ⟶ restrictedCover A U j :=
    homOfLE inf_le_right
  change res (extensionSheaf c) ((OpenRestriction.openImage A).map rj).le
      (res (extensionSheaf c) (imagePreimage_le A (U j)) (localDegreeOneSection c j)) -
    res (extensionSheaf c) ((OpenRestriction.openImage A).map ri).le
      (res (extensionSheaf c) (imagePreimage_le A (U i)) (localDegreeOneSection c i)) =
    (inclusion c).hom.app
      (op ((OpenRestriction.openImage A).obj (OpenRestriction.preimageOpen A (U i ⊓ U j))))
        (res F (imagePreimage_le A (U i ⊓ U j)) (c.value i j))
  simp only [map_sub, res_trans, res_map] at h
  simp only [res_trans]
  exact h

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction
