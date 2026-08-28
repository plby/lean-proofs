import Wikipedia.NoExoticSixSphere.MayerVietorisInclusionRange
import Wikipedia.NoExoticSixSphere.DoubleMappingCylinderOverlapEquivalence
import Wikipedia.NoExoticSixSphere.DoubleMappingCylinderEquivalence
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# Homology preservation by the original pushout inclusion

The actual open-piece and overlap equivalences transfer Mayer--Vietoris
to the two original end maps. When the left attaching map has homotopy
extension, the genuine cylinder collapse transfers the conclusions to
the ordinary pushout, with the original right inclusion retained.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Set
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology OrbitPair

namespace NoExoticSixSphere.DoubleMappingCylinder

variable {A X Y : TopCat.{0}} (e : A ⟶ X) (f : A ⟶ Y)

theorem right_homology_injective (d : ℕ) [Subsingleton (SingularHomology A d)] :
    Function.Injective (singularHomologyMap (right e f).hom d) := by
  let : Subsingleton (SingularHomology (lower e f ∩ upper e f : Set (space e f)) d) :=
    (homotopyEquivHomologyEquiv (overlapEquiv e f) d).symm.injective.subsingleton
  have hcomp : (subtypeInclusion (lower e f)).comp (lowerEquiv e f).toFun =
      (right e f).hom := rfl
  rw [← hcomp, singularHomologyMap_comp]
  exact (MayerVietorisInclusionRange.injective (lower e f) (upper e f)
    (lower_isOpen e f) (upper_isOpen e f) (cover e f) d).comp
    (homotopyEquivHomologyEquiv (lowerEquiv e f) d).injective

theorem right_homology_surjective (d : ℕ) [Subsingleton (SingularHomology X (d + 1))]
    [Subsingleton (SingularHomology A d)] :
    Function.Surjective (singularHomologyMap (right e f).hom (d + 1)) := by
  let : Subsingleton (SingularHomology (upper e f) (d + 1)) :=
    (homotopyEquivHomologyEquiv (upperEquiv e f) (d + 1)).symm.injective.subsingleton
  let : Subsingleton (SingularHomology (lower e f ∩ upper e f : Set (space e f)) d) :=
    (homotopyEquivHomologyEquiv (overlapEquiv e f) d).symm.injective.subsingleton
  have hcomp : (subtypeInclusion (lower e f)).comp (lowerEquiv e f).toFun =
      (right e f).hom := rfl
  rw [← hcomp, singularHomologyMap_comp]
  exact (MayerVietorisInclusionRange.surjective (lower e f) (upper e f)
    (lower_isOpen e f) (upper_isOpen e f) (cover e f) d).comp
    (homotopyEquivHomologyEquiv (lowerEquiv e f) (d + 1)).surjective

variable {P : TopCat.{0}} {i : X ⟶ P} {j : Y ⟶ P} (hP : IsPushout e f i j)
    (he : HomotopyExtension.HasHomotopyExtension e)

include he in
theorem collapse_homology_bijective (d : ℕ) :
    Function.Bijective (singularHomologyMap (collapse e f hP).hom d) := by
  obtain ⟨E, hE⟩ := exists_collapse_equiv e f hP he
  rw [← hE]
  exact (homotopyEquivHomologyEquiv E d).bijective

include hP he in
theorem pushout_right_homology_injective (d : ℕ) [Subsingleton (SingularHomology A d)] :
    Function.Injective (singularHomologyMap j.hom d) := by
  have hc : (collapse e f hP).hom.comp (right e f).hom = j.hom :=
    congrArg TopCat.Hom.hom (right_collapse e f hP)
  rw [← hc, singularHomologyMap_comp]
  exact (collapse_homology_bijective e f hP he d).injective.comp
    (right_homology_injective e f d)

include hP he in
theorem pushout_right_homology_surjective (d : ℕ)
    [Subsingleton (SingularHomology X (d + 1))] [Subsingleton (SingularHomology A d)] :
    Function.Surjective (singularHomologyMap j.hom (d + 1)) := by
  have hc : (collapse e f hP).hom.comp (right e f).hom = j.hom :=
    congrArg TopCat.Hom.hom (right_collapse e f hP)
  rw [← hc, singularHomologyMap_comp]
  exact (collapse_homology_bijective e f hP he (d + 1)).surjective.comp
    (right_homology_surjective e f d)

end NoExoticSixSphere.DoubleMappingCylinder
