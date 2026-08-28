import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionUnitExt

/-!
# Literal integer sections under the original open-restriction endpoint

The actual integer endpoint preserves the original constant-presheaf
degree sections on every open of the original subspace. The proof
first identifies its genuine global representing section and then
uses the original degree-unit and sheaf-map naturality. No endpoint
isomorphism, section-identification hypothesis, or separation assumption
is supplied.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction

open HolomorphicSheafCohomology
open CuspNormalization.SheafCohomologyFinitePushforward
open HolomorphicPicard.CechExtension
open PeriodFamilyHigherDirectImage

variable {X : TopCat.{0}} (U : Opens X)

/-- The literal equality of the image of the top subspace open with
the original open preserves every original integer degree section. -/
theorem restrictionGlobalEquiv_degreeUnit (n : ULift.{0} ℤ) :
    OpenRestriction.restrictionGlobalEquiv U (integerSheaf X)
        ((degreeUnit X).app (op ((OpenRestriction.openImage U).obj ⊤)) n) =
      (degreeUnit X).app (op U) n := by
  change (integerSheaf X).obj.map
      (eqToHom (congrArg op (OpenRestriction.openImage_top U)))
      ((degreeUnit X).app (op ((OpenRestriction.openImage U).obj ⊤)) n) = _
  exact (ConcreteCategory.congr_hom
    ((degreeUnit X).naturality
      (eqToHom (congrArg op (OpenRestriction.openImage_top U)))) n).symm

/-- The actual endpoint has the original constant-one representing
section under the genuine global-section comparison. -/
theorem integerRestrictionUnit_globalSection :
    OpenRestriction.restrictionGlobalEquiv U (integerSheaf X)
      (homGlobalEquiv (TopCat.of U)
        ((OpenRestriction.restriction U).obj (integerSheaf X)) (integerRestrictionUnit U)) =
      (degreeUnit X).app (op U) (ULift.up (1 : ℤ)) := by
  rw [integerRestrictionUnit_eq_homRestrictionEquiv,
    OpenRestriction.homRestrictionEquiv_sections, GlobalRestriction.globalUnit_section]

/-- At the top subspace open, the endpoint preserves the actual
constant degree-one section, with its original ambient image open. -/
theorem integerRestrictionUnit_degreeUnit_top_one :
    (integerRestrictionUnit U).hom.app (op (⊤ : Opens U))
        ((degreeUnit (TopCat.of U)).app (op (⊤ : Opens U)) (ULift.up (1 : ℤ))) =
      (degreeUnit X).app (op ((OpenRestriction.openImage U).obj ⊤)) (ULift.up (1 : ℤ)) := by
  apply (OpenRestriction.restrictionGlobalEquiv U (integerSheaf X)).injective
  have h := (CechFibre.homGlobalEquiv_degreeUnit (TopCat.of U)
    ((OpenRestriction.restriction U).obj (integerSheaf X)) (integerRestrictionUnit U)).symm
  exact (congrArg (OpenRestriction.restrictionGlobalEquiv U (integerSheaf X)) h).trans
    ((integerRestrictionUnit_globalSection U).trans
      (restrictionGlobalEquiv_degreeUnit U (ULift.up (1 : ℤ))).symm)

/-- The same actual global formula holds for every lifted integer. -/
theorem integerRestrictionUnit_degreeUnit_top (n : ULift.{0} ℤ) :
    (integerRestrictionUnit U).hom.app (op (⊤ : Opens U))
        ((degreeUnit (TopCat.of U)).app (op (⊤ : Opens U)) n) =
      (degreeUnit X).app (op ((OpenRestriction.openImage U).obj ⊤)) n := by
  have h : (degreeUnit (TopCat.of U)).app (op (⊤ : Opens U)) ≫
        (integerRestrictionUnit U).hom.app (op (⊤ : Opens U)) =
      (degreeUnit X).app (op ((OpenRestriction.openImage U).obj ⊤)) := by
    apply (AddCommGrpCat.uliftZMultiplesAddEquiv _).injective
    exact integerRestrictionUnit_degreeUnit_top_one U
  exact ConcreteCategory.congr_hom h n

/-- On every original open of the subspace, the actual endpoint sends
each native constant integer section to the same original integer
section on its literal ambient image open. -/
theorem integerRestrictionUnit_degreeUnit_app (W : Opens U) (n : ULift.{0} ℤ) :
    (integerRestrictionUnit U).hom.app (op W)
        ((degreeUnit (TopCat.of U)).app (op W) n) =
      (degreeUnit X).app (op ((OpenRestriction.openImage U).obj W)) n := by
  let r : W ⟶ (⊤ : Opens U) := homOfLE le_top
  have hU := ConcreteCategory.congr_hom
    ((degreeUnit (TopCat.of U)).naturality r.op) n
  have hX := ConcreteCategory.congr_hom
    ((degreeUnit X).naturality ((OpenRestriction.openImage U).map r).op) n
  have hη := ConcreteCategory.congr_hom ((integerRestrictionUnit U).hom.naturality r.op)
    ((degreeUnit (TopCat.of U)).app (op (⊤ : Opens U)) n)
  change (degreeUnit (TopCat.of U)).app (op W) n =
    (integerSheaf (TopCat.of U)).obj.map r.op
      ((degreeUnit (TopCat.of U)).app (op (⊤ : Opens U)) n) at hU
  rw [hU]
  exact hη.trans ((congrArg
    (((OpenRestriction.restriction U).obj (integerSheaf X)).obj.map r.op)
    (integerRestrictionUnit_degreeUnit_top U n)).trans hX.symm)

/-- As an actual presheaf equation, the original degree unit followed
by the endpoint is literal restriction along the open-image functor. -/
theorem degreeUnit_integerRestrictionUnit :
    degreeUnit (TopCat.of U) ≫ (integerRestrictionUnit U).hom =
      Functor.whiskerLeft (OpenRestriction.openImage U).op (degreeUnit X) := by
  apply NatTrans.ext
  funext W
  apply ConcreteCategory.hom_ext
  intro n
  exact integerRestrictionUnit_degreeUnit_app U W.unop n

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction
