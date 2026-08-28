import Wikipedia.HopfProblem.SheafSingularCupComparisonRowGlobalUnitComparison
import Wikipedia.HopfProblem.SheafSingularCupComparisonRowGlobalDiagram
import Wikipedia.HopfProblem.SheafSingularCupComparisonResolutionRowComparison
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonConcreteCoefficients

/-!
# Exact agreement with the original native sheaf/singular comparison

The original Ext comparison followed by the actual ring-unit map equals
the actual row-resolution comparison followed by its canonical coface
quotient isomorphism. No native Ext comparison is redefined here.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.RowGlobal

open CuspNormalization ConstantSheafSingularComparison ResolutionRow

variable (X : TopCat.{0})

/-- The row window map is exactly the one used in the original resolution comparison. -/
theorem oneOriginalIso_hom (hLC : LocallyContractibleSpace X) :
    (oneOriginalIso X).hom = rowOneToOriginalHomology X hLC := rfl

/-- The second row window map is likewise the original resolution map. -/
theorem twoOriginalIso_hom (hLC : LocallyContractibleSpace X) :
    (twoOriginalIso X).hom = rowTwoToOriginalHomology X hLC := rfl

variable [CompactSpace X] [T2Space X]

/-- The original sheaf/singular H¹ comparison commutes with the original global row map. -/
theorem complexSheafH1Iso_original (hLC : LocallyContractibleSpace X) :
    (complexSheafH1Iso X hLC).hom ≫
        HomologicalComplex.homologyMap (globalCochainComparison X (AddCommGrpCat.of ℂ)) 1 =
      (rowH1Iso X hLC).hom ≫ (oneOriginalIso X).hom := by
  let f := (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 1).map
    (SheafConstants.complexAdditiveSheafIso X).hom
  let g := (constantSheafH1Iso X (AddCommGrpCat.of ℂ) hLC).hom
  let m := HomologicalComplex.homologyMap
    (globalCochainComparison X (AddCommGrpCat.of ℂ)) 1
  change (f ≫ g) ≫ m = _
  exact (Category.assoc f g m).trans
    ((congrArg (fun k => f ≫ k)
      (constantSheafH1Iso_global X (AddCommGrpCat.of ℂ) hLC)).trans
        (rowToOriginal_h1Iso X hLC))

/-- The original sheaf/singular H² comparison commutes with the original global row map. -/
theorem complexSheafH2Iso_original (hLC : LocallyContractibleSpace X) :
    (complexSheafH2Iso X hLC).hom ≫
        HomologicalComplex.homologyMap (globalCochainComparison X (AddCommGrpCat.of ℂ)) 2 =
      (rowH2Iso X hLC).hom ≫ (twoOriginalIso X).hom := by
  let f := (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 2).map
    (SheafConstants.complexAdditiveSheafIso X).hom
  let g := (constantSheafH2Iso X (AddCommGrpCat.of ℂ) hLC).hom
  let m := HomologicalComplex.homologyMap
    (globalCochainComparison X (AddCommGrpCat.of ℂ)) 2
  change (f ≫ g) ≫ m = _
  exact (Category.assoc f g m).trans
    ((congrArg (fun k => f ≫ k)
      (constantSheafH2Iso_global X (AddCommGrpCat.of ℂ) hLC)).trans
        (rowToOriginal_h2Iso X hLC))

/-- The actual unit map intertwines the original native H¹ comparison with the row quotient. -/
theorem complexSheafH1Iso_unit (hLC : LocallyContractibleSpace X) :
    (complexSheafH1Iso X hLC).hom ≫ AddCommGrpCat.ofHom (unitOne X) =
      (rowH1Iso X hLC).hom ≫ (oneHomologyIso X).hom := by
  exact comparison_of_unit_and_iso (complexSheafH1Iso X hLC).hom
    (HomologicalComplex.homologyMap (globalCochainComparison X (AddCommGrpCat.of ℂ)) 1)
    (oneOriginalIso X) (rowH1Iso X hLC).hom (oneHomologyIso X).hom
    (AddCommGrpCat.ofHom (unitOne X)) (unitOne_original X)
    (complexSheafH1Iso_original X hLC)

/-- The actual unit map intertwines the original native H² comparison with the row quotient. -/
theorem complexSheafH2Iso_unit (hLC : LocallyContractibleSpace X) :
    (complexSheafH2Iso X hLC).hom ≫ AddCommGrpCat.ofHom (unitTwo X) =
      (rowH2Iso X hLC).hom ≫ (twoHomologyIso X).hom := by
  exact comparison_of_unit_and_iso (complexSheafH2Iso X hLC).hom
    (HomologicalComplex.homologyMap (globalCochainComparison X (AddCommGrpCat.of ℂ)) 2)
    (twoOriginalIso X) (rowH2Iso X hLC).hom (twoHomologyIso X).hom
    (AddCommGrpCat.ofHom (unitTwo X)) (unitTwo_original X)
    (complexSheafH2Iso_original X hLC)

/-- Pointwise compatibility retains the original native complex sheaf/singular H¹ map. -/
theorem complexSheafH1Equiv_unit (hLC : LocallyContractibleSpace X)
    (a : CategoryTheory.Sheaf.H.{0} (SheafConstants.complexAdditiveSheaf X) 1) :
    unitOne X (complexSheafH1Equiv X hLC a) =
      oneHomologyEquiv X ((rowH1Iso X hLC).hom a) :=
  congrArg (fun f : AddCommGrpCat.of
    (CategoryTheory.Sheaf.H.{0} (SheafConstants.complexAdditiveSheaf X) 1) ⟶
      AddCommGrpCat.of (RingCochains.globalData X).CohomologyOne => f.hom a)
    (complexSheafH1Iso_unit X hLC)

/-- Pointwise compatibility retains the original native complex sheaf/singular H² map. -/
theorem complexSheafH2Equiv_unit (hLC : LocallyContractibleSpace X)
    (a : CategoryTheory.Sheaf.H.{0} (SheafConstants.complexAdditiveSheaf X) 2) :
    unitTwo X (complexSheafH2Equiv X hLC a) =
      twoHomologyEquiv X ((rowH2Iso X hLC).hom a) :=
  congrArg (fun f : AddCommGrpCat.of
    (CategoryTheory.Sheaf.H.{0} (SheafConstants.complexAdditiveSheaf X) 2) ⟶
      AddCommGrpCat.of (RingCochains.globalData X).CohomologyTwo => f.hom a)
    (complexSheafH2Iso_unit X hLC)

end Wikipedia.HopfProblem.SheafSingularCupComparison.RowGlobal
