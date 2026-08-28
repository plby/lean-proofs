import Wikipedia.HopfProblem.ConstantSheafSingularComparisonGlobalCohomology
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonResolution

/-!
# Native constant-sheaf Ext cohomology and actual singular cohomology

In degrees one and two, the original Ext-defined cohomology of the
constant additive sheaf is canonically isomorphic to the native homology
of the original singular cochain complex. The proof uses the actual
locally exact cochain-sheaf resolution, proved acyclicity of its terms,
and the actual global sheafification-unit comparison. There is no
assumed sheaf--singular comparison in these statements or constructions.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0})
  [CompactSpace X] [T2Space X]

/-- The canonical comparison between genuine constant-sheaf `Ext` H¹
and the original singular cohomology, for arbitrary abelian coefficients. -/
def constantSheafH1Iso (hLC : LocallyContractibleSpace X) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (ConstantSheafFirstCohomology.Constant.sheaf X A) 1) ≅
      (singularCochainComplex X A).homology 1 :=
  constantSheafGlobalH1Iso X A hLC ≪≫ (globalCochainCohomologyIso X A 0).symm

/-- The canonical comparison between genuine constant-sheaf `Ext` H²
and original singular cohomology, for arbitrary abelian coefficients. -/
def constantSheafH2Iso (hLC : LocallyContractibleSpace X) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (ConstantSheafFirstCohomology.Constant.sheaf X A) 2) ≅
      (singularCochainComplex X A).homology 2 :=
  constantSheafGlobalH2Iso X A hLC ≪≫ (globalCochainCohomologyIso X A 1).symm

/-- The H¹ comparison is characterized by the actual unit-induced
global singular-cochain map and the actual Ext resolution comparison. -/
@[reassoc]
theorem constantSheafH1Iso_global (hLC : LocallyContractibleSpace X) :
    (constantSheafH1Iso X A hLC).hom ≫
      HomologicalComplex.homologyMap (globalCochainComparison X A) 1 =
        (constantSheafGlobalH1Iso X A hLC).hom := by
  let a : AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (ConstantSheafFirstCohomology.Constant.sheaf X A) 1) ⟶
      (globalSheafCochainComplex X A).homology 1 :=
    (constantSheafGlobalH1Iso X A hLC).hom
  let e := globalCochainCohomologyIso X A 0
  exact (Category.assoc a e.inv e.hom).trans
    ((congrArg (fun f => a ≫ f) e.inv_hom_id).trans (Category.comp_id a))

/-- The same canonical characterization in degree two. -/
@[reassoc]
theorem constantSheafH2Iso_global (hLC : LocallyContractibleSpace X) :
    (constantSheafH2Iso X A hLC).hom ≫
      HomologicalComplex.homologyMap (globalCochainComparison X A) 2 =
        (constantSheafGlobalH2Iso X A hLC).hom := by
  let a : AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (ConstantSheafFirstCohomology.Constant.sheaf X A) 2) ⟶
      (globalSheafCochainComplex X A).homology 2 :=
    (constantSheafGlobalH2Iso X A hLC).hom
  let e := globalCochainCohomologyIso X A 1
  exact (Category.assoc a e.inv e.hom).trans
    ((congrArg (fun f => a ≫ f) e.inv_hom_id).trans (Category.comp_id a))

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
