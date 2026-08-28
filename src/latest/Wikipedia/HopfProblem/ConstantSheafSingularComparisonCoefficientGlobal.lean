import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCoefficientSheaf
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonGlobalComplex

/-!
# Coefficient naturality of the genuine global singular comparison

The coefficient map on the target is literal global sections of the
sheafified coefficient cochain map.  Naturality of the original singular
pullback to the top open and of the native sheafification unit proves the
commuting square on actual complexes, and therefore on native homology.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

open CuspNormalization.SheafCohomologyResolution

variable (X : TopCat.{0}) {A B : AddCommGrpCat.{0}}

/-- Literal global sections of the native sheafified coefficient cochain map. -/
def globalSheafCoefficientMap (α : A ⟶ B) :
    globalSheafCochainComplex X A ⟶ globalSheafCochainComplex X B :=
  ((globalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).map
    (sheafCoefficientComplexMap X α)

@[simp]
theorem globalSheafCoefficientMap_f (α : A ⟶ B) (n : ℕ) :
    (globalSheafCoefficientMap X α).f n =
      (sheafCoefficientMap X α n).hom.app (op ⊤) := rfl

/-- The original global unit is natural under actual coefficient changes. -/
@[reassoc]
theorem globalCochainUnit_coefficient_naturality (α : A ⟶ B) (n : ℕ) :
    globalCochainUnit X A n ≫ (sheafCoefficientMap X α n).hom.app (op ⊤) =
      (coefficientMap X α).f n ≫ globalCochainUnit X B n := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro φ
  let f : C((⊤ : Opens X), X) := ⟨Subtype.val, continuous_subtype_val⟩
  have hp := congrArg
    (fun g : singularCochainComplex X A ⟶ singularCochainComplex (⊤ : Opens X) B =>
      g.f n φ)
    (coefficientMap_naturality α f)
  have hu := congrArg
    (fun g : (cochainPresheaf X A n).obj (op ⊤) ⟶
      (cochainSheaf X B n).obj.obj (op ⊤) =>
      g (restrictGlobalCochain A n φ ⊤))
    (NatTrans.congr_app (cochainSheafUnit_coefficient_naturality X α n) (op ⊤))
  exact hu.trans (congrArg ((cochainSheafUnit X B n).app (op ⊤)) hp)

/-- Coefficient change commutes with the actual map of global cochain complexes. -/
@[reassoc]
theorem globalCochainComparison_coefficient_naturality (α : A ⟶ B) :
    globalCochainComparison X A ≫ globalSheafCoefficientMap X α =
      coefficientMap X α ≫ globalCochainComparison X B := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact globalCochainUnit_coefficient_naturality X α n

/-- The same naturality square holds on native cohomology, in every degree. -/
@[reassoc]
theorem globalCochainComparison_homology_coefficient_naturality (α : A ⟶ B) (n : ℕ) :
    HomologicalComplex.homologyMap (globalCochainComparison X A) n ≫
      HomologicalComplex.homologyMap (globalSheafCoefficientMap X α) n =
      HomologicalComplex.homologyMap (coefficientMap X α) n ≫
        HomologicalComplex.homologyMap (globalCochainComparison X B) n := by
  exact (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    ((congrArg (fun f => HomologicalComplex.homologyMap f n)
      (globalCochainComparison_coefficient_naturality X α)).trans
        (HomologicalComplex.homologyMap_comp _ _ n))

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
