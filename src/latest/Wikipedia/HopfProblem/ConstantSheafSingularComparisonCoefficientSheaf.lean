import Wikipedia.HopfProblem.ConstantSheafSingularComparisonSheafBasic

/-!
# Coefficient changes on the actual sheafified cochain resolution

All coefficient maps are the native constant-functor maps or the native
sheafification of literal postcomposition on singular cochains.  The
augmentation square and the unit square commute before and after
sheafification, for arbitrary homomorphisms of abelian coefficient groups.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

variable (X : TopCat.{0}) {A B C : AddCommGrpCat.{0}}

/-- The native constant-presheaf map of coefficient groups. -/
def constantPresheafCoefficientMap (α : A ⟶ B) :
    ConstantSheafFirstCohomology.Constant.presheaf X A ⟶
      ConstantSheafFirstCohomology.Constant.presheaf X B :=
  (Functor.const (Opens X)ᵒᵖ).map α

@[simp]
theorem constantPresheafCoefficientMap_app (α : A ⟶ B) (U : Opens X) :
    (constantPresheafCoefficientMap X α).app (op U) = α := rfl

/-- The constant augmentation commutes with actual coefficient changes. -/
@[reassoc]
theorem constantAugmentation_coefficient_naturality (α : A ⟶ B) :
    constantPresheafCoefficientMap X α ≫ constantAugmentation X B =
      constantAugmentation X A ≫ presheafCoefficientMap X α 0 := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  exact (coefficientMap_constant A U.unop α a).symm

/-- Native sheafification of actual degreewise coefficient postcomposition. -/
def sheafCoefficientMap (α : A ⟶ B) (n : ℕ) :
    cochainSheaf X A n ⟶ cochainSheaf X B n :=
  (cochainSheafification X).map (presheafCoefficientMap X α n)

/-- Native sheafification of the whole coefficient cochain map. -/
def sheafCoefficientComplexMap (α : A ⟶ B) :
    cochainSheafComplex X A ⟶ cochainSheafComplex X B :=
  ((cochainSheafification X).mapHomologicalComplex (.up ℕ)).map
    (presheafCoefficientComplexMap X α)

@[simp]
theorem sheafCoefficientComplexMap_f (α : A ⟶ B) (n : ℕ) :
    (sheafCoefficientComplexMap X α).f n = sheafCoefficientMap X α n := rfl

/-- The actual sheafification units commute with coefficient postcomposition. -/
@[reassoc]
theorem cochainSheafUnit_coefficient_naturality (α : A ⟶ B) (n : ℕ) :
    cochainSheafUnit X A n ≫ (sheafCoefficientMap X α n).hom =
      presheafCoefficientMap X α n ≫ cochainSheafUnit X B n :=
  (CategoryTheory.toSheafify_naturality (Opens.grothendieckTopology X)
    (presheafCoefficientMap X α n)).symm

/-- Coefficient change on the source is literally Mathlib's constant-sheaf map. -/
@[reassoc]
theorem sheafAugmentation_coefficient_naturality (α : A ⟶ B) :
    (CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{0}).map α ≫ sheafAugmentation X B =
        sheafAugmentation X A ≫ sheafCoefficientMap X α 0 := by
  exact ((cochainSheafification X).map_comp
    (constantPresheafCoefficientMap X α) (constantAugmentation X B)).symm.trans
      ((congrArg (cochainSheafification X).map
        (constantAugmentation_coefficient_naturality X α)).trans
          ((cochainSheafification X).map_comp
            (constantAugmentation X A) (presheafCoefficientMap X α 0)))

/-- The native constant-sheaf unit respects the same literal coefficient map. -/
@[reassoc]
theorem constantUnit_coefficient_naturality (α : A ⟶ B) :
    ConstantSheafFirstCohomology.Constant.unit X A ≫
      ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{0}).map α).hom =
      constantPresheafCoefficientMap X α ≫
        ConstantSheafFirstCohomology.Constant.unit X B :=
  (CategoryTheory.toSheafify_naturality (Opens.grothendieckTopology X)
    (constantPresheafCoefficientMap X α)).symm

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
