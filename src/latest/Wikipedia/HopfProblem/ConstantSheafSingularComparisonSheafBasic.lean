import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPresheafAugmentation
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonSheafifyBasic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The genuine sheafified singular cochain complex

This applies the native exact sheafification functor to the actual
cochain presheaves. The coefficient augmentation and all differentials
are the images of their original presheaf maps. The original unit is a
map of the full presheaf complexes.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0})

/-- Native sheafification, named here only to expose its actual maps. -/
abbrev cochainSheafification : TopCat.Presheaf AddCommGrpCat.{0} X ⥤
    TopCat.Sheaf AddCommGrpCat.{0} X :=
  presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}

instance cochainSheafification_additive : (cochainSheafification X).Additive :=
  inferInstanceAs (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).Additive

/-- The actual sheaf of germs of singular cochains. -/
abbrev cochainSheaf (n : ℕ) : TopCat.Sheaf AddCommGrpCat.{0} X :=
  Sheafification.sheaf (cochainPresheaf X A n)

/-- The differential induced by the original singular boundary. -/
def sheafDifferential (i j : ℕ) : cochainSheaf X A i ⟶ cochainSheaf X A j :=
  (cochainSheafification X).map (presheafDifferential X A i j)

/-- Apply the native sheafification functor to the entire actual complex. -/
abbrev cochainSheafComplex : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ :=
  ((cochainSheafification X).mapHomologicalComplex (.up ℕ)).obj (cochainPresheafComplex X A)

@[simp]
theorem cochainSheafComplex_X (n : ℕ) :
    (cochainSheafComplex X A).X n = cochainSheaf X A n := rfl

@[simp]
theorem cochainSheafComplex_d (i j : ℕ) :
    (cochainSheafComplex X A).d i j = sheafDifferential X A i j := rfl

/-- The actual unit in each degree of the original cochain presheaf. -/
def cochainSheafUnit (n : ℕ) : cochainPresheaf X A n ⟶ (cochainSheaf X A n).obj :=
  Sheafification.unit (cochainPresheaf X A n)

/-- The original units commute with the original differentials. -/
@[reassoc]
theorem cochainSheafUnit_d (i j : ℕ) :
    cochainSheafUnit X A i ≫ (sheafDifferential X A i j).hom =
      presheafDifferential X A i j ≫ cochainSheafUnit X A j :=
  (CategoryTheory.toSheafify_naturality (Opens.grothendieckTopology X)
    (presheafDifferential X A i j)).symm

/-- The genuine constant additive sheaf augments the sheafified cochains. -/
def sheafAugmentation : ConstantSheafFirstCohomology.Constant.sheaf X A ⟶
    cochainSheaf X A 0 :=
  (cochainSheafification X).map (constantAugmentation X A)

/-- The augmented sequence is an actual complex. -/
theorem sheafAugmentation_d : sheafAugmentation X A ≫ sheafDifferential X A 0 1 = 0 := by
  exact ((cochainSheafification X).map_comp
    (constantAugmentation X A) (presheafDifferential X A 0 1)).symm.trans
      ((congrArg (cochainSheafification X).map (constantAugmentation_d X A)).trans
        ((cochainSheafification X).map_zero _ _))

/-- The original augmented short complex whose local exactness is to be proved. -/
abbrev initialSheafComplex : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X) :=
  ShortComplex.mk (sheafAugmentation X A) (sheafDifferential X A 0 1)
    (sheafAugmentation_d X A)

/-- The actual sheafification unit intertwines the original constant augmentation. -/
@[reassoc]
theorem constantUnit_sheafAugmentation :
    ConstantSheafFirstCohomology.Constant.unit X A ≫ (sheafAugmentation X A).hom =
      constantAugmentation X A ≫ cochainSheafUnit X A 0 :=
  (CategoryTheory.toSheafify_naturality (Opens.grothendieckTopology X)
    (constantAugmentation X A)).symm

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
