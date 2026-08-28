import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCochainSingular
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Additive dependence of native singular cohomology on its coefficient group

The coefficient functor uses the existing literal postcomposition maps
on the original singular cochains.  Both that functor and its composite
with native homology are additive.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

variable (X : Type) [TopologicalSpace X]

/-- The zero coefficient map gives the zero map on the original cochains. -/
@[simp]
theorem coefficientMap_zero (A B : AddCommGrpCat.{0}) :
    coefficientMap X (0 : A ⟶ B) = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply AddCommGrpCat.hom_ext
  ext φ c
  rfl

/-- Addition of actual coefficient maps is preserved on the original cochains. -/
@[simp]
theorem coefficientMap_add {A B : AddCommGrpCat.{0}} (α β : A ⟶ B) :
    coefficientMap X (α + β) = coefficientMap X α + coefficientMap X β := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply AddCommGrpCat.hom_ext
  ext φ c
  rfl

/-- The actual singular cochain complex as a covariant functor of its
abelian coefficient group. -/
def coefficientCochainFunctor :
    AddCommGrpCat.{0} ⥤ CochainComplex AddCommGrpCat.{0} ℕ where
  obj A := singularCochainComplex X A
  map α := coefficientMap X α
  map_id A := coefficientMap_id X A
  map_comp α β := coefficientMap_comp X α β

@[simp]
theorem coefficientCochainFunctor_obj (A : AddCommGrpCat.{0}) :
    (coefficientCochainFunctor X).obj A = singularCochainComplex X A := rfl

@[simp]
theorem coefficientCochainFunctor_map {A B : AddCommGrpCat.{0}} (α : A ⟶ B) :
    (coefficientCochainFunctor X).map α = coefficientMap X α := rfl

instance coefficientCochainFunctor_additive : (coefficientCochainFunctor X).Additive where
  map_add := by
    intro A B α β
    exact coefficientMap_add X α β

/-- The actual native singular cohomology, covariant in the coefficient
group, in every degree. -/
def coefficientCohomologyFunctor (n : ℕ) : AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0} :=
  coefficientCochainFunctor X ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{0} (ComplexShape.up ℕ) n

@[simp]
theorem coefficientCohomologyFunctor_obj (n : ℕ) (A : AddCommGrpCat.{0}) :
    (coefficientCohomologyFunctor X n).obj A = (singularCochainComplex X A).homology n := rfl

@[simp]
theorem coefficientCohomologyFunctor_map (n : ℕ) {A B : AddCommGrpCat.{0}} (α : A ⟶ B) :
    (coefficientCohomologyFunctor X n).map α =
      HomologicalComplex.homologyMap (coefficientMap X α) n := rfl

instance coefficientCohomologyFunctor_additive (n : ℕ) :
    (coefficientCohomologyFunctor X n).Additive := by
  dsimp only [coefficientCohomologyFunctor]
  infer_instance

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
