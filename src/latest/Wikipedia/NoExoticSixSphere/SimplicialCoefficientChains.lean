import Wikipedia.HopfProblem.SphereHomologyCoefficientsChainsFunctor
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.MonoCoprod
import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst

/-!
# Native simplicial chains for the actual small-simplex subcomplex

The native chain functor preserves monomorphisms and colimits with any
integral coefficient object. Its coefficient functor is exact, degree by
degree, on an arbitrary simplicial set. These facts will be applied to the
union of the actual singular subcomplexes of two subsets.
-/

noncomputable section

open CategoryTheory Limits Simplicial
open Wikipedia.HopfProblem SphereHomologyCoefficients

namespace NoExoticSixSphere.SimplicialCoefficients

/-- The native simplicial-chain functor with the specified coefficient object. -/
abbrev chains (A : ModuleCat.{0} ℤ) : SSet.{0} ⥤ ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  (SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).obj A

instance chains_preservesMonomorphisms (A : ModuleCat.{0} ℤ) :
    (chains A).PreservesMonomorphisms where
  preserves f _ := by
    dsimp [chains, SSet.chainComplexFunctor]
    apply +allowSynthFailures Functor.map_mono
    apply +allowSynthFailures Functor.map_mono
    dsimp [SSet, SimplicialObject.whiskering, SimplicialObject]
    infer_instance

instance chains_preservesColimitsOfShape (A : ModuleCat.{0} ℤ)
    (J : Type) [Category J] : PreservesColimitsOfShape J (chains A) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  change PreservesColimitsOfShape J
    ((evaluation SimplexCategoryᵒᵖ (Type)).obj (Opposite.op ⦋n⦌) ⋙ sigmaConst.obj A)
  infer_instance

/-- Native coefficient change on one fixed simplicial set. -/
def coefficientFunctor (X : SSet.{0}) :
    ModuleCat.{0} ℤ ⥤ ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  SSet.chainComplexFunctor (ModuleCat.{0} ℤ) ⋙
    (evaluation SSet (ChainComplex (ModuleCat.{0} ℤ) ℕ)).obj X

instance coefficientFunctor_additive (X : SSet.{0}) : (coefficientFunctor X).Additive := by
  unfold coefficientFunctor
  infer_instance

/-- Exactness uses the original coproducts of coefficient modules in each degree. -/
theorem coefficientFunctor_shortExact (X : SSet.{0})
    (S : ShortComplex (ModuleCat.{0} ℤ)) (hS : S.ShortExact) :
    (S.map (coefficientFunctor X)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact coefficientCoproductFunctor_shortExact (X _⦋n⦌) S hS

end NoExoticSixSphere.SimplicialCoefficients
