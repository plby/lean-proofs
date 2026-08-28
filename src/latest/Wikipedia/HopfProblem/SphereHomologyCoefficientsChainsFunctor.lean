import Wikipedia.HopfProblem.SphereHomologyCoefficientsBasic
import Wikipedia.HopfProblem.SphereHomologyCoefficientsChainsCoproduct
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Exactness of the native singular-chain coefficient functor

Evaluation in each degree is the exact coproduct functor, on Mathlib's
chosen singular chain groups themselves.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial

namespace Wikipedia.HopfProblem.SphereHomologyCoefficients

/-- The actual coefficient functor at a fixed topological space. -/
def nativeCoefficientFunctor (X : Type) [TopologicalSpace X] :
    ModuleCat ℤ ⥤ ChainComplex (ModuleCat ℤ) ℕ :=
  AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ) ⋙
    (evaluation TopCat (ChainComplex (ModuleCat ℤ) ℕ)).obj (TopCat.of X)

instance nativeCoefficientFunctor_additive (X : Type) [TopologicalSpace X] :
    (nativeCoefficientFunctor X).Additive := by
  unfold nativeCoefficientFunctor
  infer_instance

theorem nativeCoefficientFunctor_obj (X : Type) [TopologicalSpace X] (A : ModuleCat ℤ) :
    (nativeCoefficientFunctor X).obj A = coefficientComplex A X := rfl

theorem nativeCoefficientFunctor_map (X : Type) [TopologicalSpace X]
    {A B : ModuleCat ℤ} (f : A ⟶ B) :
    (nativeCoefficientFunctor X).map f = coefficientComplexMap f X := rfl

/-- Evaluation of coefficient change is the native coproduct of coefficient maps. -/
theorem coefficientComplexMap_f {A B : ModuleCat ℤ} (f : A ⟶ B)
    (X : Type) [TopologicalSpace X] (n : ℕ) :
    (coefficientComplexMap f X).f n =
      (coefficientCoproductFunctor ((TopCat.toSSet.obj (TopCat.of X)) _⦋n⦌)).map f := rfl

/-- Every short exact coefficient sequence gives a short exact sequence of native chains. -/
theorem nativeCoefficientFunctor_shortExact (X : Type) [TopologicalSpace X]
    (S : ShortComplex (ModuleCat ℤ)) (hS : S.ShortExact) :
    (S.map (nativeCoefficientFunctor X)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact coefficientCoproductFunctor_shortExact
    ((TopCat.toSSet.obj (TopCat.of X)) _⦋n⦌) S hS

/-- The native coefficient map for multiplication is the literal scalar chain map. -/
theorem coefficientComplexMap_multiplication (p : ℕ) (X : Type) [TopologicalSpace X] :
    coefficientComplexMap ((p : ℤ) • 𝟙 (ModuleCat.of ℤ ℤ)) X =
      multiplicationChainMap p X := by
  change (nativeCoefficientFunctor X).map ((p : ℤ) • 𝟙 (ModuleCat.of ℤ ℤ)) =
    (p : ℤ) • 𝟙 ((nativeCoefficientFunctor X).obj (ModuleCat.of ℤ ℤ))
  rw [CategoryTheory.Functor.map_zsmul, CategoryTheory.Functor.map_id]

end Wikipedia.HopfProblem.SphereHomologyCoefficients
