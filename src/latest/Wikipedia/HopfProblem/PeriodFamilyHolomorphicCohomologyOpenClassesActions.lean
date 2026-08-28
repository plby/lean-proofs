import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassesBasic

/-!
# Original scalar actions on native neighborhood cohomology

The neighborhood group remains the actual `Sheaf.H'`. Applying the
original additive Ext coefficient functor to the original scalar sheaf
endomorphisms gives its genuine scalar action. Its value is precisely
the component of Mathlib's actual cohomology-presheaf scalar morphism.
The vector-space structure is not transported through a comparison.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClasses

open HolomorphicSheafCohomology

section Generic

variable (X : TopCat.{0}) (U : Opens X) (q : ℕ)

/-- Evaluation of the original cohomology-presheaf functor at the
original open; its values are exactly the existing neighborhood groups. -/
def openCohomologyFunctor : TopCat.Sheaf AddCommGrpCat.{0} X ⥤ AddCommGrpCat.{0} :=
  CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) q ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op U)

/-- Additivity is that of the actual native coefficient Ext functor. -/
instance openCohomologyFunctor_additive : (openCohomologyFunctor X U q).Additive where
  map_add := by
    intro F G f g
    change (CategoryTheory.Abelian.extFunctorObj (OpenRestriction.freeOpen U) q).map (f + g) =
      (CategoryTheory.Abelian.extFunctorObj (OpenRestriction.freeOpen U) q).map f +
        (CategoryTheory.Abelian.extFunctorObj (OpenRestriction.freeOpen U) q).map g
    exact Functor.map_add _

/-- An original sheaf scalar action induces its original scalar action
on the genuine open cohomology group. -/
def openScalarEnd (F : TopCat.Sheaf AddCommGrpCat.{0} X) (ρ : ℂ →+* End F) :
    ℂ →+* End (CategoryTheory.Sheaf.H'.{0} F q U) :=
  (CuspNormalization.SheafCohomology.mapEndRingHom (openCohomologyFunctor X U q) F).comp ρ

end Generic

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

local notation "IT" => modelWithCornersSelf ℂ (V × ComplexPlane₂)

/-- The actual coefficient functor on the original neighborhood `Ext`
group sends the original scalar sheaf maps to its scalar endomorphisms. -/
def neighborhoodScalarEnd (P : HolomorphicPeriodMap V B) (U : Opens B) (q : ℕ) :
    ℂ →+* End (neighborhoodCohomology P U q) := by
  letI := P.totalChartedSpace
  exact openScalarEnd (TopCat.of P.TotalSpace)
    (PeriodFamilyHigherDirectImage.Zero.basePreimage P U) q
    (PeriodFamilyHigherDirectImage.Zero.totalAdditiveSheaf P)
    (CuspNormalization.SheafCohomology.holomorphicScalarEnd IT P.TotalSpace)

/-- This action is literally the original cohomology-presheaf map of
the original total-space scalar sheaf endomorphism on the chosen open. -/
theorem neighborhoodScalarEnd_apply (P : HolomorphicPeriodMap V B) (U : Opens B)
    (q : ℕ) (c : ℂ) (x : neighborhoodCohomology P U q) :
    (neighborhoodScalarEnd P U q c).asHom x =
      (((CategoryTheory.Sheaf.cohomologyPresheafFunctor
        (Opens.grothendieckTopology (TopCat.of P.TotalSpace)) q).map
          (PeriodFamilyHigherDirectImage.Zero.totalScalarEnd P c)).app
        (op (PeriodFamilyHigherDirectImage.Zero.basePreimage P U))) x := rfl

/-- The actual sheaf-induced complex module on the original native
neighborhood group, before any comparison or class construction. -/
@[instance_reducible] def neighborhoodCohomologyModule
    (P : HolomorphicPeriodMap V B) (U : Opens B) (q : ℕ) :
    Module ℂ (neighborhoodCohomology P U q) :=
  CuspNormalization.SheafCohomology.moduleOfScalarEnd (neighborhoodCohomology P U q)
    (neighborhoodScalarEnd P U q)

/-- Scalar multiplication retains its exact original functorial meaning. -/
theorem neighborhoodCohomologyModule_smul (P : HolomorphicPeriodMap V B)
    (U : Opens B) (q : ℕ) (c : ℂ) (x : neighborhoodCohomology P U q) :
    letI := neighborhoodCohomologyModule P U q
    c • x =
      (((CategoryTheory.Sheaf.cohomologyPresheafFunctor
        (Opens.grothendieckTopology (TopCat.of P.TotalSpace)) q).map
          (PeriodFamilyHigherDirectImage.Zero.totalScalarEnd P c)).app
        (op (PeriodFamilyHigherDirectImage.Zero.basePreimage P U))) x := rfl

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClasses
