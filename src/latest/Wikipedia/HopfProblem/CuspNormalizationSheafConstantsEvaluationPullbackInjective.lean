import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsEvaluationNaturalityBasic

/-!
# Constant-sheaf pullback along a surjection is injective

Every target point has a preimage.  Equality of the actual pulled-back
sections therefore gives equality of the scalar values of their germs
at every target point.  The canonical constant-sheaf stalk equivalence
and the actual sheaf separatedness theorem prove componentwise
injectivity.  No analytic or local-connectedness hypothesis is used.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.CuspNormalization.SheafConstants

variable {X Y : TopCat.{0}}

/-- Surjectivity of the actual continuous map makes the actual additive
constant-sheaf pullback injective on every open set. -/
theorem additivePullbackMap_app_injective_of_surjective
    (p : X ⟶ Y) (hp : Function.Surjective p) (U : Opens Y) :
    Function.Injective ((additivePullbackMap p).hom.app (op U)) := by
  intro s t hst
  apply TopCat.Presheaf.section_ext (complexAdditiveSheaf Y) U s t
  intro b hb
  obtain ⟨y, rfl⟩ := hp b
  apply (complexAdditiveSheafStalkEquiv Y (p y)).injective
  exact (constantGermValue_pullback p U y hb s).symm.trans
    ((congrArg (fun u => complexAdditiveSheafStalkEquiv X y
      (TopCat.Presheaf.germ (complexAdditiveSheaf X).obj
        ((Opens.map p).obj U) y hb u)) hst).trans
      (constantGermValue_pullback p U y hb t))

/-- The actual additive constant-sheaf pullback along a continuous
surjection is a monomorphism, without any analytic assumptions. -/
theorem additivePullbackMap_mono_of_surjective
    (p : X ⟶ Y) (hp : Function.Surjective p) : Mono (additivePullbackMap p) :=
  CategoryTheory.Sheaf.mono_of_injective _ fun U =>
    additivePullbackMap_app_injective_of_surjective p hp U.unop

/-- The ring-sheaf pullback has the same actual component functions,
so they too are injective along every continuous surjection. -/
theorem pullbackMap_app_injective_of_surjective
    (p : X ⟶ Y) (hp : Function.Surjective p) (U : Opens Y) :
    Function.Injective ((pullbackMap p).hom.app (op U)) :=
  additivePullbackMap_app_injective_of_surjective p hp U

/-- The actual ring-valued constant-sheaf pullback is also a monomorphism. -/
theorem pullbackMap_mono_of_surjective
    (p : X ⟶ Y) (hp : Function.Surjective p) : Mono (pullbackMap p) :=
  CategoryTheory.Sheaf.mono_of_injective _ fun U =>
    pullbackMap_app_injective_of_surjective p hp U.unop

end Wikipedia.HopfProblem.CuspNormalization.SheafConstants
