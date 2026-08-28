import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsEvaluationSheaf
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Surjectivity of actual constant-sheaf evaluation

Actual sheafified constant sections realize every scalar on a
neighbourhood of the skyscraper support.  On other opens its section
group is terminal.  Thus this single-point evaluation is surjective on
every section group and is an epimorphism of the genuine sheaves.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.CuspNormalization.SheafConstants

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]

/-- Actual constant representatives make evaluation onto a single-point
skyscraper surjective on every open set. -/
theorem constantEvaluationAt_app_surjective (p : TopCat.of M ⟶ TopCat.of B)
    (y : M) (b : B) (hy : p y = b) (U : Opens B) :
    Function.Surjective ((constantEvaluationAt p y b hy).hom.app (op U)) := by
  classical
  intro t
  by_cases hb : b ∈ U
  · let e := SheafEvaluation.skyscraperSectionIso (X := TopCat.of B)
      b (AddCommGrpCat.of ℂ) U hb
    let c : ℂ := e.hom t
    refine ⟨(additiveUnit (TopCat.of M)).app (op ((Opens.map p).obj U)) c, ?_⟩
    apply e.addCommGroupIsoToAddEquiv.injective
    exact constantEvaluationAt_app_unit p y b hy U hb c
  · refine ⟨0, ?_⟩
    apply AddCommGrpCat.asHom_injective
    exact (SheafEvaluation.skyscraperSectionIsTerminal (X := TopCat.of B)
      b (AddCommGrpCat.of ℂ) U hb).hom_ext _ _

/-- The independent actual constant evaluation is an epimorphism of sheaves. -/
instance constantEvaluationAt_epi (p : TopCat.of M ⟶ TopCat.of B)
    (y : M) (b : B) (hy : p y = b) : Epi (constantEvaluationAt p y b hy) := by
  let : ∀ U : (Opens (TopCat.of B))ᵒᵖ,
      Epi ((constantEvaluationAt p y b hy).hom.app U) := fun U =>
    ConcreteCategory.epi_of_surjective _
      (constantEvaluationAt_app_surjective p y b hy U.unop)
  let : Epi (constantEvaluationAt p y b hy).hom := NatTrans.epi_of_epi_app _
  exact CategoryTheory.Sheaf.Hom.epi_of_presheaf_epi
    (Opens.grothendieckTopology (TopCat.of B)) AddCommGrpCat (constantEvaluationAt p y b hy)

instance constantEvaluation_epi (p : TopCat.of M ⟶ TopCat.of B) (y : M) :
    Epi (constantEvaluation p y) :=
  constantEvaluationAt_epi p y (p y) rfl

end Wikipedia.HopfProblem.CuspNormalization.SheafConstants
