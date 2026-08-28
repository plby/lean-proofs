import Wikipedia.HopfProblem.CuspNormalizationSheafEvaluationSheaf
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Actual holomorphic evaluation is a surjective sheaf morphism

On every neighborhood of the chosen base point, actual constant
holomorphic sections realize all skyscraper sections. On every other
open set, the skyscraper section group is terminal. Consequently every
component of evaluation is surjective, and evaluation is an epimorphism
of the actual sheaves.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafEvaluation

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  {B : Type} [TopologicalSpace B]

/-- Every actual section component of evaluation is surjective, with
no hypothesis on the continuous base map. -/
theorem evaluationAt_app_surjective (p : TopCat.of M ⟶ TopCat.of B)
    (y : M) (b : B) (hy : p y = b) (U : Opens B) :
    Function.Surjective ((evaluationAt I p y b hy).hom.app (op U)) := by
  classical
  intro t
  by_cases hb : b ∈ U
  · let e := skyscraperSectionIso (X := TopCat.of B) b (AddCommGrpCat.of ℂ) U hb
    let c : ℂ := e.hom t
    let s : HolomorphicFunctionSheaf.Section I M ((Opens.map p).obj U) :=
      ⟨fun _ => c, contMDiff_const⟩
    refine ⟨s, ?_⟩
    apply e.addCommGroupIsoToAddEquiv.injective
    exact evaluationAt_app I p y b hy U hb s
  · refine ⟨0, ?_⟩
    apply AddCommGrpCat.asHom_injective
    exact (skyscraperSectionIsTerminal (X := TopCat.of B)
      b (AddCommGrpCat.of ℂ) U hb).hom_ext _ _

/-- Evaluation at an arbitrary source point is surjective on every
actual section component. -/
theorem evaluation_app_surjective (p : TopCat.of M ⟶ TopCat.of B)
    (y : M) (U : Opens B) :
    Function.Surjective ((evaluation I p y).hom.app (op U)) :=
  evaluationAt_app_surjective I p y (p y) rfl U

/-- The actual evaluation morphism is an epimorphism of sheaves,
proved from surjectivity of all its actual section components. -/
instance evaluationAt_epi (p : TopCat.of M ⟶ TopCat.of B)
    (y : M) (b : B) (hy : p y = b) : Epi (evaluationAt I p y b hy) := by
  let : ∀ U : (Opens (TopCat.of B))ᵒᵖ,
      Epi ((evaluationAt I p y b hy).hom.app U) := fun U =>
    ConcreteCategory.epi_of_surjective _
      (evaluationAt_app_surjective I p y b hy U.unop)
  let : Epi (evaluationAt I p y b hy).hom := NatTrans.epi_of_epi_app _
  exact CategoryTheory.Sheaf.Hom.epi_of_presheaf_epi
    (Opens.grothendieckTopology (TopCat.of B)) AddCommGrpCat (evaluationAt I p y b hy)

/-- The default evaluation at the image of the source point is also an
epimorphism of the actual sheaves. -/
instance evaluation_epi (p : TopCat.of M ⟶ TopCat.of B) (y : M) :
    Epi (evaluation I p y) :=
  evaluationAt_epi I p y (p y) rfl

end Wikipedia.HopfProblem.CuspNormalization.SheafEvaluation
