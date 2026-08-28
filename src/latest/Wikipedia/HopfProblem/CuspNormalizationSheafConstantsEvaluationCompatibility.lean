import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsEvaluationCompatibilityStalk
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsEvaluationSheaf

/-!
# The actual constant-to-holomorphic evaluation square

The two independently constructed maps to the genuine scalar skyscraper
agree after the actual inclusion of constant sections into holomorphic
functions.  Equality is checked on the actual neighbourhood components;
the other skyscraper components are terminal.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafConstants

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  {B : Type} [TopologicalSpace B]

/-- The actual constant inclusion and the two independently defined
evaluation morphisms commute with the same scalar-skyscraper target. -/
theorem evaluationAt_holomorphicAdditiveMap (p : TopCat.of M ⟶ TopCat.of B)
    (y : M) (b : B) (hy : p y = b) :
    (TopCat.Sheaf.pushforward AddCommGrpCat p).map (holomorphicAdditiveMap I M) ≫
      SheafEvaluation.evaluationAt I p y b hy = constantEvaluationAt p y b hy := by
  apply SheafEvaluation.skyscraper_hom_ext
  intro U hb
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  let f : HolomorphicFunctionSheaf.Section I M ((Opens.map p).obj U) :=
    (holomorphicAdditiveMap I M).hom.app (op ((Opens.map p).obj U)) s
  exact (SheafEvaluation.evaluationAt_app I p y b hy U hb f).trans
    ((holomorphicAdditiveMap_germ_evaluation I ((Opens.map p).obj U) y
      (SheafEvaluation.point_mem_preimage p y b hy U hb) s).trans
      (constantEvaluationAt_app p y b hy U hb s).symm)

/-- The same commuting square with the actual image point as its support. -/
theorem evaluation_holomorphicAdditiveMap (p : TopCat.of M ⟶ TopCat.of B) (y : M) :
    (TopCat.Sheaf.pushforward AddCommGrpCat p).map (holomorphicAdditiveMap I M) ≫
      SheafEvaluation.evaluation I p y = constantEvaluation p y :=
  evaluationAt_holomorphicAdditiveMap I p y (p y) rfl

end Wikipedia.HopfProblem.CuspNormalization.SheafConstants
