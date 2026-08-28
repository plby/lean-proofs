import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsEvaluationNaturalityBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsEvaluationSheaf

/-!
# Actual constant-sheaf evaluation is natural over the base

The independently defined constant-sheaf evaluation maps commute with
the actual over-base constant-sheaf pullback.  The proof passes the
proved equality of actual scalar stalk maps through Mathlib's genuine
skyscraper adjunction.  The map between the source spaces is only
assumed continuous, not holomorphic.
-/

noncomputable section

open TopologicalSpace CategoryTheory

namespace Wikipedia.HopfProblem.CuspNormalization.SheafConstants

variable {M N B : Type} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace B]

/-- Evaluation after actual constant-sheaf pullback is evaluation at
the image point, as an equality of actual sheaf morphisms to the same
specified scalar skyscraper. -/
theorem constantEvaluationAt_naturality
    (p : TopCat.of M ⟶ TopCat.of B) (q : TopCat.of N ⟶ TopCat.of B)
    (f : TopCat.of N ⟶ TopCat.of M) (hf : ∀ x : N, p (f x) = q x)
    (y : N) (b : B) (hy : q y = b) :
    additiveOverBaseMap p q f hf ≫ constantEvaluationAt q y b hy =
      constantEvaluationAt p (f y) b ((hf y).trans hy) := by
  exact (SheafEvaluation.toSkyscraper_naturality (additiveOverBaseMap p q f hf)
    b (AddCommGrpCat.of ℂ) (constantStalkEvaluationAtHom q y b hy)).trans
      (congrArg (SheafEvaluation.toSkyscraper (pushedConstantSheaf p)
        b (AddCommGrpCat.of ℂ))
        (constantStalkEvaluationAt_naturality_hom p q f hf y b hy))

/-- The support-specialized form at the actual image of the source point. -/
theorem constantEvaluation_naturality
    (p : TopCat.of M ⟶ TopCat.of B) (q : TopCat.of N ⟶ TopCat.of B)
    (f : TopCat.of N ⟶ TopCat.of M) (hf : ∀ x : N, p (f x) = q x) (y : N) :
    additiveOverBaseMap p q f hf ≫ constantEvaluation q y =
      constantEvaluationAt p (f y) (q y) (hf y) :=
  constantEvaluationAt_naturality p q f hf y (q y) rfl

end Wikipedia.HopfProblem.CuspNormalization.SheafConstants
