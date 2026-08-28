import Wikipedia.HopfProblem.CuspNormalizationSheafEvaluationSheaf
import Wikipedia.HopfProblem.CuspNormalizationSheafEvaluationSurjective
import Wikipedia.HopfProblem.CuspNormalizationSheafEvaluationStalkNaturality

/-!
# Actual evaluation morphisms in the normalization sheaf sequence

These are genuine morphisms from pushed-forward holomorphic-function
sheaves to Mathlib's actual scalar skyscraper sheaf. The component and
stalk computations use literal function evaluation. Their naturality
under actual holomorphic pullback over the base is proved here from the
actual skyscraper adjunction and the actual stalk computation.
-/

noncomputable section

open TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafEvaluation

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace G] (J : ModelWithCorners ℂ F G)
  {N : Type} [TopologicalSpace N] [ChartedSpace G N]
  {B : Type} [TopologicalSpace B]

/-- Actual scalar evaluation is natural under every actual holomorphic
map over the base. Both sides are genuine sheaf morphisms to the same
specified scalar skyscraper. -/
theorem evaluationAt_naturality
    (p : TopCat.of M ⟶ TopCat.of B) (q : TopCat.of N ⟶ TopCat.of B)
    (g : ContMDiffMap J I N M ω) (hg : ∀ x : N, p (g x) = q x)
    (y : N) (b : B) (hy : q y = b) :
    SheafOverBase.additivePullback I J p q g hg ≫ evaluationAt J q y b hy =
      evaluationAt I p (g y) b ((hg y).trans hy) := by
  exact (toSkyscraper_naturality (SheafOverBase.additivePullback I J p q g hg)
    b (AddCommGrpCat.of ℂ) (stalkEvaluationAtHom J q y b hy)).trans
    (congrArg (toSkyscraper (pushedHolomorphicSheaf I p) b (AddCommGrpCat.of ℂ))
      (stalkEvaluationAt_naturality_hom I J p q g hg y b hy))

/-- Evaluation at a source point after pullback is evaluation at its
actual image, with the common skyscraper support specified by the
proved equality over the base. -/
theorem evaluation_naturality
    (p : TopCat.of M ⟶ TopCat.of B) (q : TopCat.of N ⟶ TopCat.of B)
    (g : ContMDiffMap J I N M ω) (hg : ∀ x : N, p (g x) = q x) (y : N) :
    SheafOverBase.additivePullback I J p q g hg ≫ evaluation J q y =
      evaluationAt I p (g y) (q y) (hg y) :=
  evaluationAt_naturality I J p q g hg y (q y) rfl

end Wikipedia.HopfProblem.CuspNormalization.SheafEvaluation
