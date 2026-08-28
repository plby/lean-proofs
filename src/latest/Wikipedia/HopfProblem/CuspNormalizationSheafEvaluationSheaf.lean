import Wikipedia.HopfProblem.CuspNormalizationSheafEvaluationBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafEvaluationSkyscraper

/-!
# The genuine sheaf evaluation morphism to a scalar skyscraper

For every continuous base map and every chosen point, actual holomorphic
functions on base-open inverse images evaluate at that point. The stalk
construction and Mathlib's skyscraper adjunction make these evaluations
one genuine morphism of additive sheaves. Its actual section and stalk
maps are computed here.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafEvaluation

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  {B : Type} [TopologicalSpace B]

/-- Mathlib's genuine skyscraper sheaf with complex coefficients. -/
abbrev scalarSkyscraper (b : B) : TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of B) :=
  skyscraper (X := TopCat.of B) b (AddCommGrpCat.of ℂ)

/-- Evaluation at a chosen point of a specified fibre, as an actual
morphism from the pushforward holomorphic-function sheaf to the actual
scalar skyscraper at the base point. -/
def evaluationAt (p : TopCat.of M ⟶ TopCat.of B)
    (y : M) (b : B) (hy : p y = b) :
    pushedHolomorphicSheaf I p ⟶ scalarSkyscraper b :=
  toSkyscraper (pushedHolomorphicSheaf I p) b (AddCommGrpCat.of ℂ)
    (stalkEvaluationAtHom I p y b hy)

/-- The evaluation morphism at an arbitrary actual source point. -/
def evaluation (p : TopCat.of M ⟶ TopCat.of B) (y : M) :
    pushedHolomorphicSheaf I p ⟶ scalarSkyscraper (p y) :=
  evaluationAt I p y (p y) rfl

/-- On an open neighbourhood of the support, the actual component is
the actual section-germ map followed by scalar stalk evaluation. -/
theorem evaluationAt_app_hom (p : TopCat.of M ⟶ TopCat.of B)
    (y : M) (b : B) (hy : p y = b) (U : Opens B) (hb : b ∈ U) :
    (evaluationAt I p y b hy).hom.app (op U) ≫
        (skyscraperSectionIso (X := TopCat.of B) b (AddCommGrpCat.of ℂ) U hb).hom =
      (pushedHolomorphicSheaf I p).presheaf.germ U b hb ≫
        stalkEvaluationAtHom I p y b hy :=
  toSkyscraper_app (pushedHolomorphicSheaf I p) b (AddCommGrpCat.of ℂ)
    (stalkEvaluationAtHom I p y b hy) U hb

/-- After the canonical skyscraper-section identification, the actual
component is precisely literal evaluation of the actual function. -/
@[simp] theorem evaluationAt_app (p : TopCat.of M ⟶ TopCat.of B)
    (y : M) (b : B) (hy : p y = b) (U : Opens B) (hb : b ∈ U)
    (s : HolomorphicFunctionSheaf.Section I M ((Opens.map p).obj U)) :
    (skyscraperSectionIso (X := TopCat.of B) b (AddCommGrpCat.of ℂ) U hb).hom
        ((evaluationAt I p y b hy).hom.app (op U) s) =
      s ⟨y, point_mem_preimage p y b hy U hb⟩ := by
  exact (congrArg (fun k : (pushedHolomorphicSheaf I p).presheaf.obj (op U) ⟶
    AddCommGrpCat.of ℂ => k s) (evaluationAt_app_hom I p y b hy U hb)).trans
    (stalkEvaluationAt_germ I p y b hy U hb s)

/-- In particular the evaluation at `y` is literal evaluation on every
base open containing `p y`. -/
@[simp] theorem evaluation_app (p : TopCat.of M ⟶ TopCat.of B)
    (y : M) (U : Opens B) (hy : p y ∈ U)
    (s : HolomorphicFunctionSheaf.Section I M ((Opens.map p).obj U)) :
    (skyscraperSectionIso (X := TopCat.of B) (p y) (AddCommGrpCat.of ℂ) U hy).hom
        ((evaluation I p y).hom.app (op U) s) = s ⟨y, hy⟩ :=
  evaluationAt_app I p y (p y) rfl U hy s

/-- The actual categorical stalk map, after the canonical skyscraper
stalk isomorphism, is the actual scalar evaluation homomorphism. -/
theorem evaluationAt_stalk_hom (p : TopCat.of M ⟶ TopCat.of B)
    (y : M) (b : B) (hy : p y = b) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of B) b).map
        (evaluationAt I p y b hy).hom ≫
          (skyscraperStalkIso (X := TopCat.of B) b (AddCommGrpCat.of ℂ)).hom =
      stalkEvaluationAtHom I p y b hy :=
  toSkyscraper_stalk (pushedHolomorphicSheaf I p) b (AddCommGrpCat.of ℂ)
    (stalkEvaluationAtHom I p y b hy)

/-- The same actual stalk computation on arbitrary stalk elements. -/
@[simp] theorem evaluationAt_stalk (p : TopCat.of M ⟶ TopCat.of B)
    (y : M) (b : B) (hy : p y = b)
    (s : (pushedHolomorphicSheaf I p).presheaf.stalk b) :
    (skyscraperStalkIso (X := TopCat.of B) b (AddCommGrpCat.of ℂ)).hom
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of B) b).map
          (evaluationAt I p y b hy).hom s) = stalkEvaluationAt I p y b hy s :=
  congrArg (fun k : (pushedHolomorphicSheaf I p).presheaf.stalk b ⟶
    AddCommGrpCat.of ℂ => k s) (evaluationAt_stalk_hom I p y b hy)

/-- The actual evaluation sheaf morphism is surjective on the stalk at
its support, because actual constant sections realize every scalar. -/
theorem evaluationAt_stalk_surjective (p : TopCat.of M ⟶ TopCat.of B)
    (y : M) (b : B) (hy : p y = b) :
    Function.Surjective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of B) b).map
        (evaluationAt I p y b hy).hom) := by
  intro t
  obtain ⟨s, hs⟩ := stalkEvaluationAt_surjective I p y b hy
    ((skyscraperStalkIso (X := TopCat.of B) b (AddCommGrpCat.of ℂ)).hom t)
  refine ⟨s, ?_⟩
  apply (skyscraperStalkIso (X := TopCat.of B) b
    (AddCommGrpCat.of ℂ)).addCommGroupIsoToAddEquiv.injective
  exact (evaluationAt_stalk I p y b hy s).trans hs

end Wikipedia.HopfProblem.CuspNormalization.SheafEvaluation
