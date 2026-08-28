import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsEvaluationBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafEvaluationSheaf

/-!
# Actual constant-sheaf evaluation to a scalar skyscraper

The independently defined scalar stalk map gives a genuine sheaf
morphism through Mathlib's skyscraper adjunction.  Its section and
stalk formulas refer to the actual constant-sheaf germs and to the
same actual skyscraper targets as holomorphic evaluation.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.CuspNormalization.SheafConstants

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]

/-- Evaluation of the actual constant pushforward at a selected point
of a specified fibre, with the genuine scalar skyscraper as target. -/
def constantEvaluationAt (p : TopCat.of M ⟶ TopCat.of B)
    (y : M) (b : B) (hy : p y = b) :
    pushedConstantSheaf p ⟶ SheafEvaluation.scalarSkyscraper b :=
  SheafEvaluation.toSkyscraper (pushedConstantSheaf p) b (AddCommGrpCat.of ℂ)
    (constantStalkEvaluationAtHom p y b hy)

/-- Evaluation at an arbitrary actual source point. -/
def constantEvaluation (p : TopCat.of M ⟶ TopCat.of B) (y : M) :
    pushedConstantSheaf p ⟶ SheafEvaluation.scalarSkyscraper (p y) :=
  constantEvaluationAt p y (p y) rfl

/-- On a neighbourhood of the support, evaluation is the actual section
germ followed by the independently constructed scalar stalk map. -/
theorem constantEvaluationAt_app_hom (p : TopCat.of M ⟶ TopCat.of B)
    (y : M) (b : B) (hy : p y = b) (U : Opens B) (hb : b ∈ U) :
    (constantEvaluationAt p y b hy).hom.app (op U) ≫
        (SheafEvaluation.skyscraperSectionIso (X := TopCat.of B)
          b (AddCommGrpCat.of ℂ) U hb).hom =
      (pushedConstantSheaf p).presheaf.germ U b hb ≫
        constantStalkEvaluationAtHom p y b hy :=
  SheafEvaluation.toSkyscraper_app (pushedConstantSheaf p) b (AddCommGrpCat.of ℂ)
    (constantStalkEvaluationAtHom p y b hy) U hb

/-- The actual component computes the value of the actual source germ. -/
@[simp] theorem constantEvaluationAt_app (p : TopCat.of M ⟶ TopCat.of B)
    (y : M) (b : B) (hy : p y = b) (U : Opens B) (hb : b ∈ U)
    (s : (complexAdditiveSheaf (TopCat.of M)).obj.obj (op ((Opens.map p).obj U))) :
    (SheafEvaluation.skyscraperSectionIso (X := TopCat.of B)
        b (AddCommGrpCat.of ℂ) U hb).hom
        ((constantEvaluationAt p y b hy).hom.app (op U) s) =
      complexAdditiveSheafStalkEquiv (TopCat.of M) y
        (TopCat.Presheaf.germ (complexAdditiveSheaf (TopCat.of M)).obj
          ((Opens.map p).obj U) y (SheafEvaluation.point_mem_preimage p y b hy U hb) s) :=
  (congrArg (fun k : (pushedConstantSheaf p).presheaf.obj (op U) ⟶
    AddCommGrpCat.of ℂ => k s) (constantEvaluationAt_app_hom p y b hy U hb)).trans
      (constantStalkEvaluationAt_germ p y b hy U hb s)

/-- On an actual constant representative, the component has that exact
scalar value under the canonical skyscraper-section identification. -/
@[simp] theorem constantEvaluationAt_app_unit (p : TopCat.of M ⟶ TopCat.of B)
    (y : M) (b : B) (hy : p y = b) (U : Opens B) (hb : b ∈ U) (c : ℂ) :
    (SheafEvaluation.skyscraperSectionIso (X := TopCat.of B)
        b (AddCommGrpCat.of ℂ) U hb).hom
        ((constantEvaluationAt p y b hy).hom.app (op U)
          ((additiveUnit (TopCat.of M)).app (op ((Opens.map p).obj U)) c)) = c :=
  (constantEvaluationAt_app p y b hy U hb _).trans
    (complexAdditiveSheafStalkEquiv_germ_unit (TopCat.of M) y
      ((Opens.map p).obj U) (SheafEvaluation.point_mem_preimage p y b hy U hb) c)

/-- On the actual categorical stalk, the sheaf evaluation recovers its
defining scalar stalk homomorphism. -/
theorem constantEvaluationAt_stalk_hom (p : TopCat.of M ⟶ TopCat.of B)
    (y : M) (b : B) (hy : p y = b) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of B) b).map
        (constantEvaluationAt p y b hy).hom ≫
          (SheafEvaluation.skyscraperStalkIso (X := TopCat.of B)
            b (AddCommGrpCat.of ℂ)).hom =
      constantStalkEvaluationAtHom p y b hy :=
  SheafEvaluation.toSkyscraper_stalk (pushedConstantSheaf p) b (AddCommGrpCat.of ℂ)
    (constantStalkEvaluationAtHom p y b hy)

@[simp] theorem constantEvaluationAt_stalk (p : TopCat.of M ⟶ TopCat.of B)
    (y : M) (b : B) (hy : p y = b)
    (s : (pushedConstantSheaf p).presheaf.stalk b) :
    (SheafEvaluation.skyscraperStalkIso (X := TopCat.of B) b (AddCommGrpCat.of ℂ)).hom
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of B) b).map
          (constantEvaluationAt p y b hy).hom s) = constantStalkEvaluationAt p y b hy s :=
  congrArg (fun k : (pushedConstantSheaf p).presheaf.stalk b ⟶
    AddCommGrpCat.of ℂ => k s) (constantEvaluationAt_stalk_hom p y b hy)

end Wikipedia.HopfProblem.CuspNormalization.SheafConstants
