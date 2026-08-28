import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsResolutionStalkRetraction
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsEvaluationSheaf
import Wikipedia.HopfProblem.CuspNormalizationSheafTripleStalkSkyscraper

/-!
# Scalar-evaluation retractions preserve actual endpoint maps

At the support point of a scalar skyscraper, the retraction preserves
the defining fibre evaluation by construction. At every other point of
a `T1` base, the actual skyscraper stalk is zero. Thus the actual stalk
retractions commute with the genuine single-point evaluation morphisms
at every base point, not only at their support.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafConstants

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {B : Type} [TopologicalSpace B] [T1Space B]

/-- The actual constant stalk retraction preserves evaluation to an
actual scalar skyscraper, at every point of the base. -/
theorem holomorphicStalkConstantRetraction_evaluationAt
    (p : TopCat.of M ⟶ TopCat.of B) (hp : IsClosedMap p)
    (x : B) (hfinite : (p ⁻¹' {x}).Finite) (y : M) (b : B) (hy : p y = b) :
    holomorphicStalkConstantRetractionHom I p hp x hfinite ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of B) x).map
          (constantEvaluationAt p y b hy).hom =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of B) x).map
        (SheafEvaluation.evaluationAt I p y b hy).hom := by
  by_cases hx : x = b
  · subst x
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    apply (SheafEvaluation.skyscraperStalkIso (X := TopCat.of B)
      b (AddCommGrpCat.of ℂ)).addCommGroupIsoToAddEquiv.injective
    exact (constantEvaluationAt_stalk p y b hy
      (holomorphicStalkConstantRetraction I p hp b hfinite s)).trans
        ((holomorphicStalkConstantRetraction_eval I p hp b hfinite s y hy).trans
          (SheafEvaluation.evaluationAt_stalk I p y b hy s).symm)
  · exact (SheafTripleStalk.skyscraper_stalk_isZero_of_ne
      (X := TopCat.of B) b x (AddCommGrpCat.of ℂ) hx).eq_of_tgt _ _

end Wikipedia.HopfProblem.CuspNormalization.SheafConstants
