import Wikipedia.HopfProblem.CuspNormalizationSheafEvaluationBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafOverBase

/-!
# Scalar stalk evaluation commutes with actual holomorphic pullback

For a holomorphic map over the same topological base, evaluation of the
pulled-back actual function at a source point is evaluation of the
original actual function at its image. The statement here concerns the
actual categorical pushforward stalk maps, not just section functions.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafEvaluation

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace G] (J : ModelWithCorners ℂ F G)
  {N : Type} [TopologicalSpace N] [ChartedSpace G N]
  {B : Type} [TopologicalSpace B]

/-- Scalar evaluation commutes with the actual stalk map of a
holomorphic pullback over the fixed base. -/
theorem stalkEvaluationAt_naturality
    (p : TopCat.of M ⟶ TopCat.of B) (q : TopCat.of N ⟶ TopCat.of B)
    (g : ContMDiffMap J I N M ω) (hg : ∀ x : N, p (g x) = q x)
    (y : N) (b : B) (hy : q y = b)
    (s : (pushedHolomorphicSheaf I p).presheaf.stalk b) :
    stalkEvaluationAt J q y b hy
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of B) b).map
          (SheafOverBase.additivePullback I J p q g hg).hom s) =
      stalkEvaluationAt I p (g y) b ((hg y).trans hy) s := by
  obtain ⟨U, hbU, u, rfl⟩ := (pushedHolomorphicSheaf I p).presheaf.exists_germ_eq s
  change HolomorphicFunctionSheaf.Section I M ((Opens.map p).obj U) at u
  calc
    stalkEvaluationAt J q y b hy
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of B) b).map
          (SheafOverBase.additivePullback I J p q g hg).hom
          ((pushedHolomorphicSheaf I p).presheaf.germ U b hbU u)) =
        stalkEvaluationAt J q y b hy
          ((pushedHolomorphicSheaf J q).presheaf.germ U b hbU
            ((SheafOverBase.additivePullback I J p q g hg).hom.app (op U) u)) :=
      congrArg (stalkEvaluationAt J q y b hy)
        (TopCat.Presheaf.stalkFunctor_map_germ_apply U b hbU
          (SheafOverBase.additivePullback I J p q g hg).hom u)
    _ = SheafOverBase.sectionPullback I J p q g hg U u
        ⟨y, point_mem_preimage q y b hy U hbU⟩ :=
      stalkEvaluationAt_germ J q y b hy U hbU
        (SheafOverBase.sectionPullback I J p q g hg U u)
    _ = u ⟨g y, point_mem_preimage p (g y) b ((hg y).trans hy) U hbU⟩ := rfl
    _ = stalkEvaluationAt I p (g y) b ((hg y).trans hy)
        ((pushedHolomorphicSheaf I p).presheaf.germ U b hbU u) :=
      (stalkEvaluationAt_germ I p (g y) b ((hg y).trans hy) U hbU u).symm

/-- The same compatibility as an equality of actual additive-group
morphisms, for direct use in the skyscraper adjunction. -/
theorem stalkEvaluationAt_naturality_hom
    (p : TopCat.of M ⟶ TopCat.of B) (q : TopCat.of N ⟶ TopCat.of B)
    (g : ContMDiffMap J I N M ω) (hg : ∀ x : N, p (g x) = q x)
    (y : N) (b : B) (hy : q y = b) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of B) b).map
        (SheafOverBase.additivePullback I J p q g hg).hom ≫
          stalkEvaluationAtHom J q y b hy =
      stalkEvaluationAtHom I p (g y) b ((hg y).trans hy) := by
  ext s
  exact stalkEvaluationAt_naturality I J p q g hg y b hy s

end Wikipedia.HopfProblem.CuspNormalization.SheafEvaluation
