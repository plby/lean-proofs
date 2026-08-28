import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalarResolutionDirectImages
import Wikipedia.HopfProblem.CuspNormalizationSheafPullback
import Wikipedia.HopfProblem.CuspNormalizationSheafOverBase

/-!
# Pointwise scalars commute with the actual pullbacks and evaluations
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyScalarResolution

open SheafEvaluation

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℂ E H)
  {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace G] {N : Type} [TopologicalSpace N] [ChartedSpace G N]
  (J : ModelWithCorners ℂ F G)

/-- Reduced-function pullback commutes with the original pointwise scalar actions. -/
theorem reducedPullback_scalar (S : Set M) (g : ContMDiffMap J I N M ω)
    (hg : ∀ x : N, g x ∈ S) (c : ℂ) :
    reducedScalarEnd I S c ≫ SheafPullback.additivePullback I J S g hg =
      SheafPullback.additivePullback I J S g hg ≫
        pushedScalarEnd J (SheafPullback.topMap I J S g hg) c := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  apply ContMDiffMap.ext
  intro x
  rfl

variable {B : Type} [TopologicalSpace B]

/-- Holomorphic pullback over the actual base commutes with pointwise scalars. -/
theorem overBasePullback_scalar
    (p : TopCat.of M ⟶ TopCat.of B) (q : TopCat.of N ⟶ TopCat.of B)
    (g : ContMDiffMap J I N M ω) (hg : ∀ x : N, p (g x) = q x) (c : ℂ) :
    pushedScalarEnd I p c ≫ SheafOverBase.additivePullback I J p q g hg =
      SheafOverBase.additivePullback I J p q g hg ≫ pushedScalarEnd J q c := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  apply ContMDiffMap.ext
  intro x
  rfl

/-- The actual evaluation map commutes with multiplication on its actual skyscraper target. -/
theorem evaluation_scalar (p : TopCat.of M ⟶ TopCat.of B)
    (y : M) (b : B) (hy : p y = b) (c : ℂ) :
    pushedScalarEnd I p c ≫ evaluationAt I p y b hy =
      evaluationAt I p y b hy ≫ skyscraperScalarEnd (X := TopCat.of B) b c := by
  apply skyscraper_hom_ext
  intro U hb
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  change (skyscraperSectionIso (X := TopCat.of B) b (AddCommGrpCat.of ℂ) U hb).hom
      ((evaluationAt I p y b hy).hom.app (op U)
        ((pushedScalarEnd I p c).hom.app (op U) s)) =
    (skyscraperSectionIso (X := TopCat.of B) b (AddCommGrpCat.of ℂ) U hb).hom
      ((skyscraperScalarEnd (X := TopCat.of B) b c).hom.app (op U)
        ((evaluationAt I p y b hy).hom.app (op U) s))
  let f : HolomorphicFunctionSheaf.Section I M ((Opens.map p).obj U) := s
  have hl := evaluationAt_app I p y b hy U hb (c • f)
  have hr := congrArg (fun z : ℂ => c • z) (evaluationAt_app I p y b hy U hb f)
  exact Eq.trans hl (Eq.trans hr.symm
    (skyscraperScalarEnd_apply (X := TopCat.of B) b c U hb
      ((evaluationAt I p y b hy).hom.app (op U) f)).symm)

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyScalarResolution
