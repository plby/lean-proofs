import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsResolutionReducedRetraction
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsResolutionStalkRetraction
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsEvaluationNaturalityBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafPullback

/-!
# Actual pullback compatibility of the reduced-stalk retraction

Literal composition of functions preserves the independent scalar
evaluation on reduced stalks.  For a closed map with finite fibre and
Hausdorff source, the resulting equality at all actual fibre points
proves the first-arrow square between the genuine stalk retractions.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafConstants

section ConstantPullback

variable {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q]

/-- Actual constant pullback preserves the scalar value on genuine
stalks, with a named target point and no finiteness hypothesis. -/
theorem constantStalkEvaluationAt_additivePullbackMap
    (p : TopCat.of P ⟶ TopCat.of Q) (y : P) (x : Q) (hy : p y = x)
    (s : (complexAdditiveSheaf (TopCat.of Q)).presheaf.stalk x) :
    constantStalkEvaluationAt p y x hy
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of Q) x).map
          (additivePullbackMap p).hom s) =
      complexAdditiveSheafStalkEquiv (TopCat.of Q) x s := by
  subst x
  obtain ⟨U, hxU, u, rfl⟩ :=
    (complexAdditiveSheaf (TopCat.of Q)).presheaf.exists_germ_eq s
  calc
    _ = constantStalkEvaluationAt p y (p y) rfl
        ((pushedConstantSheaf p).presheaf.germ U (p y) hxU
          ((additivePullbackMap p).hom.app (op U) u)) :=
      congrArg (constantStalkEvaluationAt p y (p y) rfl)
        (TopCat.Presheaf.stalkFunctor_map_germ_apply U (p y) hxU
          (additivePullbackMap p).hom u)
    _ = complexAdditiveSheafStalkEquiv (TopCat.of P) y
        (TopCat.Presheaf.germ (complexAdditiveSheaf (TopCat.of P)).obj
          ((Opens.map p).obj U) y hxU ((additivePullbackMap p).hom.app (op U) u)) :=
      constantStalkEvaluationAt_germ p y (p y) rfl U hxU _
    _ = _ := constantGermValue_pullback p U y hxU u

end ConstantPullback

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℂ E H)
  {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace G] {N : Type} [TopologicalSpace N] [ChartedSpace G N]
  (J : ModelWithCorners ℂ F G) (S : Set M)
  (g : ContMDiffMap J I N M ω) (hg : ∀ y : N, g y ∈ S)

/-- Actual reduced-function pullback preserves literal scalar stalk
evaluation at every source point, without any chart comparison. -/
theorem reducedStalkEval_pullback (y : N) (x : S)
    (hy : SheafPullback.topMap I J S g hg y = x)
    (s : (SheafReduced.additiveSheaf I S).presheaf.stalk x) :
    SheafEvaluation.stalkEvaluationAt J (SheafPullback.topMap I J S g hg) y x hy
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of S) x).map
          (SheafPullback.additivePullback I J S g hg).hom s) =
      reducedStalkEval I S x s := by
  obtain ⟨U, hxU, u, rfl⟩ := (SheafReduced.additiveSheaf I S).presheaf.exists_germ_eq s
  change SheafReduced.Section I S U at u
  let p := SheafPullback.topMap I J S g hg
  let f := SheafPullback.pullbackSection I J S g hg U u
  calc
    _ = SheafEvaluation.stalkEvaluationAt J p y x hy
        ((SheafEvaluation.pushedHolomorphicSheaf J p).presheaf.germ U x hxU f) :=
      congrArg (SheafEvaluation.stalkEvaluationAt J p y x hy)
        (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
          (SheafPullback.additivePullback I J S g hg).hom u)
    _ = f ⟨y, SheafEvaluation.point_mem_preimage p y x hy U hxU⟩ :=
      SheafEvaluation.stalkEvaluationAt_germ J p y x hy U hxU f
    _ = u ⟨x, hxU⟩ := congrArg (fun z : U => u z) (Subtype.ext hy)
    _ = _ := (reducedStalkEval_germ I S U x hxU u).symm

/-- The same scalar compatibility as an equality of actual additive
stalk morphisms. -/
theorem reducedStalkEval_pullback_hom (y : N) (x : S)
    (hy : SheafPullback.topMap I J S g hg y = x) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of S) x).map
        (SheafPullback.additivePullback I J S g hg).hom ≫
      SheafEvaluation.stalkEvaluationAtHom J (SheafPullback.topMap I J S g hg) y x hy =
        reducedStalkEvalHom I S x := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  exact reducedStalkEval_pullback I J S g hg y x hy s

section FiniteFibre

variable [T2Space N]

/-- The first-arrow square of genuine stalk retractions commutes for
the actual reduced-function pullback and actual constant pullback. -/
theorem reducedStalkConstantRetraction_pullback
    (hp : IsClosedMap (SheafPullback.topMap I J S g hg)) (x : S)
    (hfinite : ((SheafPullback.topMap I J S g hg) ⁻¹' {x}).Finite)
    (s : (SheafReduced.additiveSheaf I S).presheaf.stalk x) :
    holomorphicStalkConstantRetraction J (SheafPullback.topMap I J S g hg) hp x hfinite
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of S) x).map
          (SheafPullback.additivePullback I J S g hg).hom s) =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of S) x).map
        (additivePullbackMap (SheafPullback.topMap I J S g hg)).hom
        (reducedStalkConstantRetraction I S x s) := by
  let p := SheafPullback.topMap I J S g hg
  apply (constantFibreValueEquiv p hp x hfinite).injective
  funext y
  calc
    _ = SheafEvaluation.stalkEvaluationAt J p y.val x y.property
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of S) x).map
          (SheafPullback.additivePullback I J S g hg).hom s) :=
      holomorphicStalkConstantRetraction_component J p hp x hfinite _ y
    _ = reducedStalkEval I S x s :=
      reducedStalkEval_pullback I J S g hg y.val x y.property s
    _ = complexAdditiveSheafStalkEquiv (TopCat.of S) x
        (reducedStalkConstantRetraction I S x s) :=
      (reducedStalkConstantRetraction_eval I S x s).symm
    _ = constantStalkEvaluationAt p y.val x y.property
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of S) x).map
          (additivePullbackMap p).hom (reducedStalkConstantRetraction I S x s)) :=
      (constantStalkEvaluationAt_additivePullbackMap p y.val x y.property
        (reducedStalkConstantRetraction I S x s)).symm
    _ = _ := (constantFibreValueEquiv_apply p hp x hfinite _ y).symm

/-- The same first-arrow square as an equality of actual categorical
additive morphisms. -/
theorem reducedStalkConstantRetraction_pullback_hom
    (hp : IsClosedMap (SheafPullback.topMap I J S g hg)) (x : S)
    (hfinite : ((SheafPullback.topMap I J S g hg) ⁻¹' {x}).Finite) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of S) x).map
        (SheafPullback.additivePullback I J S g hg).hom ≫
      holomorphicStalkConstantRetractionHom J (SheafPullback.topMap I J S g hg) hp x hfinite =
        reducedStalkConstantRetractionHom I S x ≫
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of S) x).map
            (additivePullbackMap (SheafPullback.topMap I J S g hg)).hom := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  exact reducedStalkConstantRetraction_pullback I J S g hg hp x hfinite s

end FiniteFibre

end Wikipedia.HopfProblem.CuspNormalization.SheafConstants
