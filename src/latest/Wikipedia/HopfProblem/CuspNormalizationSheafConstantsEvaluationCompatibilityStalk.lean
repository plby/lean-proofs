import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsAdditiveMaps
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsEvaluationBasic

/-!
# Compatibility of independently constructed constant and holomorphic evaluations

The actual constant stalk is identified with `ℂ` by the proved
constant-sheaf stalk isomorphism.  Evaluation after the actual inclusion
into holomorphic functions agrees with that independent identification.
Taking actual pushforward section germs then gives the compatibility
at a chosen point over any topological base.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafConstants

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  {M : Type} [TopologicalSpace M] [ChartedSpace H M]

/-- Evaluation after the actual constant-to-holomorphic stalk map is
the independently constructed constant-stalk identification. -/
theorem holomorphicStalkEval_holomorphicAdditiveMap (y : M)
    (s : TopCat.Presheaf.stalk (C := AddCommGrpCat)
      (complexAdditiveSheaf (TopCat.of M)).obj y) :
    SheafEvaluation.holomorphicStalkEval I y
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
          (holomorphicAdditiveMap I M).hom s) =
      complexAdditiveSheafStalkEquiv (TopCat.of M) y s := by
  obtain ⟨c, rfl⟩ := (complexAdditiveSheafStalkEquiv (TopCat.of M) y).symm.surjective s
  have hy : y ∈ (⊤ : Opens M) := by trivial
  let f : HolomorphicFunctionSheaf.Section I M ⊤ :=
    (holomorphicAdditiveMap I M).hom.app (op ⊤)
      ((additiveUnit (TopCat.of M)).app (op ⊤) c)
  calc
    _ = SheafEvaluation.holomorphicStalkEval I y
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
          (holomorphicAdditiveMap I M).hom
          (TopCat.Presheaf.germ (complexAdditiveSheaf (TopCat.of M)).obj ⊤ y hy
            ((additiveUnit (TopCat.of M)).app (op ⊤) c))) :=
      congrArg (fun t => SheafEvaluation.holomorphicStalkEval I y
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
          (holomorphicAdditiveMap I M).hom t))
        (complexAdditiveSheafStalkEquiv_symm_eq_germ_unit (TopCat.of M) y ⊤ hy c)
    _ = SheafEvaluation.holomorphicStalkEval I y
        ((HolomorphicFunctionSheaf.additiveSheaf I M).presheaf.germ ⊤ y hy f) :=
      congrArg (SheafEvaluation.holomorphicStalkEval I y)
        (TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ y hy
          (holomorphicAdditiveMap I M).hom ((additiveUnit (TopCat.of M)).app (op ⊤) c))
    _ = f ⟨y, hy⟩ := SheafEvaluation.holomorphicStalkEval_germ I ⊤ y hy f
    _ = c := holomorphicAdditiveMap_unit I M ⊤ c ⟨y, hy⟩
    _ = _ := ((complexAdditiveSheafStalkEquiv (TopCat.of M) y).apply_symm_apply c).symm

/-- On each actual local section, the holomorphic image's value agrees
with the independent value of its actual constant-sheaf germ. -/
theorem holomorphicAdditiveMap_germ_evaluation (U : Opens M) (y : M) (hy : y ∈ U)
    (s : (complexAdditiveSheaf (TopCat.of M)).obj.obj (op U)) :
    (fun f : HolomorphicFunctionSheaf.Section I M U => f ⟨y, hy⟩)
        ((holomorphicAdditiveMap I M).hom.app (op U) s) =
      complexAdditiveSheafStalkEquiv (TopCat.of M) y
        (TopCat.Presheaf.germ (complexAdditiveSheaf (TopCat.of M)).obj U y hy s) := by
  let f : HolomorphicFunctionSheaf.Section I M U :=
    (holomorphicAdditiveMap I M).hom.app (op U) s
  exact (SheafEvaluation.holomorphicStalkEval_germ I U y hy f).symm.trans
    ((congrArg (SheafEvaluation.holomorphicStalkEval I y)
      (TopCat.Presheaf.stalkFunctor_map_germ_apply U y hy
        (holomorphicAdditiveMap I M).hom s)).symm.trans
      (holomorphicStalkEval_holomorphicAdditiveMap I y
        (TopCat.Presheaf.germ (complexAdditiveSheaf (TopCat.of M)).obj U y hy s)))

variable {B : Type} [TopologicalSpace B]

/-- The actual pushed constant inclusion commutes with the independently
defined evaluations on the genuine pushforward stalks. -/
theorem stalkEvaluationAt_holomorphicAdditiveMap (p : TopCat.of M ⟶ TopCat.of B)
    (y : M) (b : B) (hy : p y = b) (s : (pushedConstantSheaf p).presheaf.stalk b) :
    SheafEvaluation.stalkEvaluationAt I p y b hy
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat b).map
          ((TopCat.Sheaf.pushforward AddCommGrpCat p).map
            (holomorphicAdditiveMap I M)).hom s) =
      constantStalkEvaluationAt p y b hy s := by
  obtain ⟨U, hbU, u, rfl⟩ := (pushedConstantSheaf p).presheaf.exists_germ_eq s
  let α := (TopCat.Sheaf.pushforward AddCommGrpCat p).map (holomorphicAdditiveMap I M)
  let f : HolomorphicFunctionSheaf.Section I M ((Opens.map p).obj U) :=
    (holomorphicAdditiveMap I M).hom.app (op ((Opens.map p).obj U)) u
  calc
    _ = SheafEvaluation.stalkEvaluationAt I p y b hy
        ((SheafEvaluation.pushedHolomorphicSheaf I p).presheaf.germ U b hbU f) :=
      congrArg (SheafEvaluation.stalkEvaluationAt I p y b hy)
        (TopCat.Presheaf.stalkFunctor_map_germ_apply U b hbU α.hom u)
    _ = f ⟨y, SheafEvaluation.point_mem_preimage p y b hy U hbU⟩ :=
      SheafEvaluation.stalkEvaluationAt_germ I p y b hy U hbU f
    _ = complexAdditiveSheafStalkEquiv (TopCat.of M) y
        (TopCat.Presheaf.germ (complexAdditiveSheaf (TopCat.of M)).obj
          ((Opens.map p).obj U) y (SheafEvaluation.point_mem_preimage p y b hy U hbU) u) :=
      holomorphicAdditiveMap_germ_evaluation I ((Opens.map p).obj U) y
        (SheafEvaluation.point_mem_preimage p y b hy U hbU) u
    _ = _ := (constantStalkEvaluationAt_germ p y b hy U hbU u).symm

/-- The same compatibility as an equality of actual additive morphisms. -/
theorem stalkEvaluationAt_holomorphicAdditiveMap_hom (p : TopCat.of M ⟶ TopCat.of B)
    (y : M) (b : B) (hy : p y = b) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat b).map
        ((TopCat.Sheaf.pushforward AddCommGrpCat p).map
          (holomorphicAdditiveMap I M)).hom ≫
      SheafEvaluation.stalkEvaluationAtHom I p y b hy =
        constantStalkEvaluationAtHom p y b hy := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  exact stalkEvaluationAt_holomorphicAdditiveMap I p y b hy s

end Wikipedia.HopfProblem.CuspNormalization.SheafConstants
