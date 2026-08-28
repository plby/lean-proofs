import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsResolutionReducedRetractionBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsAdditiveMaps

/-!
# A chart-free retraction from reduced-function stalks to constant stalks

The independent colimit evaluation agrees with the genuine constant
stalk value after the actual inclusion into reduced functions.  The
inverse constant-stalk equivalence therefore gives an actual additive
retraction, without any local analytic model or comparison assumption.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafConstants

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℂ E H) (S : Set M)

/-- Evaluation after the actual reduced constant inclusion agrees with
the independently identified scalar value of the constant stalk. -/
theorem reducedStalkEval_reducedAdditiveMap (x : S)
    (s : TopCat.Presheaf.stalk (C := AddCommGrpCat)
      (complexAdditiveSheaf (TopCat.of S)).obj x) :
    reducedStalkEval I S x
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of S) x).map
          (reducedAdditiveMap I S).hom s) =
      complexAdditiveSheafStalkEquiv (TopCat.of S) x s := by
  obtain ⟨c, rfl⟩ := (complexAdditiveSheafStalkEquiv (TopCat.of S) x).symm.surjective s
  have hx : x ∈ (⊤ : Opens S) := by trivial
  let f : SheafReduced.Section I S ⊤ :=
    (reducedAdditiveMap I S).hom.app (op ⊤)
      ((additiveUnit (TopCat.of S)).app (op ⊤) c)
  calc
    _ = reducedStalkEval I S x
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of S) x).map
          (reducedAdditiveMap I S).hom
          (TopCat.Presheaf.germ (complexAdditiveSheaf (TopCat.of S)).obj ⊤ x hx
            ((additiveUnit (TopCat.of S)).app (op ⊤) c))) :=
      congrArg (fun t => reducedStalkEval I S x
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of S) x).map
          (reducedAdditiveMap I S).hom t))
        (complexAdditiveSheafStalkEquiv_symm_eq_germ_unit (TopCat.of S) x ⊤ hx c)
    _ = reducedStalkEval I S x
        ((SheafReduced.additiveSheaf I S).presheaf.germ ⊤ x hx f) :=
      congrArg (reducedStalkEval I S x)
        (TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x hx
          (reducedAdditiveMap I S).hom ((additiveUnit (TopCat.of S)).app (op ⊤) c))
    _ = f ⟨x, hx⟩ := reducedStalkEval_germ I S ⊤ x hx f
    _ = c := reducedAdditiveMap_unit I S ⊤ c ⟨x, hx⟩
    _ = _ := ((complexAdditiveSheafStalkEquiv (TopCat.of S) x).apply_symm_apply c).symm

/-- Independent reduced-stalk evaluation followed by the inverse actual
constant-stalk identification. -/
def reducedStalkConstantRetraction (x : S) :
    (SheafReduced.additiveSheaf I S).presheaf.stalk x →+
      TopCat.Presheaf.stalk (C := AddCommGrpCat) (complexAdditiveSheaf (TopCat.of S)).obj x :=
  (complexAdditiveSheafStalkEquiv (TopCat.of S) x).symm.toAddMonoidHom.comp
    (reducedStalkEval I S x)

/-- The retracted stalk has precisely its original literal scalar value. -/
@[simp] theorem reducedStalkConstantRetraction_eval (x : S)
    (s : (SheafReduced.additiveSheaf I S).presheaf.stalk x) :
    complexAdditiveSheafStalkEquiv (TopCat.of S) x
        (reducedStalkConstantRetraction I S x s) = reducedStalkEval I S x s :=
  (complexAdditiveSheafStalkEquiv (TopCat.of S) x).apply_symm_apply _

/-- On every actual representative the retraction retains its literal value. -/
@[simp] theorem reducedStalkConstantRetraction_germ (U : Opens S) (x : S) (hx : x ∈ U)
    (f : SheafReduced.Section I S U) :
    reducedStalkConstantRetraction I S x
        ((SheafReduced.additiveSheaf I S).presheaf.germ U x hx f) =
      (complexAdditiveSheafStalkEquiv (TopCat.of S) x).symm (f ⟨x, hx⟩) :=
  congrArg (complexAdditiveSheafStalkEquiv (TopCat.of S) x).symm
    (reducedStalkEval_germ I S U x hx f)

/-- The retraction is a left inverse to the genuine reduced constant
inclusion on actual additive stalks. -/
theorem reducedStalkConstantRetraction_leftInverse (x : S) :
    Function.LeftInverse (reducedStalkConstantRetraction I S x)
      (fun s : TopCat.Presheaf.stalk (C := AddCommGrpCat)
          (complexAdditiveSheaf (TopCat.of S)).obj x =>
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of S) x).map
          (reducedAdditiveMap I S).hom s) := by
  intro s
  apply (complexAdditiveSheafStalkEquiv (TopCat.of S) x).injective
  exact (reducedStalkConstantRetraction_eval I S x _).trans
    (reducedStalkEval_reducedAdditiveMap I S x s)

/-- The actual reduced-stalk retraction as a categorical additive morphism. -/
def reducedStalkConstantRetractionHom (x : S) :
    (SheafReduced.additiveSheaf I S).presheaf.stalk x ⟶
      TopCat.Presheaf.stalk (C := AddCommGrpCat) (complexAdditiveSheaf (TopCat.of S)).obj x :=
  AddCommGrpCat.ofHom (reducedStalkConstantRetraction I S x)

/-- The actual constant inclusion followed by its retraction is the identity. -/
theorem reducedStalkConstantRetraction_comp (x : S) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of S) x).map
        (reducedAdditiveMap I S).hom ≫ reducedStalkConstantRetractionHom I S x =
      𝟙 (TopCat.Presheaf.stalk (C := AddCommGrpCat)
        (complexAdditiveSheaf (TopCat.of S)).obj x) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  exact reducedStalkConstantRetraction_leftInverse I S x s

end Wikipedia.HopfProblem.CuspNormalization.SheafConstants
