import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsAdditiveStalk
import Wikipedia.HopfProblem.CuspNormalizationSheafEvaluationBasic

/-!
# Actual scalar evaluation on pushed-forward constant-sheaf stalks

Evaluation first takes the canonical component of the actual pushforward
stalk at the selected source point, then uses the proved constant-sheaf
stalk identification with `ℂ`.  It is defined independently of the map
to holomorphic functions.  Its constant-germ formula is proved directly.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.CuspNormalization.SheafConstants

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]

/-- The genuine pushforward of the actual constant additive complex sheaf. -/
abbrev pushedConstantSheaf (p : TopCat.of M ⟶ TopCat.of B) :
    TopCat.Sheaf AddCommGrpCat (TopCat.of B) :=
  (TopCat.Sheaf.pushforward AddCommGrpCat p).obj (complexAdditiveSheaf (TopCat.of M))

/-- Independent scalar evaluation on the actual pushforward stalk, using
the selected fibre component and the actual constant-sheaf stalk isomorphism. -/
def constantStalkEvaluationAt (p : TopCat.of M ⟶ TopCat.of B)
    (y : M) (b : B) (hy : p y = b) :
    (pushedConstantSheaf p).presheaf.stalk b →+ ℂ :=
  (complexAdditiveSheafStalkEquiv (TopCat.of M) y).toAddMonoidHom.comp
    (SheafFiniteStalk.pushforwardStalkComponent p
      (complexAdditiveSheaf (TopCat.of M)).obj b ⟨y, hy⟩).hom

/-- The same actual scalar evaluation as a categorical additive homomorphism. -/
def constantStalkEvaluationAtHom (p : TopCat.of M ⟶ TopCat.of B)
    (y : M) (b : B) (hy : p y = b) :
    (pushedConstantSheaf p).presheaf.stalk b ⟶ AddCommGrpCat.of ℂ :=
  AddCommGrpCat.ofHom (constantStalkEvaluationAt p y b hy)

/-- The pushforward-stalk value is the value of the actual source germ. -/
@[simp] theorem constantStalkEvaluationAt_germ (p : TopCat.of M ⟶ TopCat.of B)
    (y : M) (b : B) (hy : p y = b) (U : Opens B) (hb : b ∈ U)
    (s : (complexAdditiveSheaf (TopCat.of M)).obj.obj (op ((Opens.map p).obj U))) :
    constantStalkEvaluationAt p y b hy
        ((pushedConstantSheaf p).presheaf.germ U b hb s) =
      complexAdditiveSheafStalkEquiv (TopCat.of M) y
        (TopCat.Presheaf.germ (complexAdditiveSheaf (TopCat.of M)).obj
          ((Opens.map p).obj U) y (SheafEvaluation.point_mem_preimage p y b hy U hb) s) :=
  congrArg (complexAdditiveSheafStalkEquiv (TopCat.of M) y)
    (SheafFiniteStalk.pushforwardStalkComponent_germ p
      (complexAdditiveSheaf (TopCat.of M)).obj b ⟨y, hy⟩ U hb s)

/-- A genuine sheafified constant representative has its original value. -/
@[simp] theorem constantStalkEvaluationAt_germ_unit (p : TopCat.of M ⟶ TopCat.of B)
    (y : M) (b : B) (hy : p y = b) (U : Opens B) (hb : b ∈ U) (c : ℂ) :
    constantStalkEvaluationAt p y b hy
        ((pushedConstantSheaf p).presheaf.germ U b hb
          ((additiveUnit (TopCat.of M)).app (op ((Opens.map p).obj U)) c)) = c :=
  (constantStalkEvaluationAt_germ p y b hy U hb _).trans
    (complexAdditiveSheafStalkEquiv_germ_unit (TopCat.of M) y
      ((Opens.map p).obj U) (SheafEvaluation.point_mem_preimage p y b hy U hb) c)

/-- Actual constant sections realize every scalar at every chosen fibre point. -/
theorem constantStalkEvaluationAt_surjective (p : TopCat.of M ⟶ TopCat.of B)
    (y : M) (b : B) (hy : p y = b) :
    Function.Surjective (constantStalkEvaluationAt p y b hy) := by
  intro c
  exact ⟨(pushedConstantSheaf p).presheaf.germ ⊤ b (by trivial)
    ((additiveUnit (TopCat.of M)).app (op ((Opens.map p).obj ⊤)) c),
    constantStalkEvaluationAt_germ_unit p y b hy ⊤ (by trivial) c⟩

end Wikipedia.HopfProblem.CuspNormalization.SheafConstants
