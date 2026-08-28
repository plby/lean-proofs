import Wikipedia.HopfProblem.CuspNormalizationSheafReducedSheaf
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsAdditiveStalk

/-!
# Literal evaluation on the actual additive reduced-function stalk

The reduced sheaf consists of actual functions locally extendible to
ambient holomorphic functions.  Evaluating those functions at a point
gives a compatible additive cocone on its actual neighbourhood diagram.
The resulting colimit map needs no chart or analytic-germ comparison.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafConstants

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℂ E H) (S : Set M)

/-- Actual point evaluation is a cocone on the additive reduced-function
presheaf's neighbourhood diagram. -/
def reducedStalkEvalCocone (x : S) :
    Cocone ((OpenNhds.inclusion (X := TopCat.of S) x).op ⋙
      (SheafReduced.additiveSheaf I S).obj) where
  pt := AddCommGrpCat.of ℂ
  ι :=
    { app := fun U => AddCommGrpCat.ofHom
        (SheafReduced.eval I S U.unop.val ⟨x, U.unop.property⟩).toAddMonoidHom
      naturality := by
        intro U V i
        ext f
        rfl }

/-- The actual colimit-induced additive evaluation morphism. -/
def reducedStalkEvalHom (x : S) :
    (SheafReduced.additiveSheaf I S).presheaf.stalk x ⟶ AddCommGrpCat.of ℂ :=
  colimit.desc _ (reducedStalkEvalCocone I S x)

/-- Independent scalar evaluation on the actual reduced additive stalk. -/
def reducedStalkEval (x : S) :
    (SheafReduced.additiveSheaf I S).presheaf.stalk x →+ ℂ :=
  (reducedStalkEvalHom I S x).hom

/-- Every actual section representative gives its literal value. -/
@[simp] theorem reducedStalkEval_germ (U : Opens S) (x : S) (hx : x ∈ U)
    (f : SheafReduced.Section I S U) :
    reducedStalkEval I S x
        ((SheafReduced.additiveSheaf I S).presheaf.germ U x hx f) = f ⟨x, hx⟩ := by
  exact congrArg (fun h => h f)
    (colimit.ι_desc (reducedStalkEvalCocone I S x) (op ⟨U, hx⟩))

/-- Genuine constant sections realize every scalar under actual stalk evaluation. -/
theorem reducedStalkEval_surjective (x : S) : Function.Surjective (reducedStalkEval I S x) := by
  intro c
  exact ⟨(SheafReduced.additiveSheaf I S).presheaf.germ ⊤ x (by trivial)
    (SheafReduced.constant I S ⊤ c),
      reducedStalkEval_germ I S ⊤ x (by trivial) (SheafReduced.constant I S ⊤ c)⟩

end Wikipedia.HopfProblem.CuspNormalization.SheafConstants
