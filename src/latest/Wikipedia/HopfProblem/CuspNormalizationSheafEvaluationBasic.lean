import Wikipedia.HopfProblem.CuspNormalizationSheafFiniteStalkBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafForgetStalkBasic
import Wikipedia.HopfProblem.HolomorphicFunctionSheafCohomologyZeroBasic
import Wikipedia.HopfProblem.HolomorphicFunctionSheafLocalRingEvaluation
import Mathlib.Topology.Sheaves.Functors

/-!
# Actual scalar evaluation on pushforward holomorphic stalks

At a chosen point over the base, the canonical pushforward-stalk map,
the proved forgetful-stalk comparison, and actual holomorphic-germ
evaluation compose to a scalar-valued additive map. Its formula on
every actual inverse-image section is literal evaluation at that point.
No closedness, finiteness, stalk-model or cohomological assumption is
needed for this construction.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold AlgebraicGeometry

namespace Wikipedia.HopfProblem.CuspNormalization.SheafEvaluation

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  {B : Type} [TopologicalSpace B]

/-- The actual additive holomorphic-function sheaf pushed forward along
the specified continuous map. -/
abbrev pushedHolomorphicSheaf (p : TopCat.of M ⟶ TopCat.of B) :
    TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of B) :=
  (TopCat.Sheaf.pushforward AddCommGrpCat p).obj
    (HolomorphicFunctionSheaf.additiveSheaf I M)

/-- Scalar evaluation on the actual additive holomorphic stalk, obtained
from the proved comparison with the actual ring-valued stalk. -/
def holomorphicStalkEval (y : M) :
    (HolomorphicFunctionSheaf.additiveSheaf I M).presheaf.stalk y →+ ℂ :=
  (HolomorphicFunctionSheaf.stalkEval I M y).toAddMonoidHom.comp
    (SheafForgetStalk.stalkAddEquiv (HolomorphicFunctionSheaf.presheaf I M) y).toAddMonoidHom

/-- Evaluation on the actual additive stalk retains the literal section
value of every representative. -/
@[simp] theorem holomorphicStalkEval_germ (U : Opens M) (y : M) (hy : y ∈ U)
    (s : HolomorphicFunctionSheaf.Section I M U) :
    holomorphicStalkEval I y
        ((HolomorphicFunctionSheaf.additiveSheaf I M).presheaf.germ U y hy s) =
      s ⟨y, hy⟩ := by
  exact (congrArg (HolomorphicFunctionSheaf.stalkEval I M y)
    (SheafForgetStalk.stalkAddEquiv_germ (HolomorphicFunctionSheaf.presheaf I M)
      U y hy s)).trans (HolomorphicFunctionSheaf.stalkEval_germ I M U y hy s)

/-- The chosen source point belongs to the inverse image of each base
neighbourhood of its specified image point. -/
theorem point_mem_preimage (p : TopCat.of M ⟶ TopCat.of B)
    (y : M) (b : B) (hy : p y = b) (U : Opens B) (hb : b ∈ U) :
    y ∈ (Opens.map p).obj U :=
  SheafFiniteStalk.fiber_mem_preimage p b ⟨y, hy⟩ U hb

/-- Evaluation at an actual point of a fibre, on the genuine
pushforward stalk over its specified base point. -/
def stalkEvaluationAt (p : TopCat.of M ⟶ TopCat.of B)
    (y : M) (b : B) (hy : p y = b) :
    (pushedHolomorphicSheaf I p).presheaf.stalk b →+ ℂ :=
  (holomorphicStalkEval I y).comp
    (SheafFiniteStalk.pushforwardStalkComponent p
      (HolomorphicFunctionSheaf.additiveSheaf I M).presheaf b ⟨y, hy⟩).hom

/-- The same actual evaluation as a morphism in additive commutative
groups, with the source and target objects specified explicitly. -/
def stalkEvaluationAtHom (p : TopCat.of M ⟶ TopCat.of B)
    (y : M) (b : B) (hy : p y = b) :
    (pushedHolomorphicSheaf I p).presheaf.stalk b ⟶ AddCommGrpCat.of ℂ :=
  AddCommGrpCat.ofHom (stalkEvaluationAt I p y b hy)

@[simp] theorem stalkEvaluationAtHom_apply (p : TopCat.of M ⟶ TopCat.of B)
    (y : M) (b : B) (hy : p y = b)
    (s : (pushedHolomorphicSheaf I p).presheaf.stalk b) :
    stalkEvaluationAtHom I p y b hy s = stalkEvaluationAt I p y b hy s := rfl

/-- The actual pushforward-stalk evaluation is literal evaluation of an
actual holomorphic section on the base-open inverse image. -/
@[simp] theorem stalkEvaluationAt_germ (p : TopCat.of M ⟶ TopCat.of B)
    (y : M) (b : B) (hy : p y = b) (U : Opens B) (hb : b ∈ U)
    (s : HolomorphicFunctionSheaf.Section I M ((Opens.map p).obj U)) :
    stalkEvaluationAt I p y b hy
        ((pushedHolomorphicSheaf I p).presheaf.germ U b hb s) =
      s ⟨y, point_mem_preimage p y b hy U hb⟩ := by
  exact (congrArg (holomorphicStalkEval I y)
    (SheafFiniteStalk.pushforwardStalkComponent_germ p
      (HolomorphicFunctionSheaf.additiveSheaf I M).presheaf b ⟨y, hy⟩ U hb s)).trans
    (holomorphicStalkEval_germ I ((Opens.map p).obj U) y
      (point_mem_preimage p y b hy U hb) s)

/-- Constant sections show that this actual scalar evaluation is
surjective, with no hypothesis on the continuous base map. -/
theorem stalkEvaluationAt_surjective (p : TopCat.of M ⟶ TopCat.of B)
    (y : M) (b : B) (hy : p y = b) :
    Function.Surjective (stalkEvaluationAt I p y b hy) := by
  intro c
  let s : HolomorphicFunctionSheaf.Section I M ((Opens.map p).obj ⊤) :=
    ⟨fun _ => c, contMDiff_const⟩
  refine ⟨(pushedHolomorphicSheaf I p).presheaf.germ ⊤ b (by trivial) s, ?_⟩
  exact stalkEvaluationAt_germ I p y b hy ⊤ (by trivial) s

end Wikipedia.HopfProblem.CuspNormalization.SheafEvaluation
