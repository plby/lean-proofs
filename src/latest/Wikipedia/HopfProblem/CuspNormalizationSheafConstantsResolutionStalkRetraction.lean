import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsEvaluationCompatibilityStalk
import Wikipedia.HopfProblem.CuspNormalizationSheafFiniteStalk

/-!
# A genuine scalar-evaluation retraction on finite pushforward stalks

For a closed continuous map with Hausdorff source and finite fibre, the
proved actual-stalk formula identifies the constant-sheaf pushforward
stalk with one complex value per fibre point.  Evaluating an actual
holomorphic pushforward stalk at those points and applying the inverse
identification gives a retraction of the actual constant inclusion.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafConstants

section FibreValues

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B] [T2Space M]

/-- Actual constant pushforward stalks are complex-valued functions on
the actual finite fibre, via the proved finite-fibre stalk comparison. -/
def constantFibreValueEquiv (p : TopCat.of M ⟶ TopCat.of B) (hp : IsClosedMap p)
    (b : B) (hfinite : (p ⁻¹' {b}).Finite) :
    (pushedConstantSheaf p).presheaf.stalk b ≃+ (∀ _ : p ⁻¹' {b}, ℂ) :=
  (SheafFiniteStalk.pushforwardStalkEquiv p hp
    (complexAdditiveSheaf (TopCat.of M)) b hfinite).trans
      (AddEquiv.piCongrRight fun x => complexAdditiveSheafStalkEquiv (TopCat.of M) x.val)

/-- Each coordinate is the independently defined actual constant-stalk
evaluation at the selected fibre point. -/
@[simp] theorem constantFibreValueEquiv_apply
    (p : TopCat.of M ⟶ TopCat.of B) (hp : IsClosedMap p)
    (b : B) (hfinite : (p ⁻¹' {b}).Finite)
    (s : (pushedConstantSheaf p).presheaf.stalk b) (x : p ⁻¹' {b}) :
    constantFibreValueEquiv p hp b hfinite s x =
      constantStalkEvaluationAt p x.val b x.property s := rfl

end FibreValues

section Retraction

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {B : Type} [TopologicalSpace B]

/-- Actual scalar evaluations at the fibre points define an additive
map back to the actual constant pushforward stalk. -/
def holomorphicStalkConstantRetraction (p : TopCat.of M ⟶ TopCat.of B)
    (hp : IsClosedMap p) (b : B) (hfinite : (p ⁻¹' {b}).Finite) :
    (SheafEvaluation.pushedHolomorphicSheaf I p).presheaf.stalk b →+
      (pushedConstantSheaf p).presheaf.stalk b :=
  (constantFibreValueEquiv p hp b hfinite).symm.toAddMonoidHom.comp
    (AddMonoidHom.pi fun x : p ⁻¹' {b} =>
      SheafEvaluation.stalkEvaluationAt I p x.val b x.property)

/-- The value of the retracted germ at each fibre point is exactly its
original holomorphic scalar evaluation. -/
@[simp] theorem holomorphicStalkConstantRetraction_component
    (p : TopCat.of M ⟶ TopCat.of B) (hp : IsClosedMap p)
    (b : B) (hfinite : (p ⁻¹' {b}).Finite)
    (s : (SheafEvaluation.pushedHolomorphicSheaf I p).presheaf.stalk b)
    (x : p ⁻¹' {b}) :
    constantFibreValueEquiv p hp b hfinite
        (holomorphicStalkConstantRetraction I p hp b hfinite s) x =
      SheafEvaluation.stalkEvaluationAt I p x.val b x.property s :=
  congrFun ((constantFibreValueEquiv p hp b hfinite).apply_symm_apply
    (fun x : p ⁻¹' {b} => SheafEvaluation.stalkEvaluationAt I p x.val b x.property s)) x

/-- The same computation using the independent constant evaluation at
an arbitrary named point of the fibre. -/
@[simp] theorem holomorphicStalkConstantRetraction_eval
    (p : TopCat.of M ⟶ TopCat.of B) (hp : IsClosedMap p)
    (b : B) (hfinite : (p ⁻¹' {b}).Finite)
    (s : (SheafEvaluation.pushedHolomorphicSheaf I p).presheaf.stalk b)
    (y : M) (hy : p y = b) :
    constantStalkEvaluationAt p y b hy
        (holomorphicStalkConstantRetraction I p hp b hfinite s) =
      SheafEvaluation.stalkEvaluationAt I p y b hy s :=
  holomorphicStalkConstantRetraction_component I p hp b hfinite s ⟨y, hy⟩

/-- The actual scalar-evaluation retraction is a left inverse to the
actual stalk map of the pushed constant-to-holomorphic inclusion. -/
theorem holomorphicStalkConstantRetraction_leftInverse
    (p : TopCat.of M ⟶ TopCat.of B) (hp : IsClosedMap p)
    (b : B) (hfinite : (p ⁻¹' {b}).Finite) :
    Function.LeftInverse (holomorphicStalkConstantRetraction I p hp b hfinite)
      (fun s : (pushedConstantSheaf p).presheaf.stalk b =>
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat (X := TopCat.of B) b).map
        ((TopCat.Sheaf.pushforward AddCommGrpCat p).map
          (holomorphicAdditiveMap I M)).hom s) := by
  intro s
  apply (constantFibreValueEquiv p hp b hfinite).injective
  funext x
  exact (holomorphicStalkConstantRetraction_component I p hp b hfinite _ x).trans
    ((stalkEvaluationAt_holomorphicAdditiveMap I p x.val b x.property s).trans
      (constantFibreValueEquiv_apply p hp b hfinite s x).symm)

/-- The retraction as a morphism of the actual additive stalk objects. -/
def holomorphicStalkConstantRetractionHom (p : TopCat.of M ⟶ TopCat.of B)
    (hp : IsClosedMap p) (b : B) (hfinite : (p ⁻¹' {b}).Finite) :
    (SheafEvaluation.pushedHolomorphicSheaf I p).presheaf.stalk b ⟶
      (pushedConstantSheaf p).presheaf.stalk b :=
  AddCommGrpCat.ofHom (holomorphicStalkConstantRetraction I p hp b hfinite)

/-- Inclusion followed by the genuine stalk retraction is the identity. -/
theorem holomorphicStalkConstantRetraction_comp
    (p : TopCat.of M ⟶ TopCat.of B) (hp : IsClosedMap p)
    (b : B) (hfinite : (p ⁻¹' {b}).Finite) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat b).map
        ((TopCat.Sheaf.pushforward AddCommGrpCat p).map
          (holomorphicAdditiveMap I M)).hom ≫
      holomorphicStalkConstantRetractionHom I p hp b hfinite =
        𝟙 ((pushedConstantSheaf p).presheaf.stalk b) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  exact holomorphicStalkConstantRetraction_leftInverse I p hp b hfinite s

end Retraction

end Wikipedia.HopfProblem.CuspNormalization.SheafConstants
