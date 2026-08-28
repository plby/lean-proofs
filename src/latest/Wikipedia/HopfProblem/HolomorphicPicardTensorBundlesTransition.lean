import Wikipedia.HopfProblem.HolomorphicPicardTensorBundlesBasic
import Wikipedia.HopfProblem.HolomorphicPicardTensorCoreBasic

/-!
# The tensor object's transitions are the original transition products

Evaluating the literal sheaf restrictions identifies the constructed
tensor transition with the product of the two original native coordinate
changes.  The dual transition is the inverse original transition.
-/

noncomputable section

open Bundle TopologicalSpace

namespace Wikipedia.HopfProblem.HolomorphicPicard.TensorBundles

open HolomorphicExponentialSheaf HolomorphicPicardNative
open HolomorphicFunctionSheaf.SphereH1
open PeriodTorusLineBundleClassificationNative

universe u v

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  (V : LineBundle.{u} I M) (W : LineBundle.{v} I M)

/-- Literal restriction and addition in the original unit sheaf evaluate
to the product of the original native scalar coordinate changes. -/
@[simp] theorem tensorCocycle_eval (a b : M × M)
    (x : ↥(commonCover I M V W a ⊓ commonCover I M V W b)) :
    unitSectionEval ((tensorCocycle I M V W).value a b) x =
      (scalarTransition V.Fiber a.1 b.1 x : ℂ) *
        (scalarTransition W.Fiber a.2 b.2 x : ℂ) := rfl

/-- On an actual common overlap, the glued tensor transition is the
product of the original two native transition functions. -/
theorem tensorData_transition (a b : M × M) (x : M)
    (hx : x ∈ commonCover I M V W a ⊓ commonCover I M V W b) :
    ((tensorData I M V W).transition a b x : ℂ) =
      (scalarTransition V.Fiber a.1 b.1 x : ℂ) *
        (scalarTransition W.Fiber a.2 b.2 x : ℂ) :=
  (cocycleTransitionData_transition I M (commonCover I M V W)
    (commonCover_covers I M V W) (tensorCocycle I M V W) a b x hx).trans
      (tensorCocycle_eval I M V W a b ⟨x, hx⟩)

/-- The product transition is the actual coordinate change between the
constructed tensor bundle's two local trivializations. -/
theorem tensorCore_localTriv_coordChange (a b : M × M) (x : M)
    (hx : x ∈ commonCover I M V W a ⊓ commonCover I M V W b) (z : ℂ) :
    ((tensorCore I M V W).localTriv a).coordChangeL ℂ
        ((tensorCore I M V W).localTriv b) x z =
      ((scalarTransition V.Fiber a.1 b.1 x : ℂ) *
        (scalarTransition W.Fiber a.2 b.2 x : ℂ)) * z := by
  rw [(tensorData I M V W).core_localTriv_coordChange a b hx,
    tensorData_transition I M V W a b x hx]

/-- Inverting the original unit cocycle gives the actual inverse scalar
coordinate change of the original native bundle. -/
@[simp] theorem dualCocycle_eval (i j : M)
    (x : ↥(nativeCover M V.Fiber i ⊓ nativeCover M V.Fiber j)) :
    unitSectionEval ((dualCocycle I M V).value i j) x =
      (scalarTransition V.Fiber i j x : ℂ)⁻¹ :=
  unitSectionEval_neg ((nativeCocycle I M V.Fiber).value i j) x

/-- The dual's actual transition is the inverse of the original bundle's
native transition on the original overlap. -/
theorem dualData_transition (i j x : M)
    (hx : x ∈ nativeCover M V.Fiber i ⊓ nativeCover M V.Fiber j) :
    ((dualData I M V).transition i j x : ℂ) =
      (scalarTransition V.Fiber i j x : ℂ)⁻¹ :=
  (cocycleTransitionData_transition I M (nativeCover M V.Fiber)
    (nativeCover_covers M V.Fiber) (dualCocycle I M V) i j x hx).trans
      (dualCocycle_eval I M V i j ⟨x, hx⟩)

end Wikipedia.HopfProblem.HolomorphicPicard.TensorBundles
