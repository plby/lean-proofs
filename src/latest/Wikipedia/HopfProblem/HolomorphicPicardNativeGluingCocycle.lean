import Wikipedia.HopfProblem.HolomorphicPicardNativeGluing
import Wikipedia.HopfProblem.HolomorphicPicardNativeCocycle
import Wikipedia.HopfProblem.HolomorphicPicardCechRefinement

/-!
# The actual native cocycle of a glued bundle recovers the input cocycle

The preferred native trivialization of the constructed `VectorBundleCore`
is its existing local trivialization at `indexAt`. Consequently its actual
native cover refines the original cover. Evaluating the actual native
coordinate changes proves that its extracted Čech cocycle is exactly the
literal sheaf restriction of the original input cocycle along this refinement.
No alternative atlas or cocycle-defined bundle subtype is used.
-/

noncomputable section

open Bundle Set TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicPicardNative

open PeriodTorusLineBundleClassificationNative HolomorphicExponentialSheaf
  HolomorphicFunctionSheaf.SphereH1 HolomorphicPicard.Cech

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    (M : Type) [TopologicalSpace M] [ChartedSpace H M]
    {ι : Type} (U : ι → Opens M) (hcover : ∀ x : M, ∃ i : ι, x ∈ U i)
    (c : CechOneCocycle (unitsSheaf I M) U)

/-- The actual preferred native trivialization is the original core chart
selected by the already constructed core's index function. -/
@[simp] theorem nativeTriv_glued (y : M) :
    nativeTriv (cocycleCore I M U hcover c).Fiber y =
      (cocycleCore I M U hcover c).localTriv
        ((cocycleTransitionData I M U hcover c).indexAt y) := rfl

/-- The actual native cover is the corresponding original cover member. -/
@[simp] theorem nativeCover_glued (y : M) :
    nativeCover M (cocycleCore I M U hcover c).Fiber y =
      U ((cocycleTransitionData I M U hcover c).indexAt y) := rfl

/-- The actual native scalar transition on the refined overlap evaluates
to the original input cocycle at the selected original chart indices. -/
theorem scalarTransition_glued (a b x : M)
    (hx : x ∈ nativeCover M (cocycleCore I M U hcover c).Fiber a ⊓
      nativeCover M (cocycleCore I M U hcover c).Fiber b) :
    (scalarTransition (cocycleCore I M U hcover c).Fiber a b x : ℂ) =
      unitSectionEval (c.value
        ((cocycleTransitionData I M U hcover c).indexAt a)
        ((cocycleTransitionData I M U hcover c).indexAt b)) ⟨x, hx⟩ := by
  change ((cocycleCore I M U hcover c).localTriv
    ((cocycleTransitionData I M U hcover c).indexAt a)).coordChangeL ℂ
      ((cocycleCore I M U hcover c).localTriv
        ((cocycleTransitionData I M U hcover c).indexAt b)) x 1 = _
  exact (cocycleCore_localTriv_coordChange I M U hcover c
    ((cocycleTransitionData I M U hcover c).indexAt a)
    ((cocycleTransitionData I M U hcover c).indexAt b) hx 1).trans (mul_one _)

/-- Gluing the actual unit cocycle and extracting the resulting bundle's
actual native cocycle gives precisely its restriction along the native
preferred-chart refinement. -/
theorem nativeCocycle_glued_eq_refinement :
    nativeCocycle I M (cocycleCore I M U hcover c).Fiber =
      refinement (unitsSheaf I M)
        (V := nativeCover M (cocycleCore I M U hcover c).Fiber)
        (cocycleTransitionData I M U hcover c).indexAt (fun _ => le_rfl) c := by
  apply cocycle_ext
  intro a b
  apply unitSection_ext
  intro x
  change (scalarTransition (cocycleCore I M U hcover c).Fiber a b (x : M) : ℂ) =
    unitSectionEval (c.value
      ((cocycleTransitionData I M U hcover c).indexAt a)
      ((cocycleTransitionData I M U hcover c).indexAt b)) ⟨x, x.property⟩
  exact scalarTransition_glued I M U hcover c a b x x.property

end Wikipedia.HopfProblem.HolomorphicPicardNative
