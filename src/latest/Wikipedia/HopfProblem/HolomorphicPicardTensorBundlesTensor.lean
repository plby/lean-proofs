import Wikipedia.HopfProblem.HolomorphicPicardTensorBundlesTransition
import Wikipedia.HopfProblem.HolomorphicPicardNativeGaugeBasic
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# The constructed tensor bundle has the original tensor-product fibres

The two original native local linear equivalences identify their genuine
fibre tensor product with the preferred fibre of the constructed tensor
bundle.  The original native coordinate-change identities prove the
formula in every common local chart, not just the selected one.
-/

noncomputable section

open Bundle TopologicalSpace
open scoped TensorProduct

namespace Wikipedia.HopfProblem.HolomorphicPicard.TensorBundles

open HolomorphicPicardNative HolomorphicCharacterBundle
open PeriodTorusLineBundleClassificationNative

universe u v

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  (V : LineBundle.{u} I M) (W : LineBundle.{v} I M)

/-- The native core chooses an index in the actual common cover. -/
abbrev tensorIndexAt (x : M) : M × M := (tensorData I M V W).indexAt x

theorem tensorIndexAt_mem (x : M) : x ∈ commonCover I M V W (tensorIndexAt I M V W x) :=
  (tensorData I M V W).mem_baseSet_at x

/-- The original left fibre's genuine linear coordinate at the selected
member of the common cover. -/
def tensorLeftCoordinate (x : M) : V.Fiber x ≃ₗ[ℂ] ℂ :=
  (nativeTriv V.Fiber (tensorIndexAt I M V W x).1).linearEquivAt ℂ x
    (tensorIndexAt_mem I M V W x).1

/-- The original right fibre's genuine linear coordinate at the selected
member of the common cover. -/
def tensorRightCoordinate (x : M) : W.Fiber x ≃ₗ[ℂ] ℂ :=
  (nativeTriv W.Fiber (tensorIndexAt I M V W x).2).linearEquivAt ℂ x
    (tensorIndexAt_mem I M V W x).2

/-- The tensor object has the genuine tensor product of the two original
native fibres, with no fibre presentation or global-frame hypothesis. -/
def tensorFiberEquiv (x : M) :
    V.Fiber x ⊗[ℂ] W.Fiber x ≃ₗ[ℂ] (LineBundle.tensorBundle I M V W).Fiber x :=
  (TensorProduct.congr (tensorLeftCoordinate I M V W x)
    (tensorRightCoordinate I M V W x)).trans (TensorProduct.lid ℂ ℂ)

/-- The preferred-coordinate formula follows from the actual tensor
product of the original native linear equivalences. -/
@[simp] theorem tensorFiberEquiv_tmul (x : M) (z : V.Fiber x) (w : W.Fiber x) :
    tensorFiberEquiv I M V W x (z ⊗ₜ[ℂ] w) =
      (nativeTriv V.Fiber (tensorIndexAt I M V W x).1 ⟨x, z⟩).2 *
        (nativeTriv W.Fiber (tensorIndexAt I M V W x).2 ⟨x, w⟩).2 := by
  rfl

/-- Every original pair of local charts identifies the genuine fibre
tensor map with multiplication of the two original scalar coordinates. -/
theorem tensorFiberEquiv_coordinate (a : M × M) (x : M)
    (hx : x ∈ commonCover I M V W a) (z : V.Fiber x) (w : W.Fiber x) :
    ((tensorCore I M V W).localTriv a
      ⟨x, tensorFiberEquiv I M V W x (z ⊗ₜ[ℂ] w)⟩).2 =
      (nativeTriv V.Fiber a.1 ⟨x, z⟩).2 * (nativeTriv W.Fiber a.2 ⟨x, w⟩).2 := by
  rw [TransitionData.core_localTriv_apply, tensorFiberEquiv_tmul]
  change ((tensorData I M V W).transition (tensorIndexAt I M V W x) a x : ℂ) *
      ((nativeTriv V.Fiber (tensorIndexAt I M V W x).1 ⟨x, z⟩).2 *
        (nativeTriv W.Fiber (tensorIndexAt I M V W x).2 ⟨x, w⟩).2) = _
  rw [tensorData_transition I M V W (tensorIndexAt I M V W x) a x
    ⟨tensorIndexAt_mem I M V W x, hx⟩,
    NativeGauge.native_coordinates V.Fiber (tensorIndexAt I M V W x).1 a.1 x
      (tensorIndexAt_mem I M V W x).1 hx.1 z,
    NativeGauge.native_coordinates W.Fiber (tensorIndexAt I M V W x).2 a.2 x
      (tensorIndexAt_mem I M V W x).2 hx.2 w]
  ring

/-- The chart compatibility is an equality of linear maps on the full
tensor product of the original fibres. -/
theorem tensorFiberEquiv_localTriv (a : M × M) (x : M)
    (hx : x ∈ commonCover I M V W a) :
    ((tensorCore I M V W).localTriv a).linearMapAt ℂ x ∘ₗ
        (tensorFiberEquiv I M V W x).toLinearMap =
      (TensorProduct.lid ℂ ℂ).toLinearMap ∘ₗ
        TensorProduct.map ((nativeTriv V.Fiber a.1).linearMapAt ℂ x)
          ((nativeTriv W.Fiber a.2).linearMapAt ℂ x) := by
  apply TensorProduct.ext'
  intro z w
  change ((tensorCore I M V W).localTriv a).linearMapAt ℂ x
      (tensorFiberEquiv I M V W x (z ⊗ₜ[ℂ] w)) =
    (TensorProduct.lid ℂ ℂ)
      (((nativeTriv V.Fiber a.1).linearMapAt ℂ x z) ⊗ₜ[ℂ]
        ((nativeTriv W.Fiber a.2).linearMapAt ℂ x w))
  rw [Trivialization.coe_linearMapAt_of_mem (R := ℂ)
      ((tensorCore I M V W).localTriv a) hx,
    Trivialization.coe_linearMapAt_of_mem (R := ℂ) (nativeTriv V.Fiber a.1) hx.1,
    Trivialization.coe_linearMapAt_of_mem (R := ℂ) (nativeTriv W.Fiber a.2) hx.2]
  simpa only [TensorProduct.lid_tmul, smul_eq_mul] using
    tensorFiberEquiv_coordinate I M V W a x hx z w

end Wikipedia.HopfProblem.HolomorphicPicard.TensorBundles
