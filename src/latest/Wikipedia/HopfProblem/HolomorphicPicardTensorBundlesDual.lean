import Wikipedia.HopfProblem.HolomorphicPicardTensorBundlesBasic
import Wikipedia.HopfProblem.HolomorphicPicardTensorCoreDual
import Wikipedia.HopfProblem.HolomorphicPicardNativeRecovery

/-!
# The dual fibres of arbitrary original native line bundles

The native cocycle recovery isomorphism identifies the original fibres
with the fibres of their glued native cocycle.  Its transpose, followed
by the inverse-cocycle dual identification, gives the actual algebraic
dual of each original fibre.  Every original native chart intertwines
this identification with the transpose of its genuine inverse chart map.
-/

noncomputable section

open Bundle TopologicalSpace
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicPicard.TensorBundles

open HolomorphicPicardNative PeriodTorusLineBundleClassificationNative

universe u

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  (V : LineBundle.{u} I M)

/-- The genuine native recovery isomorphism carries the inverse core chart
to the inverse original chart on every original chart domain. -/
theorem dualRecovery_symmL (i x : M) (hx : x ∈ nativeCover M V.Fiber i) (z : ℂ) :
    (nativeCocycleBundleIso I M V.Fiber).fiberEquiv x
        (((nativeCocycleData I M V.Fiber).core.localTriv i).symmL ℂ x z) =
      (nativeTriv V.Fiber i).symmL ℂ x z := by
  have hn : x ∈ (nativeTriv V.Fiber i).baseSet := hx
  have hc : x ∈ ((nativeCocycleData I M V.Fiber).core.localTriv i).baseSet := hx
  apply ((nativeTriv V.Fiber i).linearEquivAt ℂ x hn).injective
  have h := congrArg Prod.snd
    (nativeCocycleBundleIso_localTriv I M V.Fiber i
      ⟨x, ((nativeCocycleData I M V.Fiber).core.localTriv i).symmL ℂ x z⟩ hn)
  rw [(nativeCocycleBundleIso I M V.Fiber).map_fiber] at h
  calc
    _ = ((nativeCocycleData I M V.Fiber).core.localTriv i
        ⟨x, ((nativeCocycleData I M V.Fiber).core.localTriv i).symmL ℂ x z⟩).2 := h
    _ = z := by
      rw [Trivialization.symmL_apply _ hc, Trivialization.apply_mk_symm _ hc]
    _ = _ := by
      change z = (nativeTriv V.Fiber i ⟨x, (nativeTriv V.Fiber i).symmL ℂ x z⟩).2
      rw [Trivialization.symmL_apply _ hn, Trivialization.apply_mk_symm _ hn]

/-- An actual complex-linear equivalence from the dual of the arbitrary
original fibre to the fibre of the native inverse-cocycle bundle. -/
def dualFiberEquiv (x : M) :
    Module.Dual ℂ (V.Fiber x) ≃ₗ[ℂ] (LineBundle.dualBundle I M V).Fiber x :=
  ((nativeCocycleBundleIso I M V.Fiber).fiberEquiv x).dualMap.trans
    (TensorCore.fibreDualEquiv I M (nativeCover M V.Fiber)
      (nativeCover_covers M V.Fiber) (nativeCocycle I M V.Fiber) x)

@[simp] theorem dualFiberEquiv_apply (x : M) (f : Module.Dual ℂ (V.Fiber x)) :
    dualFiberEquiv I M V x f =
      f ((nativeCocycleBundleIso I M V.Fiber).fiberEquiv x (1 : ℂ)) := rfl

/-- The fibre equivalence preserves evaluation on every original vector. -/
theorem dualFiberEquiv_pairing (x : M) (f : Module.Dual ℂ (V.Fiber x)) (v : V.Fiber x) :
    (id (α := ℂ) (dualFiberEquiv I M V x f)) *
        (id (α := ℂ) (((nativeCocycleBundleIso I M V.Fiber).fiberEquiv x).symm v)) =
      f v := by
  have h := TensorCore.fibreDualEquiv_pairing I M (nativeCover M V.Fiber)
    (nativeCover_covers M V.Fiber) (nativeCocycle I M V.Fiber) x
    (((nativeCocycleBundleIso I M V.Fiber).fiberEquiv x).dualMap f)
    (((nativeCocycleBundleIso I M V.Fiber).fiberEquiv x).symm v)
  change (id (α := ℂ) (TensorCore.fibreDualEquiv I M (nativeCover M V.Fiber)
      (nativeCover_covers M V.Fiber) (nativeCocycle I M V.Fiber) x
      (((nativeCocycleBundleIso I M V.Fiber).fiberEquiv x).dualMap f))) *
    (id (α := ℂ) (((nativeCocycleBundleIso I M V.Fiber).fiberEquiv x).symm v)) = f v
  simpa only [LinearEquiv.dualMap_apply,
    LinearEquiv.apply_symm_apply] using h

/-- In every original native chart, the actual dual fibre coordinate is
the functional precomposed with the original inverse chart map.  This is
an equality of linear maps on the whole original dual fibre. -/
theorem dualFiberEquiv_localTriv (i x : M) (hx : x ∈ nativeCover M V.Fiber i) :
    ((dualCore I M V).localTriv i).linearMapAt ℂ x ∘ₗ
        (dualFiberEquiv I M V x).toLinearMap =
      (LinearMap.ringLmapEquivSelf ℂ ℂ ℂ).toLinearMap ∘ₗ
        ((nativeTriv V.Fiber i).symmL ℂ x).toLinearMap.dualMap := by
  apply LinearMap.ext
  intro f
  have h := DFunLike.congr_fun
    (TensorCore.fibreDualEquiv_localTriv I M (nativeCover M V.Fiber)
      (nativeCover_covers M V.Fiber) (nativeCocycle I M V.Fiber) i x hx)
    (((nativeCocycleBundleIso I M V.Fiber).fiberEquiv x).dualMap f)
  change ((dualCore I M V).localTriv i).linearMapAt ℂ x
      (dualFiberEquiv I M V x f) = f ((nativeTriv V.Fiber i).symmL ℂ x (1 : ℂ))
  calc
    _ = f ((nativeCocycleBundleIso I M V.Fiber).fiberEquiv x
        (((nativeCocycleData I M V.Fiber).core.localTriv i).symmL ℂ x (1 : ℂ))) := h
    _ = _ := congrArg f (dualRecovery_symmL I M V i x hx 1)

end Wikipedia.HopfProblem.HolomorphicPicard.TensorBundles
