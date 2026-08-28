import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersCanonical
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersLineBundleTensorFibres

/-!
# Full intrinsic tensor fibres of the native pluricanonical bundles

Every powered fibre is linearly identified with the entire algebraic
tensor product of the original canonical fibres, and hence with the
entire tensor product of the actual alternating three-covector spaces.
The identifications commute with the original canonical fibre maps.
Thus these bundles are genuine pluricanonical bundles, not merely
line bundles assigned a power name.
-/

noncomputable section

open Bundle
open scoped ContDiff TensorProduct

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Powers

open TrianglePeriodFamily.Canonical CanonicalGlobalLineBundle.Powers

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- The full tensor product of the original native canonical fibres. -/
abbrev NativeTensorFiber (x : Threefold.Space) (n : ℕ) :=
  CanonicalGlobalLineBundle.Powers.TensorPower (Threefold.Canonical.bundle.Fiber x) n

/-- The full tensor product of intrinsic alternating covectors on the
actual threefold tangent space. -/
abbrev IntrinsicTensorFiber (x : Threefold.Space) (n : ℕ) :=
  CanonicalGlobalLineBundle.Powers.TensorPower (Threefold.Canonical.IntrinsicTopCovector x) n

/-- The scalar power-cocycle fibre is the actual tensor power of the
original canonical fibre via the proved original fibre identification. -/
def nativeTensorFiberEquiv (x : Threefold.Space) (n : ℕ) :
    NativeTensorFiber x n ≃ₗ[ℂ] (bundle n).Fiber x :=
  (tensorPowerCongr (NativePresentation.fiberEquiv x).toLinearEquiv n).trans
    (fiberTensorPowerEquiv canonicalData x n)

/-- Intrinsic identification on the entire tensor product of actual
alternating three-covectors, not only on the chosen volume tensors. -/
def intrinsicTensorFiberEquiv (x : Threefold.Space) (n : ℕ) :
    (bundle n).Fiber x ≃ₗ[ℂ] IntrinsicTensorFiber x n :=
  (fiberTensorPowerEquiv canonicalData x n).symm.trans
    (tensorPowerCongr (NativePresentation.dataIntrinsicEquiv x).toLinearEquiv n)

theorem nativeTensorFiberEquiv_tprod (x : Threefold.Space) (n : ℕ)
    (v : Fin n → Threefold.Canonical.bundle.Fiber x) :
    nativeTensorFiberEquiv x n (PiTensorProduct.tprod ℂ v) =
      ∏ k, id (α := ℂ) (NativePresentation.fiberEquiv x (v k)) := by
  simp only [nativeTensorFiberEquiv, LinearEquiv.trans_apply, tensorPowerCongr_tprod,
    fiberTensorPowerEquiv_tprod, ContinuousLinearEquiv.coe_toLinearEquiv]
  rfl

/-- Compatibility with the actual original canonical-to-covector map
holds on the whole tensor product. -/
theorem intrinsicTensorFiberEquiv_nativeTensorFiberEquiv
    (x : Threefold.Space) (n : ℕ) (v : NativeTensorFiber x n) :
    intrinsicTensorFiberEquiv x n (nativeTensorFiberEquiv x n v) =
      tensorPowerCongr (Threefold.Canonical.intrinsicEquiv x).toLinearEquiv n v := by
  have hc : (NativePresentation.fiberEquiv x).toLinearEquiv.trans
      (NativePresentation.dataIntrinsicEquiv x).toLinearEquiv =
        (Threefold.Canonical.intrinsicEquiv x).toLinearEquiv := by
    apply LinearEquiv.ext
    intro w
    exact NativePresentation.dataIntrinsicEquiv_fiberEquiv x w
  simp only [intrinsicTensorFiberEquiv, nativeTensorFiberEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]
  have ht := congrArg
    (fun e : NativeTensorFiber x n ≃ₗ[ℂ] IntrinsicTensorFiber x n => e v)
    (tensorPowerCongr_trans (NativePresentation.fiberEquiv x).toLinearEquiv
      (NativePresentation.dataIntrinsicEquiv x).toLinearEquiv n)
  rw [hc] at ht
  exact ht.symm

/-- Pure tensors are the actual powers of the corresponding intrinsic
three-covector in every degree. -/
theorem intrinsicTensorFiberEquiv_purePower (x : Threefold.Space) (n : ℕ)
    (v : Threefold.Canonical.bundle.Fiber x) :
    intrinsicTensorFiberEquiv x n (nativeTensorFiberEquiv x n (purePower v n)) =
      purePower (Threefold.Canonical.intrinsicEquiv x v) n := by
  rw [intrinsicTensorFiberEquiv_nativeTensorFiberEquiv, tensorPowerCongr_purePower]
  rfl

theorem nativeTensorFiberEquiv_purePower_ne_zero (x : Threefold.Space) (n : ℕ)
    (v : Threefold.Canonical.bundle.Fiber x) (hv : v ≠ 0) :
    nativeTensorFiberEquiv x n (purePower v n) ≠ 0 := by
  intro hz
  have hp := (nativeTensorFiberEquiv x n).injective (hz.trans (map_zero _).symm)
  exact purePower_ne_zero hv n hp

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Powers
