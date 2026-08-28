import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalNativeCanonicalHolomorphic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalBundle

/-!
# The native canonical bundle of the actual threefold in transition-data form

The source is the genuine tangent-atlas canonical bundle of the constructed
compact threefold.  Its target is the independently constructed bundle of
unit-valued native reverse Jacobians.  The explicit comparison is a
biholomorphism for their original total-space atlases, is complex-linear
on fibres, and preserves every intrinsic continuous alternating
three-covector on the actual tangent space.  Its chart formulas use the
literal manifold derivatives on the full native chart overlaps.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.NativePresentation

open TrianglePeriodFamily.Canonical

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "Iκ" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ Model) (modelWithCornersSelf ℂ ℂ)

attribute [local instance] Threefold.chartedSpace

local instance nativePresentationManifold : IsManifold IF ω Threefold.Space :=
  Threefold.space_isManifold

/-- The actual unit-valued reverse-Jacobian presentation on the original global atlas. -/
abbrev transitionData := NativeTransitions.data Threefold.Space

/-- The holomorphic bundle independently constructed from those native unit transitions. -/
abbrev transitionBundle := transitionData.core

theorem transitionBundle_holomorphic :
    ContMDiffVectorBundle ω ℂ transitionBundle.Fiber IF :=
  transitionData.core_contMDiffVectorBundle IF

theorem transitionBundle_totalSpace_isManifold :
    IsManifold Iκ ω transitionBundle.TotalSpace :=
  transitionData.core_totalSpace_isManifold IF

/-- The genuine continuous linear comparison over each literal global base point. -/
def fiberEquiv (x : Threefold.Space) :
    Threefold.Canonical.bundle.Fiber x ≃L[ℂ] transitionBundle.Fiber x :=
  NativeCanonical.fiberEquiv Threefold.Space x

/-- Full intrinsic three-covectors on the actual global tangent space,
as represented by the independently constructed target bundle. -/
def dataIntrinsicEquiv (x : Threefold.Space) :
    transitionBundle.Fiber x ≃L[ℂ] Threefold.Canonical.IntrinsicTopCovector x :=
  NativeCanonical.intrinsicEquiv Threefold.Space x

/-- Actual target-bundle chart coefficients interpreted as full three-covectors. -/
def dataInCoordinates (i : atlas Model Threefold.Space) (x : Threefold.Space)
    (v : transitionBundle.Fiber x) : TopCovector :=
  NativeCanonical.inCoordinates Threefold.Space i x v

theorem dataInCoordinates_eq_intrinsic_pullback (i : atlas Model Threefold.Space)
    {x : Threefold.Space} (hx : x ∈ i.val.source) (v : transitionBundle.Fiber x) :
    dataInCoordinates i x v = (dataIntrinsicEquiv x v).compContinuousLinearMap
      ((tangentBundleCore IF Threefold.Space).coordChange i (achart Model x) x) :=
  NativeCanonical.inCoordinates_eq_intrinsic_pullback Threefold.Space i hx v

theorem dataInCoordinates_preferred (x : Threefold.Space) (v : transitionBundle.Fiber x) :
    dataInCoordinates (achart Model x) x v = dataIntrinsicEquiv x v :=
  NativeCanonical.inCoordinates_preferred Threefold.Space x v

/-- Changing actual global charts acts by the genuine reversed chart differential. -/
theorem dataInCoordinates_change (i j : atlas Model Threefold.Space) {x : Threefold.Space}
    (hi : x ∈ i.val.source) (hj : x ∈ j.val.source) (v : transitionBundle.Fiber x) :
    dataInCoordinates j x v = (dataInCoordinates i x v).compContinuousLinearMap
      (fderiv ℂ (i.val ∘ j.val.symm) (j.val x)) :=
  NativeCanonical.inCoordinates_change Threefold.Space i j hi hj v

theorem dataInCoordinates_fiberEquiv (i : atlas Model Threefold.Space) {x : Threefold.Space}
    (hx : x ∈ i.val.source) (v : Threefold.Canonical.bundle.Fiber x) :
    dataInCoordinates i x (fiberEquiv x v) = Threefold.Canonical.inCoordinates i x v :=
  NativeCanonical.inCoordinates_fiberEquiv Threefold.Space i hx v

theorem dataInCoordinates_fiberEquiv_symm (i : atlas Model Threefold.Space)
    {x : Threefold.Space} (hx : x ∈ i.val.source) (v : transitionBundle.Fiber x) :
    Threefold.Canonical.inCoordinates i x ((fiberEquiv x).symm v) =
      dataInCoordinates i x v :=
  NativeCanonical.inCoordinates_fiberEquiv_symm Threefold.Space i hx v

@[simp] theorem dataIntrinsicEquiv_fiberEquiv (x : Threefold.Space)
    (v : Threefold.Canonical.bundle.Fiber x) :
    dataIntrinsicEquiv x (fiberEquiv x v) = Threefold.Canonical.intrinsicEquiv x v :=
  NativeCanonical.intrinsicEquiv_fiberEquiv Threefold.Space x v

@[simp] theorem dataIntrinsicEquiv_fiberEquiv_symm (x : Threefold.Space)
    (v : transitionBundle.Fiber x) :
    Threefold.Canonical.intrinsicEquiv x ((fiberEquiv x).symm v) =
      dataIntrinsicEquiv x v :=
  NativeCanonical.intrinsicEquiv_fiberEquiv_symm Threefold.Space x v

/-- The actual native canonical bundle and its unit-valued transition
presentation are biholomorphic with their original bundle atlases. -/
def bundleBiholomorph : Diffeomorph Iκ Iκ Threefold.Canonical.bundle.TotalSpace
    transitionBundle.TotalSpace ω :=
  NativeCanonical.bundleBiholomorph Threefold.Space

@[simp] theorem bundleBiholomorph_proj (p : Threefold.Canonical.bundle.TotalSpace) :
    (bundleBiholomorph p).proj = p.proj := rfl

@[simp] theorem bundleBiholomorph_symm_proj (p : transitionBundle.TotalSpace) :
    (bundleBiholomorph.symm p).proj = p.proj := rfl

@[simp] theorem bundleBiholomorph_mk (x : Threefold.Space)
    (v : Threefold.Canonical.bundle.Fiber x) :
    bundleBiholomorph ⟨x, v⟩ = ⟨x, fiberEquiv x v⟩ := rfl

@[simp] theorem bundleBiholomorph_symm_mk (x : Threefold.Space)
    (v : transitionBundle.Fiber x) :
    bundleBiholomorph.symm ⟨x, v⟩ = ⟨x, (fiberEquiv x).symm v⟩ := rfl

theorem bundleBiholomorph_add (x : Threefold.Space)
    (v w : Threefold.Canonical.bundle.Fiber x) :
    id (α := ℂ) (bundleBiholomorph ⟨x, v + w⟩).2 =
      id (α := ℂ) (bundleBiholomorph ⟨x, v⟩).2 +
        id (α := ℂ) (bundleBiholomorph ⟨x, w⟩).2 :=
  NativeCanonical.bundleBiholomorph_add Threefold.Space x v w

theorem bundleBiholomorph_smul (x : Threefold.Space) (c : ℂ)
    (v : Threefold.Canonical.bundle.Fiber x) :
    id (α := ℂ) (bundleBiholomorph ⟨x, c • v⟩).2 =
      c • id (α := ℂ) (bundleBiholomorph ⟨x, v⟩).2 :=
  NativeCanonical.bundleBiholomorph_smul Threefold.Space x c v

theorem bundleBiholomorph_localTriv (i : atlas Model Threefold.Space)
    (p : Threefold.Canonical.bundle.TotalSpace) (hp : p.proj ∈ i.val.source) :
    (transitionBundle.localTriv i (bundleBiholomorph p)).2 =
      (Threefold.Canonical.bundle.localTriv i p).2 :=
  NativeCanonical.bundleBiholomorph_localTriv Threefold.Space i p hp

theorem bundleBiholomorph_symm_localTriv (i : atlas Model Threefold.Space)
    (p : transitionBundle.TotalSpace) (hp : p.proj ∈ i.val.source) :
    (Threefold.Canonical.bundle.localTriv i (bundleBiholomorph.symm p)).2 =
      (transitionBundle.localTriv i p).2 :=
  NativeCanonical.bundleBiholomorph_symm_localTriv Threefold.Space i p hp

/-- The total-space comparison preserves the full intrinsic covector, not only its character. -/
theorem bundleBiholomorph_intrinsic (p : Threefold.Canonical.bundle.TotalSpace) :
    dataIntrinsicEquiv (bundleBiholomorph p).proj (bundleBiholomorph p).2 =
      Threefold.Canonical.intrinsicEquiv p.proj p.2 :=
  dataIntrinsicEquiv_fiberEquiv p.proj p.2

theorem bundleBiholomorph_symm_intrinsic (p : transitionBundle.TotalSpace) :
    Threefold.Canonical.intrinsicEquiv (bundleBiholomorph.symm p).proj
      (bundleBiholomorph.symm p).2 = dataIntrinsicEquiv p.proj p.2 :=
  dataIntrinsicEquiv_fiberEquiv_symm p.proj p.2

theorem bundleBiholomorph_inCoordinates (i : atlas Model Threefold.Space)
    (p : Threefold.Canonical.bundle.TotalSpace) (hp : p.proj ∈ i.val.source) :
    dataInCoordinates i (bundleBiholomorph p).proj (bundleBiholomorph p).2 =
      Threefold.Canonical.inCoordinates i p.proj p.2 :=
  dataInCoordinates_fiberEquiv i hp p.2

theorem bundleBiholomorph_symm_inCoordinates (i : atlas Model Threefold.Space)
    (p : transitionBundle.TotalSpace) (hp : p.proj ∈ i.val.source) :
    Threefold.Canonical.inCoordinates i (bundleBiholomorph.symm p).proj
      (bundleBiholomorph.symm p).2 = dataInCoordinates i p.proj p.2 :=
  dataInCoordinates_fiberEquiv_symm i hp p.2

/-- A genuine native local volume frame retains its exact volume in the same actual chart. -/
theorem bundleBiholomorph_localFrame_inCoordinates (i : Threefold.Space)
    (x : Threefold.Canonical.chartSource i) :
    dataInCoordinates (achart Model i) x.val
      (bundleBiholomorph ⟨x.val, Threefold.Canonical.localFrame i x⟩).2 = volume := by
  rw [bundleBiholomorph_mk, dataInCoordinates_fiberEquiv (achart Model i) x.property,
    Threefold.Canonical.localFrame_inCoordinates]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.NativePresentation
