import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalCuspBiholomorph
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Scalar multiples of the genuine cusp canonical section

A holomorphic scalar on the original native cusp multiplies its signed toric
volume to a holomorphic section of the original native canonical bundle.
The actual inverse cotangent map carries this section into the original
threefold canonical bundle, and the actual cusp-patch biholomorphism supplies
the corresponding section over the entire global cusp patch.

The constructions themselves use an arbitrary scalar function.  Their
holomorphicity and nonvanishing are proved separately, so they can be applied
to the explicitly constructed extension unit without changing either bundle
or either manifold atlas.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspExtension

open ToricCharts CuspGeometry

local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] CuspGeometry.nativeChartedSpace Threefold.chartedSpace

local instance scaledNativeManifold : IsManifold I₃ ω LocalSpace := native_isManifold
local instance scaledGlobalManifold : IsManifold IF ω Threefold.Space :=
  Threefold.space_isManifold

variable (r : LocalSpace → ℂ)

/-- Scalar multiple in the actual native canonical fibre. -/
def scaledNativeVolume (x : LocalSpace) : Cusp.nativeBundle.Fiber x :=
  r x • Cusp.nativeVolume x

/-- Its total-space map, with the unchanged native bundle topology and atlas. -/
def scaledNativeVolumeSection (x : LocalSpace) : Cusp.nativeBundle.TotalSpace :=
  ⟨x, scaledNativeVolume r x⟩

@[simp] theorem scaledNativeVolumeSection_proj (x : LocalSpace) :
    (scaledNativeVolumeSection r x).proj = x := rfl

theorem scaledNativeVolume_ne_zero_iff (x : LocalSpace) :
    scaledNativeVolume r x ≠ 0 ↔ r x ≠ 0 := by
  simp only [scaledNativeVolume, ne_eq, smul_eq_zero,
    Cusp.nativeVolume_ne_zero x, or_false]

theorem scaledNativeVolume_ne_zero (hr : ∀ x, r x ≠ 0) (x : LocalSpace) :
    scaledNativeVolume r x ≠ 0 :=
  (scaledNativeVolume_ne_zero_iff r x).mpr (hr x)

/-- Multiplication preserves holomorphicity in the original native bundle. -/
theorem scaledNativeVolumeSection_holomorphic (hr : ContMDiff I₃ I₁ ω r) :
    ContMDiff I₃ ((I₃).prod I₁) ω (scaledNativeVolumeSection r) :=
  hr.smul_section Cusp.nativeVolume_holomorphic

/-- The scaled section in the original global canonical fibre along the cusp inclusion. -/
def scaledVolumeAlongInclusion (x : LocalSpace) : bundle.Fiber (CuspGeometry.inclusion x) :=
  r x • Cusp.volumeAlongInclusion x

/-- Its map into the actual global canonical total space. -/
def scaledVolumeAlongInclusionSection (x : LocalSpace) : bundle.TotalSpace :=
  ⟨CuspGeometry.inclusion x, scaledVolumeAlongInclusion r x⟩

@[simp] theorem scaledVolumeAlongInclusionSection_proj (x : LocalSpace) :
    (scaledVolumeAlongInclusionSection r x).proj = CuspGeometry.inclusion x := rfl

theorem scaledVolumeAlongInclusion_ne_zero_iff (x : LocalSpace) :
    scaledVolumeAlongInclusion r x ≠ 0 ↔ r x ≠ 0 := by
  simp only [scaledVolumeAlongInclusion, ne_eq, smul_eq_zero,
    Cusp.volumeAlongInclusion_ne_zero x, or_false]

theorem scaledVolumeAlongInclusion_ne_zero (hr : ∀ x, r x ≠ 0) (x : LocalSpace) :
    scaledVolumeAlongInclusion r x ≠ 0 :=
  (scaledVolumeAlongInclusion_ne_zero_iff r x).mpr (hr x)

/-- The actual cotangent pullback recovers the scaled native section. -/
@[simp] theorem inclusionPullback_scaledVolumeAlongInclusion (x : LocalSpace) :
    Cusp.inclusionPullback x (scaledVolumeAlongInclusion r x) = scaledNativeVolume r x := by
  rw [scaledVolumeAlongInclusion, map_smul, Cusp.inclusionPullback_volumeAlongInclusion]
  rfl

/-- Compatibility in the genuine bundle total spaces, not just in scalar coordinates. -/
@[simp] theorem nativeForwardMap_scaledNativeVolumeSection (x : LocalSpace) :
    Cusp.nativeForwardMap (scaledNativeVolumeSection r x) =
      scaledVolumeAlongInclusionSection r x := by
  exact congrArg (fun v : bundle.Fiber (CuspGeometry.inclusion x) =>
    (⟨CuspGeometry.inclusion x, v⟩ : bundle.TotalSpace))
      (map_smul (Cusp.inclusionPullback x).symm (r x) (Cusp.nativeVolume x))

/-- The native-to-global comparison remains the existing full-patch bundle biholomorphism. -/
@[simp] theorem nativePatchTotalBiholomorph_scaledNativeVolumeSection (x : LocalSpace) :
    (Cusp.nativePatchTotalBiholomorph (scaledNativeVolumeSection r x)).val =
      scaledVolumeAlongInclusionSection r x :=
  nativeForwardMap_scaledNativeVolumeSection r x

/-- Holomorphicity is transported by the already proved actual cotangent map. -/
theorem scaledVolumeAlongInclusionSection_holomorphic (hr : ContMDiff I₃ I₁ ω r) :
    ContMDiff I₃ ((IF).prod I₁) ω (scaledVolumeAlongInclusionSection r) := by
  have h : scaledVolumeAlongInclusionSection r =
      Cusp.nativeForwardMap ∘ scaledNativeVolumeSection r :=
    funext fun x => (nativeForwardMap_scaledNativeVolumeSection r x).symm
  rw [h]
  exact Cusp.nativeForwardMap_holomorphic.comp (scaledNativeVolumeSection_holomorphic r hr)

/-- The section in the actual global canonical fibre over the entire cusp patch. -/
def scaledPatchVolume (y : Threefold.liftedPatch (some none)) : bundle.Fiber y.val :=
  r (nativePatchBiholomorph.symm y) • Cusp.patchVolume y

/-- Its map into the unchanged global bundle, using the inherited full-patch atlas. -/
def scaledPatchVolumeSection (y : Threefold.liftedPatch (some none)) : bundle.TotalSpace :=
  ⟨y.val, scaledPatchVolume r y⟩

@[simp] theorem scaledPatchVolumeSection_proj (y : Threefold.liftedPatch (some none)) :
    (scaledPatchVolumeSection r y).proj = y.val := rfl

theorem scaledPatchVolume_ne_zero_iff (y : Threefold.liftedPatch (some none)) :
    scaledPatchVolume r y ≠ 0 ↔ r (nativePatchBiholomorph.symm y) ≠ 0 := by
  simp only [scaledPatchVolume, ne_eq, smul_eq_zero, Cusp.patchVolume_ne_zero y, or_false]

theorem scaledPatchVolume_ne_zero (hr : ∀ x, r x ≠ 0)
    (y : Threefold.liftedPatch (some none)) : scaledPatchVolume r y ≠ 0 :=
  (scaledPatchVolume_ne_zero_iff r y).mpr (hr _)

/-- Restricting the full-patch section along the actual inclusion gives exactly the same form. -/
@[simp] theorem scaledPatchVolume_inclusion (x : LocalSpace) :
    scaledPatchVolume r (nativePatchBiholomorph x) = scaledVolumeAlongInclusion r x := by
  simp only [scaledPatchVolume, nativePatchBiholomorph.symm_apply_apply,
    Cusp.patchVolume_inclusion, scaledVolumeAlongInclusion]
  rfl

/-- The global patch and native constructions agree as maps into the genuine total space. -/
theorem scaledPatchVolumeSection_eq_transport (y : Threefold.liftedPatch (some none)) :
    scaledPatchVolumeSection r y =
      scaledVolumeAlongInclusionSection r (nativePatchBiholomorph.symm y) := by
  apply Bundle.TotalSpace.ext
    (congrArg Subtype.val (nativePatchBiholomorph.apply_symm_apply y)).symm
  rfl

@[simp] theorem scaledPatchVolumeSection_inclusion (x : LocalSpace) :
    scaledPatchVolumeSection r (nativePatchBiholomorph x) =
      scaledVolumeAlongInclusionSection r x := by
  rw [scaledPatchVolumeSection_eq_transport, nativePatchBiholomorph.symm_apply_apply]

/-- The scaled section is holomorphic on the entire actual global cusp patch. -/
theorem scaledPatchVolumeSection_holomorphic (hr : ContMDiff I₃ I₁ ω r) :
    ContMDiff IF ((IF).prod I₁) ω (scaledPatchVolumeSection r) := by
  have h : scaledPatchVolumeSection r =
      scaledVolumeAlongInclusionSection r ∘ nativePatchBiholomorph.symm :=
    funext (scaledPatchVolumeSection_eq_transport r)
  rw [h]
  exact (scaledVolumeAlongInclusionSection_holomorphic r hr).comp
    nativePatchBiholomorph.symm.contMDiff

/-- The native intrinsic form retains the signed toric coefficient. -/
theorem scaledNativeVolume_intrinsic (x : LocalSpace) :
    Cusp.nativeIntrinsicEquiv x (scaledNativeVolume r x) =
      (r x * Cusp.nativeVolumeCoefficient x) • CanonicalBundle.volume := by
  rw [scaledNativeVolume, map_smul, Cusp.nativeIntrinsicEquiv_volume]
  exact smul_smul (r x) (Cusp.nativeVolumeCoefficient x) CanonicalBundle.volume

/-- Pullback uses the actual manifold differential of the actual cusp inclusion. -/
theorem scaledVolumeAlongInclusion_pullback (x : LocalSpace) :
    (intrinsicEquiv (CuspGeometry.inclusion x)
      (scaledVolumeAlongInclusion r x)).compContinuousLinearMap
        (mfderiv I₃ IF CuspGeometry.inclusion x) =
      (r x * Cusp.nativeVolumeCoefficient x) • CanonicalBundle.volume := by
  rw [← Cusp.inclusionPullback_intrinsic, inclusionPullback_scaledVolumeAlongInclusion,
    scaledNativeVolume_intrinsic]

/-- The full-patch section satisfies the same genuine intrinsic pullback identity. -/
theorem scaledPatchVolume_pullback (x : LocalSpace) :
    (intrinsicEquiv (CuspGeometry.inclusion x)
      (scaledPatchVolume r (nativePatchBiholomorph x))).compContinuousLinearMap
        (mfderiv I₃ IF CuspGeometry.inclusion x) =
      (r x * Cusp.nativeVolumeCoefficient x) • CanonicalBundle.volume := by
  rw [scaledPatchVolume_inclusion]
  exact scaledVolumeAlongInclusion_pullback r x

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspExtension
