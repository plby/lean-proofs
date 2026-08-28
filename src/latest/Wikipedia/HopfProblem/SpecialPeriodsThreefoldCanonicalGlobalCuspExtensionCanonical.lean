import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCuspExtensionUnit
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCuspExtensionSection

/-!
# The actual regularized canonical section over the full cusp patch

The constructed holomorphic unit multiplies the original signed cusp
volume. This gives a nowhere-zero section of the genuine canonical bundle
on the entire cusp neighborhood. On its full regular overlap it equals
the original regular canonical section multiplied by the literal reciprocal
sphere coordinate. The agreement is proved in the actual bundle total
space, as well as in each canonical fibre.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspExtension

open ToricCharts CuspGeometry

local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] CuspGeometry.nativeChartedSpace Threefold.chartedSpace

local instance filledNativeManifold : IsManifold I₃ ω LocalSpace := native_isManifold
local instance filledGlobalManifold : IsManifold IF ω Threefold.Space := Threefold.space_isManifold

/-- The regularized section of the original native cusp canonical bundle. -/
def filledNativeSection (x : LocalSpace) : Cusp.nativeBundle.Fiber x :=
  scaledNativeVolume extensionUnit x

def filledNativeSectionMap : LocalSpace → Cusp.nativeBundle.TotalSpace :=
  scaledNativeVolumeSection extensionUnit

theorem filledNativeSectionMap_holomorphic :
    ContMDiff I₃ ((I₃).prod I₁) ω filledNativeSectionMap :=
  scaledNativeVolumeSection_holomorphic extensionUnit extensionUnit_holomorphic

theorem filledNativeSection_ne_zero (x : LocalSpace) : filledNativeSection x ≠ 0 :=
  scaledNativeVolume_ne_zero extensionUnit extensionUnit_ne_zero x

/-- The regularized section in the genuine global canonical bundle along the actual inclusion. -/
def filledAlongSection (x : LocalSpace) : bundle.Fiber (CuspGeometry.inclusion x) :=
  scaledVolumeAlongInclusion extensionUnit x

def filledAlongSectionMap : LocalSpace → bundle.TotalSpace :=
  scaledVolumeAlongInclusionSection extensionUnit

theorem filledAlongSectionMap_holomorphic :
    ContMDiff I₃ ((IF).prod I₁) ω filledAlongSectionMap :=
  scaledVolumeAlongInclusionSection_holomorphic extensionUnit extensionUnit_holomorphic

/-- The exact normalized-section identity on the entire native punctured cusp. -/
theorem filledAlongSection_overlap (x : puncturedNative) :
    filledAlongSection x.val =
      reciprocalParameter x • GlobalRegular.globalSection (puncturedRegularPoint x) := by
  change extensionUnit x.val • Cusp.volumeAlongInclusion x.val = _
  rw [extensionUnit_punctured]
  exact (reciprocal_smul_globalSection x).symm

/-- The actual nowhere-zero canonical section on the full global cusp neighborhood. -/
def canonicalSection (y : FullCuspPatch) : bundle.Fiber y.val :=
  scaledPatchVolume extensionUnit y

def canonicalSectionMap : FullCuspPatch → bundle.TotalSpace :=
  scaledPatchVolumeSection extensionUnit

@[simp] theorem canonicalSectionMap_proj (y : FullCuspPatch) :
    (canonicalSectionMap y).proj = y.val := rfl

/-- Holomorphicity is for the original global canonical total space and full inherited patch. -/
theorem canonicalSectionMap_holomorphic :
    ContMDiff IF ((IF).prod I₁) ω canonicalSectionMap :=
  scaledPatchVolumeSection_holomorphic extensionUnit extensionUnit_holomorphic

theorem canonicalSection_ne_zero (y : FullCuspPatch) : canonicalSection y ≠ 0 :=
  scaledPatchVolume_ne_zero extensionUnit extensionUnit_ne_zero y

/-- Its coefficient relative to the original full-patch cusp volume is
the constructed unit. -/
theorem canonicalSection_eq_patchUnit_smul (y : FullCuspPatch) :
    canonicalSection y = patchUnit y • Cusp.patchVolume y := rfl

/-- Actual total-space agreement over every point of the full regular/cusp overlap. -/
theorem canonicalSectionMap_overlap (y : FullCuspPatch) (hy : y.val ∈ regularLocus) :
    canonicalSectionMap y =
      (⟨y.val, patchReciprocal y • GlobalRegular.globalSection ⟨y.val, hy⟩⟩ :
        bundle.TotalSpace) := by
  let x := regularPatchPoint y hy
  have hp : puncturedRegularPoint x = ⟨y.val, hy⟩ :=
    puncturedRegularPoint_regularPatchPoint y hy
  calc
    canonicalSectionMap y = filledAlongSectionMap x.val :=
      scaledPatchVolumeSection_eq_transport extensionUnit y
    _ = (⟨CuspGeometry.inclusion x.val,
        reciprocalParameter x • GlobalRegular.globalSection (puncturedRegularPoint x)⟩ :
          bundle.TotalSpace) :=
      congrArg (fun v : bundle.Fiber (CuspGeometry.inclusion x.val) =>
        (⟨CuspGeometry.inclusion x.val, v⟩ : bundle.TotalSpace)) (filledAlongSection_overlap x)
    _ = _ :=
      congrArg (fun z : regularLocus =>
        (⟨z.val, GlobalCusp.reciprocalCoordinate (Threefold.projectionSphere z.val) •
          GlobalRegular.globalSection z⟩ : bundle.TotalSpace)) hp

/-- In the original canonical fibre, the regularized section is exactly `t⁻¹ Ω`. -/
theorem canonicalSection_overlap (y : FullCuspPatch) (hy : y.val ∈ regularLocus) :
    canonicalSection y =
      patchReciprocal y • GlobalRegular.globalSection ⟨y.val, hy⟩ :=
  congrArg (fun p : bundle.TotalSpace => id (α := ℂ) p.2) (canonicalSectionMap_overlap y hy)

/-- Equivalently, the original regular form is one reciprocal-coordinate
pole times this unit frame. -/
theorem globalSection_eq_reciprocal_inv_smul (y : FullCuspPatch)
    (hy : y.val ∈ regularLocus) :
    GlobalRegular.globalSection ⟨y.val, hy⟩ =
      (patchReciprocal y)⁻¹ • canonicalSection y := by
  have hw : patchReciprocal y ≠ 0 := fun h =>
    (patch_mem_regular_iff y).mp hy ((patchReciprocal_eq_zero_iff y).mp h)
  have he : id (α := ℂ) (canonicalSection y) =
      patchReciprocal y * id (α := ℂ) (GlobalRegular.globalSection ⟨y.val, hy⟩) :=
    canonicalSection_overlap y hy
  change id (α := ℂ) (GlobalRegular.globalSection ⟨y.val, hy⟩) =
    (patchReciprocal y)⁻¹ * id (α := ℂ) (canonicalSection y)
  rw [he, ← mul_assoc, inv_mul_cancel₀ hw, one_mul]

/-- The intrinsic section retains the true signed toric pullback coefficient. -/
theorem canonicalSection_intrinsic_pullback (x : LocalSpace) :
    (intrinsicEquiv (CuspGeometry.inclusion x)
      (canonicalSection (nativePatchBiholomorph x))).compContinuousLinearMap
        (mfderiv I₃ IF CuspGeometry.inclusion x) =
      (extensionUnit x * Cusp.nativeVolumeCoefficient x) • CanonicalBundle.volume :=
  scaledPatchVolume_pullback extensionUnit x

/-- On every central stratum the coefficient is the same computed nonzero analytic value. -/
theorem canonicalSection_central {y : FullCuspPatch} (hy : patchParameter y = 0) :
    canonicalSection y = regularizingGerm 0 • Cusp.patchVolume y := by
  rw [canonicalSection_eq_patchUnit_smul, patchUnit_central hy]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspExtension
