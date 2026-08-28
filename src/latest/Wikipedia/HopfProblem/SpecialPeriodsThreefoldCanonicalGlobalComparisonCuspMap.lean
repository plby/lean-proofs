import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalComparisonCuspFractions
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleOpenMapsFrames

/-!
# The genuine holomorphic divisor-to-canonical map on the full cusp patch

The map sends the actual divisor-line cusp frame to the transported,
regularized canonical frame. It is holomorphic on the entire cusp-patch
preimage in the original bundle total space and has holomorphic inverse
there. On the actual dense generic overlap it sends the prescribed Cartier
section to the original regular canonical form, as follows from the proved
`1/T` and `T` coefficients of these two actual sections.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalComparisonCusp

open CanonicalGlobalLineBundle.OpenMaps

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "IK" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (modelWithCornersSelf ℂ ℂ)

attribute [local instance] Threefold.chartedSpace

local instance cuspMapManifold : IsManifold IF ω Threefold.Space := Threefold.space_isManifold

/-- The unit ratio of the two actual frame values, fixed to one off the cusp patch. -/
def multiplier : Threefold.Space → ℂˣ :=
  frameMultiplier sourceData targetData patch sourceFrame targetFrame
    sourceFrame_ne_zero targetFrame_ne_zero

theorem multiplier_of_not_mem {x : Threefold.Space} (hx : x ∉ patch) : multiplier x = 1 :=
  frameMultiplier_of_notMem sourceData targetData patch sourceFrame targetFrame
    sourceFrame_ne_zero targetFrame_ne_zero hx

/-- The actual preferred-fibre map of the two independently constructed native bundles. -/
def bundleMap : sourceData.core.TotalSpace → targetData.core.TotalSpace :=
  preferredMap sourceData targetData multiplier

/-- Its actual complex-linear equivalence on every original fibre. -/
def fiberMap (x : Threefold.Space) : sourceData.core.Fiber x ≃L[ℂ] targetData.core.Fiber x :=
  fiberEquiv sourceData targetData multiplier x

@[simp] theorem bundleMap_mk (x : Threefold.Space) (v : sourceData.core.Fiber x) :
    bundleMap ⟨x, v⟩ = ⟨x, fiberMap x v⟩ := rfl

@[simp] theorem bundleMap_proj (p : sourceData.core.TotalSpace) :
    (bundleMap p).proj = p.proj := rfl

/-- Holomorphicity concerns the actual bundle total spaces over the entire original cusp open. -/
theorem bundleMap_holomorphicOn :
    ContMDiffOn IK IK ω bundleMap
      ((Bundle.TotalSpace.proj : sourceData.core.TotalSpace → Threefold.Space) ⁻¹'
        (patch : Set Threefold.Space)) :=
  preferredMap_frameMultiplier_holomorphicOn sourceData targetData IF patch sourceFrame targetFrame
    sourceFrame_ne_zero targetFrame_ne_zero
    sourceFrameMap_holomorphicOn targetFrameMap_holomorphicOn

theorem inverseBundleMap_holomorphicOn :
    ContMDiffOn IK IK ω (preferredMap targetData sourceData (fun x => (multiplier x)⁻¹))
      ((Bundle.TotalSpace.proj : targetData.core.TotalSpace → Threefold.Space) ⁻¹'
        (patch : Set Threefold.Space)) :=
  preferredMap_frameMultiplier_inv_holomorphicOn sourceData targetData IF patch
    sourceFrame targetFrame sourceFrame_ne_zero targetFrame_ne_zero
    sourceFrameMap_holomorphicOn targetFrameMap_holomorphicOn

/-- The literal image of the original divisor-line cusp frame is the true canonical frame. -/
theorem bundleMap_frame {x : Threefold.Space} (hx : x ∈ patch) :
    bundleMap (sourceFrameMap x) = targetFrameMap x :=
  preferredMap_frameMultiplier_frame sourceData targetData patch sourceFrame targetFrame
    sourceFrame_ne_zero targetFrame_ne_zero hx

theorem fiberMap_frame {x : Threefold.Space} (hx : x ∈ patch) :
    fiberMap x (sourceFrame x) = targetFrame x :=
  congrArg (fun p : targetData.core.TotalSpace => id (α := ℂ) p.2) (bundleMap_frame hx)

/-- The genuine fibre map sends the actual Cartier section to the
original regular canonical form. -/
theorem fiberMap_rawSection {x : Threefold.Space} (hx : x ∈ patch)
    (hg : x ∈ GlobalPrescribedDivisor.cartier.genericSet) :
    fiberMap x (GlobalPrescribedDivisor.cartier.rawSection x) =
      NativePresentation.fiberEquiv x
        (GlobalRegular.globalSection ⟨x, generic_mem_regular hx hg⟩) := by
  rw [sourceRawSection_eq_inv_smul_frame hx hg, map_smul, fiberMap_frame hx]
  exact inv_smul_targetFrame hx hg

/-- The same statement is an equality in the original native target total space. -/
theorem bundleMap_rawSection {x : Threefold.Space} (hx : x ∈ patch)
    (hg : x ∈ GlobalPrescribedDivisor.cartier.genericSet) :
    bundleMap (GlobalPrescribedDivisor.cartier.rawSectionMap x) =
      NativePresentation.bundleBiholomorph
        (GlobalRegular.globalSectionMap ⟨x, generic_mem_regular hx hg⟩) := by
  exact congrArg (fun v : targetData.core.Fiber x =>
    (⟨x, v⟩ : targetData.core.TotalSpace)) (fiberMap_rawSection hx hg)

/-- Extracted chart units are the true local coefficients of this actual holomorphic map. -/
theorem chartUnit_holomorphicOn (i : GlobalPrescribedDivisor.Index ×
    atlas (ℂ × ComplexPlane₂) Threefold.Space) :
    ContMDiffOn IF (modelWithCornersSelf ℂ ℂ) ω
      (fun x =>
        (CanonicalGlobalLineBundle.OpenMaps.chartUnit sourceData targetData multiplier i x : ℂ))
      ((sourceData.baseSet i.1 ∩ targetData.baseSet i.2) ∩ patch) :=
  CanonicalGlobalLineBundle.OpenMaps.chartUnit_holomorphicOn sourceData targetData multiplier IF
    patch bundleMap_holomorphicOn i

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalComparisonCusp
