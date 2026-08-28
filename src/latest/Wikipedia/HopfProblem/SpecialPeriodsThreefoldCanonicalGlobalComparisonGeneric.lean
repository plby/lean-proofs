import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalComparisonGenericSections
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleOpenMapsFrames

/-!
# The genuine divisor-to-canonical comparison on the generic open

The actual nonzero meromorphic divisor section is sent to the actual
canonical form on exactly the prescribed generic open.  Their preferred
fibre ratio defines a unit multiplier, extended by one outside that open.
Holomorphicity of the native total-space map follows from the two actual
holomorphic frames, and not from an assumption on preferred coordinates.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalComparisonGeneric

open TrianglePeriodFamily.Canonical
open CanonicalGlobalLineBundle.OpenMaps

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "Iᴷ" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ Model) (modelWithCornersSelf ℂ ℂ)

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- The actual frame ratio on the exact generic open, with unit value one elsewhere. -/
def multiplier : Threefold.Space → ℂˣ :=
  frameMultiplier sourceData targetData domain GlobalPrescribedDivisor.cartier.rawSection
    targetSection sourceSection_ne_zero targetSection_ne_zero

theorem multiplier_ne_zero (x : Threefold.Space) : (multiplier x : ℂ) ≠ 0 :=
  (multiplier x).ne_zero

theorem multiplier_of_notMem (x : Threefold.Space) (hx : x ∉ domain) : multiplier x = 1 :=
  frameMultiplier_of_notMem sourceData targetData domain
    GlobalPrescribedDivisor.cartier.rawSection targetSection
      sourceSection_ne_zero targetSection_ne_zero hx

/-- The preferred scalar is the quotient of the two actual native fibre values. -/
theorem multiplier_val (x : Threefold.Space) (hx : x ∈ domain) :
    (multiplier x : ℂ) =
      id (α := ℂ) (NativePresentation.fiberEquiv x
        (GlobalFiniteRegularSection.genericSection ⟨x, hx⟩)) /
          id (α := ℂ) (GlobalPrescribedDivisor.cartier.rawSection x) :=
  (frameMultiplier_val sourceData targetData domain
    GlobalPrescribedDivisor.cartier.rawSection targetSection
      sourceSection_ne_zero targetSection_ne_zero hx).trans
        (congrArg (fun v : targetData.core.Fiber x =>
          id (α := ℂ) v / id (α := ℂ) (GlobalPrescribedDivisor.cartier.rawSection x))
            (targetSection_eq x hx))

/-- Literal fibre multiplication sends the original divisor vector to
the actual canonical vector, transported by the proved native equivalence. -/
theorem multiplier_mul_rawSection (x : Threefold.Space) (hx : x ∈ domain) :
    (multiplier x : ℂ) * id (α := ℂ) (GlobalPrescribedDivisor.cartier.rawSection x) =
      id (α := ℂ) (NativePresentation.fiberEquiv x
        (GlobalFiniteRegularSection.genericSection ⟨x, hx⟩)) := by
  rw [multiplier_val x hx]
  exact div_mul_cancel₀ _ (sourceSection_ne_zero x hx)

/-- The native base-preserving, fibrewise complex-linear bundle map. -/
def bundleMap : sourceData.core.TotalSpace → targetData.core.TotalSpace :=
  preferredMap sourceData targetData multiplier

@[simp] theorem bundleMap_proj (p : sourceData.core.TotalSpace) :
    (bundleMap p).proj = p.proj := rfl

def bundleFiberEquiv (x : Threefold.Space) :
    sourceData.core.Fiber x ≃L[ℂ] targetData.core.Fiber x :=
  CanonicalGlobalLineBundle.OpenMaps.fiberEquiv sourceData targetData multiplier x

theorem bundleMap_fiberEquiv (x : Threefold.Space) (v : sourceData.core.Fiber x) :
    bundleMap ⟨x, v⟩ = ⟨x, bundleFiberEquiv x v⟩ := rfl

/-- Exact equality of actual native total-space points on the source frame. -/
theorem bundleMap_rawSection (x : Threefold.Space) (hx : x ∈ domain) :
    bundleMap (GlobalPrescribedDivisor.cartier.rawSectionMap x) =
      NativePresentation.bundleBiholomorph
        (GlobalFiniteRegularSection.genericSectionMap ⟨x, hx⟩) :=
  (preferredMap_frameMultiplier_frame sourceData targetData domain
    GlobalPrescribedDivisor.cartier.rawSection targetSection
      sourceSection_ne_zero targetSection_ne_zero hx).trans
        (targetSectionMap_on_domain ⟨x, hx⟩)

/-- Holomorphicity is in the original total-space atlases over the entire exact open. -/
theorem bundleMap_holomorphicOn :
    ContMDiffOn Iᴷ Iᴷ ω bundleMap
      ((Bundle.TotalSpace.proj : sourceData.core.TotalSpace → Threefold.Space) ⁻¹'
        (domain : Set Threefold.Space)) :=
  preferredMap_frameMultiplier_holomorphicOn sourceData targetData IF domain
    GlobalPrescribedDivisor.cartier.rawSection targetSection
      sourceSection_ne_zero targetSection_ne_zero
        sourceSectionMap_holomorphicOn targetSectionMap_holomorphicOn

/-- The inverse fibrewise map is holomorphic on the same native open. -/
theorem inverseBundleMap_holomorphicOn :
    ContMDiffOn Iᴷ Iᴷ ω (preferredMap targetData sourceData (fun x => (multiplier x)⁻¹))
      ((Bundle.TotalSpace.proj : targetData.core.TotalSpace → Threefold.Space) ⁻¹'
        (domain : Set Threefold.Space)) :=
  preferredMap_frameMultiplier_inv_holomorphicOn sourceData targetData IF domain
    GlobalPrescribedDivisor.cartier.rawSection targetSection
      sourceSection_ne_zero targetSection_ne_zero
        sourceSectionMap_holomorphicOn targetSectionMap_holomorphicOn

/-- All actual chart-pair gauge coefficients are holomorphic on the corresponding
original intersections with the generic open. -/
theorem chartUnit_holomorphicOn
    (i : GlobalPrescribedDivisor.Index × atlas Model Threefold.Space) :
    ContMDiffOn IF 𝓘(ℂ) ω (fun x => (chartUnit sourceData targetData multiplier i x : ℂ))
      ((sourceData.baseSet i.1 ∩ targetData.baseSet i.2) ∩ domain) :=
  CanonicalGlobalLineBundle.OpenMaps.chartUnit_holomorphicOn
    sourceData targetData multiplier IF domain bundleMap_holomorphicOn i

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalComparisonGeneric
