import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalPrescribedDivisorOrders
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalNativeCanonical
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCuspExtension
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleOpenMaps

/-!
# The two actual line-bundle frames on the full cusp neighborhood

The source frame is the actual `(infinity, outside S2)` chart frame of
the independently constructed tensor divisor line. The target frame is
the proved nowhere-zero regularized canonical section, transported by
the genuine native canonical-bundle biholomorphism. Both are holomorphic
on the full original cusp patch; no regularity is imposed outside it.
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

local instance comparisonManifold : IsManifold IF ω Threefold.Space :=
  Threefold.space_isManifold

/-- The independently constructed actual tensor divisor cocycle. -/
abbrev sourceData := GlobalPrescribedDivisor.cartier.transitions

/-- The actual native reverse-Jacobian canonical cocycle. -/
abbrev targetData := NativePresentation.transitionData

/-- The whole original cusp patch, including all central strata. -/
abbrev patch : TopologicalSpace.Opens Threefold.Space := Threefold.liftedPatch (some none)

/-- The literal source chart frame of the actual divisor line. -/
def sourceFrame (x : Threefold.Space) : sourceData.core.Fiber x :=
  CanonicalGlobalLineBundle.OpenMaps.localFrame sourceData (true, none) x

def sourceFrameMap (x : Threefold.Space) : sourceData.core.TotalSpace := ⟨x, sourceFrame x⟩

theorem sourceFrame_localCoefficient {x : Threefold.Space} (hx : x ∈ patch) :
    (sourceData.core.localTriv (true, none) (sourceFrameMap x)).2 = 1 :=
  congrArg Prod.snd (localFrame_localTriv sourceData (true, none)
    (GlobalPrescribedDivisor.cuspPatch_subset_baseSet hx))

theorem sourceFrame_ne_zero (x : Threefold.Space) (hx : x ∈ patch) : sourceFrame x ≠ 0 := by
  change id (α := ℂ)
    (CanonicalGlobalLineBundle.OpenMaps.localFrame sourceData (true, none) x) ≠ 0
  rw [localFrame_preferred sourceData (true, none)
    (GlobalPrescribedDivisor.cuspPatch_subset_baseSet hx)]
  exact sourceData.transition_ne_zero _ _ _

theorem sourceFrameMap_holomorphicOn : ContMDiffOn IF IK ω sourceFrameMap patch :=
  (localFrameMap_holomorphicOn sourceData IF (true, none)).mono
    GlobalPrescribedDivisor.cuspPatch_subset_baseSet

/-- The actual regularized canonical frame, in the independently presented native bundle.
Its off-patch value is irrelevant and fixed to zero. -/
def targetFrame (x : Threefold.Space) : targetData.core.Fiber x := by
  classical
  exact if hx : x ∈ patch then
    NativePresentation.fiberEquiv x (GlobalCuspExtension.canonicalSection ⟨x, hx⟩)
  else 0

def targetFrameMap (x : Threefold.Space) : targetData.core.TotalSpace := ⟨x, targetFrame x⟩

theorem targetFrame_of_mem {x : Threefold.Space} (hx : x ∈ patch) :
    targetFrame x =
      NativePresentation.fiberEquiv x (GlobalCuspExtension.canonicalSection ⟨x, hx⟩) := by
  simp only [targetFrame, dif_pos hx]

theorem targetFrame_of_not_mem {x : Threefold.Space} (hx : x ∉ patch) : targetFrame x = 0 := by
  simp only [targetFrame, dif_neg hx]

theorem targetFrame_ne_zero (x : Threefold.Space) (hx : x ∈ patch) : targetFrame x ≠ 0 := by
  rw [targetFrame_of_mem hx]
  intro h
  exact GlobalCuspExtension.canonicalSection_ne_zero ⟨x, hx⟩
    ((NativePresentation.fiberEquiv x).injective (h.trans (map_zero _).symm))

/-- This is an equality of maps into the original target bundle total space. -/
theorem targetFrameMap_on_patch (x : patch) :
    targetFrameMap x.val =
      NativePresentation.bundleBiholomorph (GlobalCuspExtension.canonicalSectionMap x) := by
  change (⟨x.val, targetFrame x.val⟩ : targetData.core.TotalSpace) =
    ⟨x.val, NativePresentation.fiberEquiv x.val (GlobalCuspExtension.canonicalSection x)⟩
  exact congrArg (fun v : targetData.core.Fiber x.val =>
    (⟨x.val, v⟩ : targetData.core.TotalSpace)) (targetFrame_of_mem x.property)

theorem targetFrameMap_holomorphicOn : ContMDiffOn IF IK ω targetFrameMap patch := by
  have hsub : ContMDiff IF IK ω (fun x : patch => targetFrameMap x.val) := by
    have he : (fun x : patch => targetFrameMap x.val) =
        NativePresentation.bundleBiholomorph ∘ GlobalCuspExtension.canonicalSectionMap :=
      funext targetFrameMap_on_patch
    rw [he]
    exact NativePresentation.bundleBiholomorph.contMDiff.comp
      GlobalCuspExtension.canonicalSectionMap_holomorphic
  intro x hx
  have ht : ContMDiffAt IF IK ω targetFrameMap x :=
    contMDiffAt_subtype_iff.mp (hsub ⟨x, hx⟩)
  exact ht.contMDiffWithinAt

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalComparisonCusp
