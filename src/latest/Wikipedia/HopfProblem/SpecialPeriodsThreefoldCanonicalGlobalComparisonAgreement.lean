import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalComparisonGluing
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalComparisonGeneric
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalComparisonElliptic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalComparisonCusp
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleOpenMapsAgreement

/-!
# Actual agreement of the canonical bundle maps

On each nonempty coarse overlap, both native maps take the same
nonzero Cartier vector to the same actual regular canonical form.
Cancellation in that genuine fibre proves equality of the maps.  Thus
the transition compatibility and holomorphic gluing hypotheses are
discharged by the constructed geometric comparisons, rather than
assumed.  The resulting cross-gauge has no extra hypotheses.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalComparison

open TrianglePeriodFamily.Canonical CanonicalGlobalLineBundle

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "Iκ" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ Model) (modelWithCornersSelf ℂ ℂ)

theorem generic_map_rawSection_regular {x : Threefold.Space}
    (hg : x ∈ cover .generic) (hr : x ∈ regularLocus) :
    GlobalComparisonGeneric.bundleMap (GlobalPrescribedDivisor.cartier.rawSectionMap x) =
      NativePresentation.bundleBiholomorph (GlobalRegular.globalSectionMap ⟨x, hr⟩) := by
  refine (GlobalComparisonGeneric.bundleMap_rawSection x hg).trans ?_
  apply congrArg NativePresentation.bundleBiholomorph
  exact congrArg (fun v : Threefold.Canonical.bundle.Fiber x =>
    (⟨x, v⟩ : Threefold.Canonical.bundle.TotalSpace))
    (GlobalFiniteRegularSection.genericSection_eq_regular ⟨x, hg⟩ hr)

/-- Agreement follows from the actual common image of one nonzero
Cartier vector, including all points in this original overlap. -/
theorem generic_elliptic_multiplier_eq {x : Threefold.Space}
    (hg : x ∈ cover .generic) (he : x ∈ cover .elliptic) :
    GlobalComparisonGeneric.multiplier x = GlobalComparisonElliptic.preferredUnit x := by
  have hr := generic_elliptic_mem_regular hg he
  apply OpenMaps.multiplier_eq_of_image_eq sourceTransitions targetTransitions
    GlobalComparisonGeneric.multiplier GlobalComparisonElliptic.preferredUnit x
    (GlobalPrescribedDivisor.cartier.rawSection x)
    (GlobalPrescribedDivisor.cartier.rawSection_ne_zero hg)
  exact (generic_map_rawSection_regular hg hr).trans
    (GlobalComparisonElliptic.totalMap_rawSection_regular ⟨x, he⟩ hr).symm

/-- The cusp's reciprocal factor is already part of its proved actual
section identity, so this is literal equality of the two original fibre maps. -/
theorem generic_cusp_multiplier_eq {x : Threefold.Space}
    (hg : x ∈ cover .generic) (hc : x ∈ cover .cusp) :
    GlobalComparisonGeneric.multiplier x = GlobalComparisonCusp.multiplier x := by
  have hr := generic_cusp_mem_regular hg hc
  apply OpenMaps.multiplier_eq_of_image_eq sourceTransitions targetTransitions
    GlobalComparisonGeneric.multiplier GlobalComparisonCusp.multiplier x
    (GlobalPrescribedDivisor.cartier.rawSection x)
    (GlobalPrescribedDivisor.cartier.rawSection_ne_zero hg)
  exact (generic_map_rawSection_regular hg hr).trans
    (GlobalComparisonCusp.bundleMap_rawSection hc hg).symm

/-- These are the three constructed native maps, not supplied local data. -/
def localMultiplier : Patch → Threefold.Space → ℂˣ
  | .generic => GlobalComparisonGeneric.multiplier
  | .elliptic => GlobalComparisonElliptic.preferredUnit
  | .cusp => GlobalComparisonCusp.multiplier

theorem localMultiplier_holomorphic (k : Patch) :
    ContMDiffOn Iκ Iκ ω
      (OpenMaps.preferredMap sourceTransitions targetTransitions (localMultiplier k))
      ((Bundle.TotalSpace.proj : sourceTransitions.core.TotalSpace → Threefold.Space) ⁻¹'
        (cover k : Set Threefold.Space)) := by
  cases k with
  | generic => exact GlobalComparisonGeneric.bundleMap_holomorphicOn
  | elliptic => exact GlobalComparisonElliptic.preferredMap_holomorphicOn
  | cusp => exact GlobalComparisonCusp.bundleMap_holomorphicOn

/-- Every coarse overlap is accounted for.  The two full filling patches
are disjoint, and the other agreements were proved using the actual form. -/
theorem localMultiplier_agreement (k l : Patch) (x : Threefold.Space)
    (hk : x ∈ cover k) (hl : x ∈ cover l) : localMultiplier k x = localMultiplier l x := by
  cases k <;> cases l
  · rfl
  · exact generic_elliptic_multiplier_eq hk hl
  · exact generic_cusp_multiplier_eq hk hl
  · exact (generic_elliptic_multiplier_eq hl hk).symm
  · rfl
  · exact (Set.disjoint_left.mp elliptic_cusp_disjoint hk hl).elim
  · exact (generic_cusp_multiplier_eq hl hk).symm
  · exact (Set.disjoint_left.mp elliptic_cusp_disjoint hl hk).elim
  · rfl

/-- An actual local cross-gauge, with every geometric compatibility proved. -/
def localGauge : LocalCrossGauge IF sourceTransitions targetTransitions Patch :=
  glueLocalMaps localMultiplier localMultiplier_holomorphic localMultiplier_agreement

/-- The global holomorphic comparison of the original two unit cocycles. -/
def globalGauge : CrossGauge IF sourceTransitions targetTransitions := localGauge.toCrossGauge

theorem globalGauge_fiberEquiv_apply (k : Patch) {x : Threefold.Space}
    (hx : x ∈ cover k) (v : sourceTransitions.core.Fiber x) :
    globalGauge.fiberEquiv x v = (localMultiplier k x : ℂ) * id (α := ℂ) v :=
  glueLocalMaps_fiberEquiv_apply localMultiplier localMultiplier_holomorphic
    localMultiplier_agreement k hx v

/-- The true global biholomorphism restricts to each independently
constructed local native bundle map on its entire original coarse patch. -/
theorem globalGauge_diffeomorph_eq (k : Patch) (p : sourceTransitions.core.TotalSpace)
    (hp : p.proj ∈ cover k) :
    globalGauge.diffeomorph p =
      OpenMaps.preferredMap sourceTransitions targetTransitions (localMultiplier k) p :=
  glueLocalMaps_diffeomorph_eq localMultiplier localMultiplier_holomorphic
    localMultiplier_agreement k p hp

/-- The global map sends the actual Cartier section to the genuine
canonical form on the whole dense generic open, including the first elliptic fibre. -/
theorem globalGauge_rawSection {x : Threefold.Space} (hx : x ∈ cover .generic) :
    globalGauge.diffeomorph (GlobalPrescribedDivisor.cartier.rawSectionMap x) =
      NativePresentation.bundleBiholomorph
        (GlobalFiniteRegularSection.genericSectionMap ⟨x, hx⟩) :=
  (globalGauge_diffeomorph_eq .generic _ hx).trans
    (GlobalComparisonGeneric.bundleMap_rawSection x hx)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalComparison
