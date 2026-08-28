import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticComparisonDescent
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsPatches

/-!
# The elliptic comparison unit on the actual global patches

The invariant unit descends to the original full filling and is then
restricted through the original patch biholomorphism.  Multiplication by
this unit gives a genuine holomorphic section of the actual global
canonical bundle on the entire elliptic patch, with precisely the zeros
of the previously constructed local canonical section.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticComparison

open Wikipedia.HopfProblem.Elliptic EllipticFilling TrianglePeriodFamily.Canonical

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "Iᴷ" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ Model) (modelWithCornersSelf ℂ ℂ)

attribute [local instance] specialFullFillingChartedSpace specialEllipticPieceChartedSpace
  Threefold.chartedSpace

local instance comparisonPatchGlobalManifold : IsManifold IF ω Threefold.Space :=
  Threefold.space_isManifold

/-- The descended unit on the full, original elliptic patch of the threefold. -/
def patchRatio (j : Kind) (y : Threefold.liftedPatch (some (some j))) : ℂ :=
  fullRatio j ((EllipticGeometry.nativePatchBiholomorph j).symm y).val

@[simp] theorem patchRatio_inclusion (j : Kind) (x : SpecialEllipticPiece j) :
    patchRatio j (EllipticGeometry.nativePatchBiholomorph j x) = fullRatio j x.val := by
  rw [patchRatio, Diffeomorph.symm_apply_apply]

theorem patchRatio_holomorphic (j : Kind) :
    ContMDiff IF 𝓘(ℂ) ω (patchRatio j) :=
  (fullRatio_holomorphic j).comp
    (contMDiff_subtype_val.comp (EllipticGeometry.nativePatchBiholomorph j).symm.contMDiff)

theorem patchRatio_ne_zero (j : Kind) (y : Threefold.liftedPatch (some (some j))) :
    patchRatio j y ≠ 0 :=
  fullRatio_ne_zero j ((EllipticGeometry.nativePatchBiholomorph j).symm y).val

/-- The extended form is a vector in the literal global canonical fibre. -/
def extendedSection (j : Kind) (y : Threefold.liftedPatch (some (some j))) :
    Threefold.Canonical.bundle.Fiber y.val := patchRatio j y • Sections.patchSection j y

def extendedSectionMap (j : Kind) (y : Threefold.liftedPatch (some (some j))) :
    Threefold.Canonical.bundle.TotalSpace := ⟨y.val, extendedSection j y⟩

@[simp] theorem extendedSectionMap_proj (j : Kind)
    (y : Threefold.liftedPatch (some (some j))) : (extendedSectionMap j y).proj = y.val := rfl

theorem extendedSection_inclusion (j : Kind) (x : SpecialEllipticPiece j) :
    extendedSection j (EllipticGeometry.nativePatchBiholomorph j x) =
      fullRatio j x.val • Sections.sectionAlongInclusion j x := by
  rw [extendedSection, patchRatio_inclusion, Sections.patchSection_inclusion]
  rfl

/-- Holomorphicity is proved in the already selected global bundle charts. -/
theorem extendedSectionMap_holomorphic (j : Kind) :
    ContMDiff IF Iᴷ ω (extendedSectionMap j) := by
  intro y
  let i : atlas Model Threefold.Space := achart Model y.val
  have hi : y.val ∈ i.val.source := mem_chart_source Model y.val
  have hs : Sections.patchSectionMap j y ∈
      (Threefold.Canonical.bundle.localTriv i).source := hi
  have he : extendedSectionMap j y ∈
      (Threefold.Canonical.bundle.localTriv i).source := hi
  apply ((Threefold.Canonical.bundle.localTriv i).contMDiffAt_iff he).mpr
  refine ⟨contMDiff_subtype_val y, ?_⟩
  have hc := (((Threefold.Canonical.bundle.localTriv i).contMDiffOn.contMDiffAt
    ((Threefold.Canonical.bundle.localTriv i).open_source.mem_nhds hs)).comp y
      (Sections.patchSectionMap_holomorphic j y)).snd
  apply ((patchRatio_holomorphic j y).smul hc).congr_of_eventuallyEq
  filter_upwards [continuous_subtype_val.continuousAt
    (i.val.open_source.mem_nhds hi)] with z hz
  exact ((Threefold.Canonical.bundle.localTriv i).linear ℂ hz).2
    (patchRatio j z) (Sections.patchSection j z)

/-- A nonvanishing multiplier adds no zeros to the original local section. -/
theorem extendedSection_eq_zero_iff (j : Kind)
    (y : Threefold.liftedPatch (some (some j))) :
    extendedSection j y = 0 ↔ Sections.patchSection j y = 0 := by
  rw [extendedSection, smul_eq_zero]
  exact or_iff_right (patchRatio_ne_zero j y)

theorem extendedSection_zero_support (j : Kind)
    (y : Threefold.liftedPatch (some (some j))) :
    extendedSection j y = 0 ↔ SectionsUnit.vanishingOrder j ≠ 0 ∧
      Threefold.projectionSphere y.val = EllipticGeometry.sphereValue j :=
  (extendedSection_eq_zero_iff j y).trans (Sections.patchSection_eq_zero_iff j y)

theorem extendedSection_three_ne_zero
    (y : Threefold.liftedPatch (some (some .three))) : extendedSection .three y ≠ 0 :=
  fun h => Sections.patchSection_three_ne_zero y ((extendedSection_eq_zero_iff .three y).mp h)

theorem extendedSection_four_eq_zero_iff
    (y : Threefold.liftedPatch (some (some .four))) :
    extendedSection .four y = 0 ↔ Threefold.projectionSphere y.val = ((1 : ℂ) : RiemannSphere) :=
  (extendedSection_eq_zero_iff .four y).trans (Sections.patchSection_four_eq_zero_iff y)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticComparison
