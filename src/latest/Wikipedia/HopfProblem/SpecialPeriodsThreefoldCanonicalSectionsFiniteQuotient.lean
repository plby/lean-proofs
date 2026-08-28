import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsInvariance
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsDescentAction
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsQuotientCharts

/-!
# Actual canonical sections on the ambient elliptic fillings

The corrected genuine upstairs three-form descends through the actual
finite free quotient.  The resulting section is holomorphic for the
native tangent-canonical bundle of the full filling, and pulling it back
by the actual quotient differential recovers the original form.  Its
zero set is exactly the reduced central support in the order-four case
and is empty in the order-three case.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.Elliptic.Equivariant.Data.CanonicalSections

open SpecialPeriods TrianglePeriodFamily.Canonical SpecialPeriods.Threefold.Canonical

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₃" => modelWithCornersSelf ℂ Model

variable {j : Kind} (D : Equivariant.Data j) (v : Lattice) (hv : AdmissibleTwist j v)

local instance quotientSectionsFamilyChartedSpace : ChartedSpace Model D.TotalSpace :=
  D.periods.totalChartedSpace

local instance quotientSectionsFamilyManifold : IsManifold I₃ ω D.TotalSpace :=
  D.periods.totalSpace_isManifold

local instance quotientSectionsChartedSpace : ChartedSpace Model (D.Space v hv) :=
  D.chartedSpace v hv

local instance quotientSectionsManifold : IsManifold I₃ ω (D.Space v hv) :=
  D.isManifold v hv

/-- Invariance under the actual group action gives genuine fibre
compatibility for the actual unramified quotient. -/
theorem quotientCompatible :
    SectionsDescent.Compatible (CanonicalQuotientCharts.quotient_isLocalDiffeomorph D v hv)
      (upstairsSection D) := by
  let := D.action v hv.1
  apply SectionsDescent.compatible_of_action_invariant
    (CanonicalQuotientCharts.quotient_isLocalDiffeomorph D v hv)
    (fun g => (D.actionBiholomorph v hv.1 g).isLocalDiffeomorph)
    (D.quotient_smul v hv)
  · intro x y hxy
    have hy : y ∈ MulAction.orbit (CyclicGroup j) x :=
      (D.quotient_eq_iff_mem_orbit v hv y x).mp hxy.symm
    exact hy
  · exact action_pullbackEquiv D v hv.1

/-- The native ambient tangent-canonical bundle on the actual finite quotient. -/
abbrev quotientBundle := Atlas.core (D.Space v hv)

/-- The actual descended canonical section, defined through genuine
inverse differential pullback and equality transport on fibres. -/
def quotientSection (y : D.Space v hv) : (quotientBundle D v hv).Fiber y :=
  SectionsDescent.descendedSection
    (CanonicalQuotientCharts.quotient_isLocalDiffeomorph D v hv)
    (D.quotient_surjective v hv) (upstairsSection D) y

def quotientSectionMap (y : D.Space v hv) : (quotientBundle D v hv).TotalSpace :=
  ⟨y, quotientSection D v hv y⟩

@[simp] theorem quotientSectionMap_proj (y : D.Space v hv) :
    (quotientSectionMap D v hv y).proj = y := rfl

theorem quotientSectionMap_holomorphic :
    ContMDiff I₃ ((I₃).prod I₁) ω (quotientSectionMap D v hv) :=
  SectionsDescent.descendedSection_holomorphic
    (CanonicalQuotientCharts.quotient_isLocalDiffeomorph D v hv)
    (D.quotient_surjective v hv) (upstairsSection D) (quotientCompatible D v hv)
    (upstairsSectionMap_holomorphic D)

def quotientHolomorphicSection :
    ContMDiffSection I₃ ℂ ω (quotientBundle D v hv).Fiber where
  toFun := quotientSection D v hv
  contMDiff_toFun := quotientSectionMap_holomorphic D v hv

@[simp] theorem quotientHolomorphicSection_apply (y : D.Space v hv) :
    quotientHolomorphicSection D v hv y = quotientSection D v hv y := rfl

/-- Exact recovery of the genuine upstairs form by the actual quotient differential. -/
theorem quotientSection_pullback (x : D.TotalSpace) :
    Pullback.pullbackEquiv (CanonicalQuotientCharts.quotient_isLocalDiffeomorph D v hv) x
      (quotientSection D v hv (D.quotient v hv x)) = upstairsSection D x :=
  SectionsDescent.pullback_descendedSection
    (CanonicalQuotientCharts.quotient_isLocalDiffeomorph D v hv)
    (D.quotient_surjective v hv) (upstairsSection D) (quotientCompatible D v hv) x

theorem quotientSectionMap_at_image (x : D.TotalSpace) :
    quotientSectionMap D v hv (D.quotient v hv x) =
      Pullback.forwardMap (CanonicalQuotientCharts.quotient_isLocalDiffeomorph D v hv)
        (upstairsSectionMap D x) :=
  SectionsDescent.descendedSectionMap_at_image
    (CanonicalQuotientCharts.quotient_isLocalDiffeomorph D v hv)
    (D.quotient_surjective v hv) (upstairsSection D) (quotientCompatible D v hv) x

theorem quotientSection_zero_iff_at_image (x : D.TotalSpace) :
    quotientSection D v hv (D.quotient v hv x) = 0 ↔ upstairsSection D x = 0 :=
  SectionsDescent.descendedSection_zero_iff_at_image
    (CanonicalQuotientCharts.quotient_isLocalDiffeomorph D v hv)
    (D.quotient_surjective v hv) (upstairsSection D) (quotientCompatible D v hv) x

/-- There are no additional zeros anywhere in the full ambient filling. -/
theorem quotientSection_eq_zero_iff (y : D.Space v hv) :
    quotientSection D v hv y = 0 ↔
      SectionsUnit.vanishingOrder j ≠ 0 ∧ D.projection v hv y = Elliptic.discZero := by
  obtain ⟨x, rfl⟩ := D.quotient_surjective v hv y
  rw [quotientSection_zero_iff_at_image, upstairsSection_eq_zero_iff,
    D.projection_quotient, discPower_eq_zero_iff]
  exact and_congr_right fun _ => by
    constructor
    · exact fun h => Subtype.ext h
    · exact congrArg (fun s : Disc => (s : ℂ))

theorem quotientSection_ne_zero_iff (y : D.Space v hv) :
    quotientSection D v hv y ≠ 0 ↔
      SectionsUnit.vanishingOrder j = 0 ∨ D.projection v hv y ≠ Elliptic.discZero := by
  simpa only [not_and_or, not_not] using not_congr (quotientSection_eq_zero_iff D v hv y)

/-- Every holomorphic section satisfying the genuine differential
pullback identity equals this constructed section. -/
theorem quotientSection_unique (t : SectionsDescent.Section (D.Space v hv))
    (ht : ∀ x, Pullback.pullbackEquiv
      (CanonicalQuotientCharts.quotient_isLocalDiffeomorph D v hv) x
        (t (D.quotient v hv x)) = upstairsSection D x) :
    t = quotientSection D v hv :=
  SectionsDescent.descendedSection_unique
    (CanonicalQuotientCharts.quotient_isLocalDiffeomorph D v hv)
    (D.quotient_surjective v hv) (upstairsSection D) (quotientCompatible D v hv) t ht

end Wikipedia.HopfProblem.Elliptic.Equivariant.Data.CanonicalSections
