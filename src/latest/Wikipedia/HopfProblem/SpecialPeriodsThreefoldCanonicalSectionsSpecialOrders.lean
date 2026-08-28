import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsSpecialOrdersCharts
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsQuotientOrders

/-!
# Exact canonical-section orders on the actual special elliptic fillings

The section and the transverse coefficient in this file belong to the
original full elliptic fillings for the unconditionally constructed
special periods and the specified main twists.  The coefficient is
extracted from the genuine native-chart alternating three-covector and
then restricted to the actual inverse-chart transverse line.

Every native chart represents the section as its first coordinate to
power zero or two, times an explicitly proved holomorphic nowhere-zero
unit and the actual canonical local frame.  The resulting transverse
analytic orders are exactly zero and two at every central point.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Sections

open Wikipedia.HopfProblem.Elliptic EllipticFilling TrianglePeriodFamily.Canonical
open Wikipedia.HopfProblem.Elliptic.Equivariant.Data

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₃" => modelWithCornersSelf ℂ Model

attribute [local instance] specialFullFillingChartedSpace

local instance specialOrdersResultUpstairsChartedSpace (j : Kind) :
    ChartedSpace Model (specialLocalData j).TotalSpace :=
  (specialLocalData j).periods.totalChartedSpace

local instance specialOrdersResultUpstairsManifold (j : Kind) :
    IsManifold I₃ ω (specialLocalData j).TotalSpace :=
  (specialLocalData j).periods.totalSpace_isManifold

local instance specialOrdersResultFullManifold (j : Kind) :
    IsManifold I₃ ω (SpecialFullFilling j) :=
  (specialFullFilling_construction j).2.2.1

/-- This is the actual previously constructed special section and the
actual generic differential-descent construction, with no additional data. -/
theorem fullSection_eq_descendedWeightedSection (j : Kind) :
    fullSection j = CanonicalQuotientCharts.descendedWeightedSection (specialLocalData j)
      j.twist (mainTwist_admissible j) (SectionsUnit.specialCoefficient j) := rfl

/-- Exact native top-covector coordinates of the actual special section
on the entire source of every original full-filling chart. -/
theorem fullSection_inCoordinates (j : Kind) (y x : SpecialFullFilling j)
    (hx : x ∈ (chartAt Model y).source) :
    Elliptic.fullInCoordinates j (achart Model y) x (fullSection j x) =
      SectionsUnit.specialCoefficient j (fullChartBase j y ⟨x, hx⟩) • volume :=
  CanonicalQuotientCharts.descendedWeightedSection_inCoordinates (specialLocalData j)
    j.twist (mainTwist_admissible j) (SectionsUnit.specialCoefficient j)
    (CanonicalSections.quotientCompatible (specialLocalData j) j.twist (mainTwist_admissible j))
    y x hx

/-- The exact power and the holomorphic unit occur in the native chart,
not in a separately prescribed coefficient model. -/
theorem fullSection_inCoordinates_power_unit (j : Kind) (y : SpecialFullFilling j)
    (x : Elliptic.fullChartSource j y) :
    Elliptic.fullInCoordinates j (achart Model y) x.val (fullSection j x.val) =
      ((chartAt Model y x.val).1 ^ SectionsUnit.vanishingOrder j * fullChartUnit j y x) •
        volume := by
  rw [fullSection_inCoordinates j y x.val x.property, SectionsUnit.specialCoefficient_eq,
    fullChartBase_coe]
  rfl

/-- Fibrewise equality with the actual native canonical frame, whose
holomorphicity and nonvanishing were proved for the original bundle. -/
theorem fullSection_eq_power_unit_smul_localFrame (j : Kind) (y : SpecialFullFilling j)
    (x : Elliptic.fullChartSource j y) :
    fullSection j x.val =
      ((chartAt Model y x.val).1 ^ SectionsUnit.vanishingOrder j * fullChartUnit j y x) •
        Elliptic.fullLocalFrame j y x := by
  apply (Elliptic.fullCoordinateEquiv j (achart Model y) x.property).injective
  calc
    _ = ((chartAt Model y x.val).1 ^ SectionsUnit.vanishingOrder j * fullChartUnit j y x) •
        volume := fullSection_inCoordinates_power_unit j y x
    _ = ((chartAt Model y x.val).1 ^ SectionsUnit.vanishingOrder j * fullChartUnit j y x) •
        Elliptic.fullCoordinateEquiv j (achart Model y) x.property
          (Elliptic.fullLocalFrame j y x) := by
      exact congrArg
        (fun α : TopCovector =>
          ((chartAt Model y x.val).1 ^ SectionsUnit.vanishingOrder j * fullChartUnit j y x) • α)
        (Elliptic.fullLocalFrame_inCoordinates j y x).symm
    _ = _ := (map_smul (Elliptic.fullCoordinateEquiv j (achart Model y) x.property)
      _ (Elliptic.fullLocalFrame j y x)).symm

/-- A complete native-chart unit factorization for every chart, with the
holomorphic unit explicitly supplied by the actual special period map. -/
theorem fullSection_native_unit_factor (j : Kind) (y : SpecialFullFilling j) :
    ∃ u : Elliptic.fullChartSource j y → ℂ,
      ContMDiff I₃ I₁ ω u ∧ (∀ x, u x ≠ 0) ∧
        ∀ x : Elliptic.fullChartSource j y,
          fullSection j x.val =
            ((chartAt Model y x.val).1 ^ SectionsUnit.vanishingOrder j * u x) •
              Elliptic.fullLocalFrame j y x :=
  ⟨fullChartUnit j y, fullChartUnit_holomorphic j y, fullChartUnit_ne_zero j y,
    fullSection_eq_power_unit_smul_localFrame j y⟩

/-- The scalar coefficient of the actual canonical section, restricted
to the actual inverse-chart transverse line through `y`. -/
def fullTransverseCoefficient (j : Kind) (y : SpecialFullFilling j) (z : ℂ) : ℂ :=
  coefficient (Elliptic.fullInCoordinates j (achart Model y)
    ((chartAt Model y).symm (z, (chartAt Model y y).2))
    (fullSection j ((chartAt Model y).symm (z, (chartAt Model y y).2))))

/-- The literal native-chart definition agrees with the general theorem
about the actual descended canonical section. -/
theorem fullTransverseCoefficient_eq (j : Kind) (y : SpecialFullFilling j) :
    fullTransverseCoefficient j y =
      CanonicalQuotientCharts.transverseCoefficient (specialLocalData j) j.twist
        (mainTwist_admissible j) (SectionsUnit.specialCoefficient j) y := rfl

theorem fullTransverseCoefficient_eventuallyEq (j : Kind) (y : SpecialFullFilling j) :
    fullTransverseCoefficient j y =ᶠ[𝓝 (chartAt Model y y).1]
      SectionsUnit.discExtension (SectionsUnit.specialCoefficient j) := by
  rw [fullTransverseCoefficient_eq]
  exact CanonicalQuotientCharts.transverseCoefficient_eventuallyEq (specialLocalData j)
    j.twist (mainTwist_admissible j) (SectionsUnit.specialCoefficient j)
    (CanonicalSections.quotientCompatible (specialLocalData j) j.twist (mainTwist_admissible j)) y

theorem fullTransverseCoefficient_eventuallyEq_zero (j : Kind) (y : SpecialFullFilling j)
    (hy : specialFullFillingProjection j y = Wikipedia.HopfProblem.Elliptic.discZero) :
    fullTransverseCoefficient j y =ᶠ[𝓝 (0 : ℂ)]
      SectionsUnit.discExtension (SectionsUnit.specialCoefficient j) := by
  rw [fullTransverseCoefficient_eq]
  exact CanonicalQuotientCharts.transverseCoefficient_eventuallyEq_zero (specialLocalData j)
    j.twist (mainTwist_admissible j) (SectionsUnit.specialCoefficient j)
    (CanonicalSections.quotientCompatible (specialLocalData j) j.twist (mainTwist_admissible j))
    y hy

/-- The ambient transverse germ of the actual section is analytic at
every point of the actual reduced central fibre. -/
theorem fullTransverseCoefficient_analyticAt (j : Kind) (y : SpecialFullFilling j)
    (hy : specialFullFillingProjection j y = Wikipedia.HopfProblem.Elliptic.discZero) :
    AnalyticAt ℂ (fullTransverseCoefficient j y) 0 :=
  (SectionsUnit.specialCoefficient_extension_analyticAt j).congr
    (fullTransverseCoefficient_eventuallyEq_zero j y hy).symm

/-- The proved transverse germ is a power times the actual holomorphic
period unit, with no additional zeros or poles at its centre. -/
theorem fullTransverseCoefficient_factorization (j : Kind) (y : SpecialFullFilling j)
    (hy : specialFullFillingProjection j y = Wikipedia.HopfProblem.Elliptic.discZero) :
    fullTransverseCoefficient j y =ᶠ[𝓝 (0 : ℂ)]
      (fun z : ℂ => z ^ SectionsUnit.vanishingOrder j *
        SectionsUnit.discExtension (SectionsUnit.specialUnit j) z) :=
  (fullTransverseCoefficient_eventuallyEq_zero j y hy).trans
    (SectionsUnit.coefficient_extension_factorization (specialLocalData j))

/-- The exact canonical-section order is zero or two at every actual
central point, unconditionally for the constructed special periods. -/
theorem fullTransverseCoefficient_analyticOrderAt (j : Kind) (y : SpecialFullFilling j)
    (hy : specialFullFillingProjection j y = Wikipedia.HopfProblem.Elliptic.discZero) :
    analyticOrderAt (fullTransverseCoefficient j y) 0 = (SectionsUnit.vanishingOrder j : ℕ∞) :=
  (analyticOrderAt_congr (fullTransverseCoefficient_eventuallyEq_zero j y hy)).trans
    (SectionsUnit.specialCoefficient_analyticOrderAt j)

theorem fullTransverseCoefficient_three_order (y : SpecialFullFilling .three)
    (hy : specialFullFillingProjection .three y = Wikipedia.HopfProblem.Elliptic.discZero) :
    analyticOrderAt (fullTransverseCoefficient .three y) 0 = 0 :=
  fullTransverseCoefficient_analyticOrderAt .three y hy

theorem fullTransverseCoefficient_four_order (y : SpecialFullFilling .four)
    (hy : specialFullFillingProjection .four y = Wikipedia.HopfProblem.Elliptic.discZero) :
    analyticOrderAt (fullTransverseCoefficient .four y) 0 = 2 :=
  fullTransverseCoefficient_analyticOrderAt .four y hy

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Sections
