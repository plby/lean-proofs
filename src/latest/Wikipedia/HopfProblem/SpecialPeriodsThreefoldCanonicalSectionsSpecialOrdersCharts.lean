import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsSpecial
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsQuotientChartsForms

/-!
# Holomorphic base coordinates and units on full native elliptic charts

The first native coordinate on each full special elliptic filling takes
values in the original base disc.  Its holomorphicity is obtained from
the actual selected quotient lift followed by the varying-family
projection.  The previously constructed special disc unit therefore
gives a holomorphic, nowhere-zero function on the entire native chart
source.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Sections

open Wikipedia.HopfProblem.Elliptic EllipticFilling TrianglePeriodFamily.Canonical
open Wikipedia.HopfProblem.Elliptic.Equivariant.Data

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₃" => modelWithCornersSelf ℂ Model

attribute [local instance] specialFullFillingChartedSpace

local instance specialOrdersUpstairsChartedSpace (j : Kind) :
    ChartedSpace Model (specialLocalData j).TotalSpace :=
  (specialLocalData j).periods.totalChartedSpace

local instance specialOrdersUpstairsManifold (j : Kind) :
    IsManifold I₃ ω (specialLocalData j).TotalSpace :=
  (specialLocalData j).periods.totalSpace_isManifold

local instance specialOrdersFullManifold (j : Kind) :
    IsManifold I₃ ω (SpecialFullFilling j) :=
  (specialFullFilling_construction j).2.2.1

/-- The actual selected quotient lift, restricted to the full native chart source. -/
def fullChartLift (j : Kind) (y : SpecialFullFilling j)
    (x : Elliptic.fullChartSource j y) : (specialLocalData j).TotalSpace :=
  CanonicalQuotientCharts.lift (specialLocalData j) j.twist
    (mainTwist_admissible j) y x.val

/-- The covering inverse is holomorphic on the entire native chart source. -/
theorem fullChartLift_holomorphic (j : Kind) (y : SpecialFullFilling j) :
    ContMDiff I₃ I₃ ω (fullChartLift j y) := by
  let := (specialLocalData j).chartedSpace j.twist (mainTwist_admissible j)
  have hl := (specialLocalData j).localInverse_holomorphic j.twist
    (mainTwist_admissible j)
    (CanonicalQuotientCharts.representative (specialLocalData j) j.twist
      (mainTwist_admissible j) y)
  exact hl.comp_contMDiff contMDiff_subtype_val fun x =>
    ((CanonicalQuotientCharts.chart_source (specialLocalData j) j.twist
      (mainTwist_admissible j) y x.val).mp x.property).1

/-- The first native quotient coordinate as a point of the actual base disc. -/
def fullChartBase (j : Kind) (y : SpecialFullFilling j)
    (x : Elliptic.fullChartSource j y) : Disc :=
  CanonicalQuotientCharts.chartBase (specialLocalData j) j.twist
    (mainTwist_admissible j) y x.val x.property

@[simp] theorem fullChartBase_coe (j : Kind) (y : SpecialFullFilling j)
    (x : Elliptic.fullChartSource j y) :
    (fullChartBase j y x : ℂ) = (chartAt Model y x.val).1 := rfl

/-- This disc-valued coordinate is the base of the actual covering lift. -/
theorem fullChartBase_eq_lift_base (j : Kind) (y : SpecialFullFilling j)
    (x : Elliptic.fullChartSource j y) :
    fullChartBase j y x = (fullChartLift j y x).1 :=
  CanonicalQuotientCharts.chartBase_eq_lift_base (specialLocalData j) j.twist
    (mainTwist_admissible j) y x.val x.property

theorem fullChartBase_holomorphic (j : Kind) (y : SpecialFullFilling j) :
    ContMDiff I₃ I₁ ω (fullChartBase j y) := by
  have he : fullChartBase j y = fun x => (fullChartLift j y x).1 :=
    funext (fullChartBase_eq_lift_base j y)
  rw [he]
  exact (specialLocalData j).periods.projection_holomorphic.comp
    (fullChartLift_holomorphic j y)

/-- The actual special period unit evaluated at the native chart's disc coordinate. -/
def fullChartUnit (j : Kind) (y : SpecialFullFilling j)
    (x : Elliptic.fullChartSource j y) : ℂ :=
  SectionsUnit.specialUnit j (fullChartBase j y x)

theorem fullChartUnit_holomorphic (j : Kind) (y : SpecialFullFilling j) :
    ContMDiff I₃ I₁ ω (fullChartUnit j y) :=
  (SectionsUnit.specialUnit_holomorphic j).comp (fullChartBase_holomorphic j y)

/-- The actual unit never vanishes anywhere in the full native chart source. -/
theorem fullChartUnit_ne_zero (j : Kind) (y : SpecialFullFilling j)
    (x : Elliptic.fullChartSource j y) : fullChartUnit j y x ≠ 0 :=
  SectionsUnit.specialUnit_ne_zero j (fullChartBase j y x)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Sections
