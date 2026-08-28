import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsQuotientOrdersDescent
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsQuotientOrdersChartBase

/-!
# Exact transverse orders of the genuine descended canonical section

The transverse function below is obtained by restricting the native-chart
coefficient of the actual descended canonical section to the actual
transverse chart line.  Its equality with the original disc coefficient
is proved from the native quotient charts and differential pullback.
Thus a disc coefficient `s^n u(s)` with a holomorphic unit has exact
transverse order `n` at every point of the reduced central fibre.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.Elliptic.Equivariant.Data.CanonicalQuotientCharts

open TrianglePeriodFamily.Canonical SpecialPeriods SpecialPeriods.Threefold.Canonical

local notation "I" => modelWithCornersSelf ℂ Model
local notation "I₁" => modelWithCornersSelf ℂ ℂ

variable {j : Kind} (D : Equivariant.Data j) (v : Lattice) (hv : AdmissibleTwist j v)

local instance ordersFamilyChartedSpace : ChartedSpace Model D.TotalSpace :=
  D.periods.totalChartedSpace

local instance ordersFamilyManifold : IsManifold I ω D.TotalSpace :=
  D.periods.totalSpace_isManifold

local instance ordersQuotientChartedSpace : ChartedSpace Model (D.Space v hv) :=
  D.chartedSpace v hv

local instance ordersQuotientManifold : IsManifold I ω (D.Space v hv) := D.isManifold v hv

/-- Restriction of the actual native canonical coefficient to the actual
transverse line through `y`, with its other two chart coordinates fixed. -/
def transverseCoefficient (F : Disc → ℂ) (y : D.Space v hv) (z : ℂ) : ℂ :=
  descendedChartCoefficient D v hv F y (transversePoint D v hv y z)

/-- The transverse germ is proved to be the given disc germ, using native
chart lifts and the genuine globally descended section. -/
theorem transverseCoefficient_eventuallyEq (F : Disc → ℂ)
    (hs : SectionsDescent.Compatible (quotient_isLocalDiffeomorph D v hv)
      (SectionsUpstairs.weightedSection D.periods F)) (y : D.Space v hv) :
    transverseCoefficient D v hv F y =ᶠ[𝓝 (chartAt Model y y).1]
      SectionsUnit.discExtension F := by
  have he : transverseCoefficient D v hv F y =ᶠ[𝓝 (chartAt Model y y).1]
      (fun z : ℂ => F (lift D v hv y (transversePoint D v hv y z)).1) := by
    filter_upwards [transversePoint_mem_source_eventually D v hv y] with z hz
    exact descendedChartCoefficient_eq_lift D v hv F hs y (transversePoint D v hv y z) hz
  exact he.trans (lift_transversePoint_coefficient_eventuallyEq D v hv F y)

/-- At every point of the actual central fibre, the transverse native
coordinate is centred at zero. -/
theorem central_chart_first_eq_zero (y : D.Space v hv)
    (hy : D.projection v hv y = Elliptic.discZero) : (chartAt Model y y).1 = 0 :=
  (D.central_chart_iff v hv y y (mem_chart_source Model y)).mp hy

theorem transverseCoefficient_eventuallyEq_zero (F : Disc → ℂ)
    (hs : SectionsDescent.Compatible (quotient_isLocalDiffeomorph D v hv)
      (SectionsUpstairs.weightedSection D.periods F))
    (y : D.Space v hv) (hy : D.projection v hv y = Elliptic.discZero) :
    transverseCoefficient D v hv F y =ᶠ[𝓝 (0 : ℂ)] SectionsUnit.discExtension F := by
  simpa only [central_chart_first_eq_zero D v hv y hy] using
    transverseCoefficient_eventuallyEq D v hv F hs y

/-- The analyticity assertion concerns the actual native transverse
coefficient, not merely the expression later proved equal to its germ. -/
theorem transverseCoefficient_analyticAt (F : Disc → ℂ)
    (hs : SectionsDescent.Compatible (quotient_isLocalDiffeomorph D v hv)
      (SectionsUpstairs.weightedSection D.periods F)) (hF : ContMDiff I₁ I₁ ω F)
    (y : D.Space v hv) (hy : D.projection v hv y = Elliptic.discZero) :
    AnalyticAt ℂ (transverseCoefficient D v hv F y) 0 :=
  (SectionsUnit.discExtension_analyticAt hF).congr
    (transverseCoefficient_eventuallyEq_zero D v hv F hs y hy).symm

theorem transverseCoefficient_order_eq_discExtension (F : Disc → ℂ)
    (hs : SectionsDescent.Compatible (quotient_isLocalDiffeomorph D v hv)
      (SectionsUpstairs.weightedSection D.periods F))
    (y : D.Space v hv) (hy : D.projection v hv y = Elliptic.discZero) :
    analyticOrderAt (transverseCoefficient D v hv F y) 0 =
      analyticOrderAt (SectionsUnit.discExtension F) 0 :=
  analyticOrderAt_congr (transverseCoefficient_eventuallyEq_zero D v hv F hs y hy)

/-- The exact order of a coordinate power times a holomorphic unit holds
at every central point of the actual finite quotient threefold. -/
theorem transverseCoefficient_power_unit_order (u : Disc → ℂ) (n : ℕ)
    (hu : ContMDiff I₁ I₁ ω u) (hunit : u SpecialPeriods.discZero ≠ 0)
    (hs : SectionsDescent.Compatible (quotient_isLocalDiffeomorph D v hv)
      (SectionsUpstairs.weightedSection D.periods (fun s : Disc => (s : ℂ) ^ n * u s)))
    (y : D.Space v hv) (hy : D.projection v hv y = Elliptic.discZero) :
    analyticOrderAt
      (transverseCoefficient D v hv (fun s : Disc => (s : ℂ) ^ n * u s) y) 0 = (n : ℕ∞) := by
  rw [transverseCoefficient_order_eq_discExtension D v hv _ hs y hy]
  exact SectionsUnit.analyticOrderAt_discExtension_power_mul hu hunit n

/-- The actual native chart-base coordinate vanishes exactly on the
reduced central support of the finite quotient. -/
theorem chartBase_coe_eq_zero_iff (y x : D.Space v hv)
    (hx : x ∈ (chartAt Model y).source) :
    (chartBase D v hv y x hx : ℂ) = 0 ↔ D.projection v hv x = Elliptic.discZero := by
  rw [chartBase_coe]
  exact (D.central_chart_iff v hv y x hx).symm

/-- If the remaining factor is nowhere zero on the disc, the zero set of
the actual descended vector is exactly the prescribed central support. -/
theorem descendedWeightedSection_power_unit_eq_zero_iff (u : Disc → ℂ) (n : ℕ)
    (hunit : ∀ s, u s ≠ 0)
    (hs : SectionsDescent.Compatible (quotient_isLocalDiffeomorph D v hv)
      (SectionsUpstairs.weightedSection D.periods (fun s : Disc => (s : ℂ) ^ n * u s)))
    (x : D.Space v hv) :
    descendedWeightedSection D v hv (fun s : Disc => (s : ℂ) ^ n * u s) x = 0 ↔
      n ≠ 0 ∧ D.projection v hv x = Elliptic.discZero := by
  rw [descendedWeightedSection_eq_zero_iff D v hv _ hs x x (mem_chart_source Model x)]
  rw [mul_eq_zero]
  simp only [hunit, or_false]
  by_cases hn : n = 0
  · simp only [hn, pow_zero, one_ne_zero, ne_eq, not_true_eq_false, false_and]
  · rw [pow_eq_zero_iff hn, chartBase_coe_eq_zero_iff]
    exact (and_iff_right hn).symm

theorem descendedWeightedSection_power_unit_ne_zero_iff (u : Disc → ℂ) (n : ℕ)
    (hunit : ∀ s, u s ≠ 0)
    (hs : SectionsDescent.Compatible (quotient_isLocalDiffeomorph D v hv)
      (SectionsUpstairs.weightedSection D.periods (fun s : Disc => (s : ℂ) ^ n * u s)))
    (x : D.Space v hv) :
    descendedWeightedSection D v hv (fun s : Disc => (s : ℂ) ^ n * u s) x ≠ 0 ↔
      n = 0 ∨ D.projection v hv x ≠ Elliptic.discZero := by
  classical
  simpa only [not_and_or, not_not] using
    (descendedWeightedSection_power_unit_eq_zero_iff D v hv u n hunit hs x).not

end Wikipedia.HopfProblem.Elliptic.Equivariant.Data.CanonicalQuotientCharts
