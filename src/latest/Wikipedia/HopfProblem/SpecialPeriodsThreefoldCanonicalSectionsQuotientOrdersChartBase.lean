import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsQuotientChartsForms
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsUnitOrders

/-!
# The actual transverse coordinate germ in a native elliptic quotient chart

Fixing the two fibre coordinates of the original quotient chart defines a
transverse line through its centre.  Near that centre the line stays in the
chart target, its inverse stays in the full native chart source, and its
lifted disc coordinate is the inverse of the original disc chart.  Thus
every function of the lifted base has the corresponding actual disc germ.
-/

noncomputable section

open Set Filter Topology

namespace Wikipedia.HopfProblem.Elliptic.Equivariant.Data.CanonicalQuotientCharts

open TrianglePeriodFamily.Canonical SpecialPeriods

variable {j : Kind} (D : Equivariant.Data j) (v : Lattice) (hv : AdmissibleTwist j v)

local instance ordersChartBaseFamilyChartedSpace : ChartedSpace Model D.TotalSpace :=
  D.periods.totalChartedSpace

local instance ordersChartBaseQuotientChartedSpace : ChartedSpace Model (D.Space v hv) :=
  D.chartedSpace v hv

/-- The inverse of the original quotient chart on its transverse coordinate line. -/
def transversePoint (y : D.Space v hv) (z : ℂ) : D.Space v hv :=
  (chartAt Model y).symm (z, (chartAt Model y y).2)

@[simp] theorem transversePoint_center (y : D.Space v hv) :
    transversePoint D v hv y (chartAt Model y y).1 = y :=
  (chartAt Model y).left_inv (mem_chart_source Model y)

/-- The transverse line stays in the target of the actual preferred chart. -/
theorem transverse_coordinate_mem_target_eventually (y : D.Space v hv) :
    ∀ᶠ z in 𝓝 (chartAt Model y y).1,
      (z, (chartAt Model y y).2) ∈ (chartAt Model y).target := by
  have ht : (chartAt Model y).target ∈
      𝓝 ((chartAt Model y y).1, (chartAt Model y y).2) :=
    (chartAt Model y).open_target.mem_nhds (mem_chart_target Model y)
  have hc : ContinuousAt (fun z : ℂ => (z, (chartAt Model y y).2))
      (chartAt Model y y).1 := continuousAt_id.prodMk continuousAt_const
  exact hc ht

theorem transversePoint_mem_source_of_mem_target (y : D.Space v hv) (z : ℂ)
    (hz : (z, (chartAt Model y y).2) ∈ (chartAt Model y).target) :
    transversePoint D v hv y z ∈ (chartAt Model y).source :=
  (chartAt Model y).map_target hz

/-- The actual inverse-chart line lies in the full native chart source near its centre. -/
theorem transversePoint_mem_source_eventually (y : D.Space v hv) :
    ∀ᶠ z in 𝓝 (chartAt Model y y).1,
      transversePoint D v hv y z ∈ (chartAt Model y).source :=
  (transverse_coordinate_mem_target_eventually D v hv y).mono fun z hz =>
    transversePoint_mem_source_of_mem_target D v hv y z hz

theorem transversePoint_chart_of_mem_target (y : D.Space v hv) (z : ℂ)
    (hz : (z, (chartAt Model y y).2) ∈ (chartAt Model y).target) :
    chartAt Model y (transversePoint D v hv y z) = (z, (chartAt Model y y).2) :=
  (chartAt Model y).right_inv hz

/-- The whole native coordinate tuple is the specified transverse line. -/
theorem transversePoint_chart_eventuallyEq (y : D.Space v hv) :
    (fun z : ℂ => chartAt Model y (transversePoint D v hv y z)) =ᶠ[
      𝓝 (chartAt Model y y).1] (fun z : ℂ => (z, (chartAt Model y y).2)) :=
  (transverse_coordinate_mem_target_eventually D v hv y).mono fun z hz =>
    transversePoint_chart_of_mem_target D v hv y z hz

theorem transversePoint_first_coordinate_eventuallyEq (y : D.Space v hv) :
    (fun z : ℂ => (chartAt Model y (transversePoint D v hv y z)).1) =ᶠ[
      𝓝 (chartAt Model y y).1] (fun z : ℂ => z) :=
  (transversePoint_chart_eventuallyEq D v hv y).mono fun _ hz => congrArg Prod.fst hz

/-- On the full chart source, the lift's base is given by the actual inverse disc chart. -/
theorem lift_base_eq_discChart_symm (y x : D.Space v hv)
    (hx : x ∈ (chartAt Model y).source) :
    (lift D v hv y x).1 = (chartAt ℂ SpecialPeriods.discZero).symm
      (chartAt Model y x).1 := by
  rw [← lift_base_coe D v hv y x hx]
  exact ((chartAt ℂ SpecialPeriods.discZero).left_inv (by trivial)).symm

/-- The actual lifted base along the native transverse line has the original disc germ. -/
theorem lift_transversePoint_base_eventuallyEq (y : D.Space v hv) :
    (fun z : ℂ => (lift D v hv y (transversePoint D v hv y z)).1) =ᶠ[
      𝓝 (chartAt Model y y).1] (chartAt ℂ SpecialPeriods.discZero).symm := by
  filter_upwards [transversePoint_mem_source_eventually D v hv y,
    transversePoint_first_coordinate_eventuallyEq D v hv y] with z hs hz
  rw [lift_base_eq_discChart_symm D v hv y _ hs, hz]

/-- Evaluating any disc coefficient on the actual lifted transverse line
agrees near the chart centre with its original ambient disc extension. -/
theorem lift_transversePoint_coefficient_eventuallyEq (F : Disc → ℂ)
    (y : D.Space v hv) :
    (fun z : ℂ => F (lift D v hv y (transversePoint D v hv y z)).1) =ᶠ[
      𝓝 (chartAt Model y y).1]
        SpecialPeriods.Threefold.Canonical.SectionsUnit.discExtension F :=
  (lift_transversePoint_base_eventuallyEq D v hv y).mono fun _ hz => congrArg F hz

end Wikipedia.HopfProblem.Elliptic.Equivariant.Data.CanonicalQuotientCharts
