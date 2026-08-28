import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionEllipticBasic
import Wikipedia.HopfProblem.EllipticEquivariantLocalModel

/-!
# Literal vertical translation in the original elliptic charts

The chart inverses of both actual covering quotients are the original
quotient maps composed with the original vector-coordinate chart
inverses.  Consequently vertical translation is addition in the last
complex coordinate in these unchanged native charts.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Elliptic

open Wikipedia.HopfProblem.Elliptic

variable {j : Kind} (D : Equivariant.Data j)

local instance vectorCoverChartedSpace : ChartedSpace FamilyModel (Disc × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (Disc × ComplexPlane₂))

/-- Exact translation formula through the original varying-period
chart inverse, including its total extension outside the chart target. -/
theorem periodFlow_chart_symm (s : ℂ) (x : D.TotalSpace) (u : FamilyModel) :
    letI := D.periods.totalChartedSpace
    Period.flow D.periods s ((chartAt FamilyModel x).symm u) =
      (chartAt FamilyModel x).symm (u.1, u.2 + Period.vector s) := by
  let := D.periods.totalChartedSpace
  let := D.periods.coveringAction
  let r := CoveringQuotient.representative D.periods.quotientCoveringMap x
  change Period.flow D.periods s
      ((CoveringQuotient.chart (E := FamilyModel) D.periods.quotientCoveringMap x).symm u) =
    (CoveringQuotient.chart (E := FamilyModel) D.periods.quotientCoveringMap x).symm
      (u.1, u.2 + Period.vector s)
  rw [CoveringQuotient.chart_symm]
  exact Period.flow_quotientMap D.periods s ((chartAt ℂ r.1).symm u.1, u.2)

/-- The actual finite-affine quotient chart has the same literal
vertical-translation formula. -/
theorem flow_chart_symm (v : Lattice) (hv : AdmissibleTwist j v) (s : ℂ)
    (y : D.Space v hv) (u : FamilyModel) :
    letI := D.chartedSpace v hv
    flow D v hv s ((chartAt FamilyModel y).symm u) =
      (chartAt FamilyModel y).symm (u.1, u.2 + Period.vector s) := by
  let := D.periods.totalChartedSpace
  let := D.chartedSpace v hv
  let := D.action v hv.1
  let r := CoveringQuotient.representative (D.quotientCoveringMap v hv) y
  change flow D v hv s
      ((CoveringQuotient.chart (E := FamilyModel) (D.quotientCoveringMap v hv) y).symm u) =
    (CoveringQuotient.chart (E := FamilyModel) (D.quotientCoveringMap v hv) y).symm
      (u.1, u.2 + Period.vector s)
  rw [CoveringQuotient.chart_symm]
  change flow D v hv s (D.quotient v hv ((chartAt FamilyModel r).symm u)) =
    D.quotient v hv ((chartAt FamilyModel r).symm (u.1, u.2 + Period.vector s))
  rw [flow_quotient, periodFlow_chart_symm]

/-- Whenever both displayed coordinates lie in the native chart, the
flow is exactly addition of `![0,s]` to the fibre coordinate. -/
theorem flow_in_chart (v : Lattice) (hv : AdmissibleTwist j v) (s : ℂ)
    (y x : D.Space v hv) :
    letI := D.chartedSpace v hv
    x ∈ (chartAt FamilyModel y).source →
      ((chartAt FamilyModel y x).1,
          (chartAt FamilyModel y x).2 + Period.vector s) ∈ (chartAt FamilyModel y).target →
      chartAt FamilyModel y (flow D v hv s x) =
        ((chartAt FamilyModel y x).1, (chartAt FamilyModel y x).2 + Period.vector s) := by
  let := D.chartedSpace v hv
  intro hx hu
  have he := flow_chart_symm D v hv s y (chartAt FamilyModel y x)
  rw [(chartAt FamilyModel y).left_inv hx] at he
  rw [he]
  exact (chartAt FamilyModel y).right_inv hu

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Elliptic
