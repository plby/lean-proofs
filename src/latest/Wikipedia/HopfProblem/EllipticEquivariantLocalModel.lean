import Wikipedia.HopfProblem.EllipticEquivariantFillings
import Wikipedia.HopfProblem.EllipticDiscOrbits

/-!
# Local analytic equations for arbitrary equivariant elliptic fillings

The varying-period complex atlas is selected from the supplied equivariant
data, and the filling atlas is selected from its actual finite covering
quotient.  In these charts the filling projection is exactly the prescribed
power of the first complex coordinate.  Consequently its reduced central
support is a coordinate hyperplane and its transverse analytic order is
three or four, with order one away from the central support.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.Elliptic.Equivariant.Data

open SpecialPeriods

variable {j : Kind} (D : Equivariant.Data j)

local instance localModelCoveringChartedSpace : ChartedSpace FamilyModel (Disc × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (Disc × ComplexPlane₂))

/-- The first coordinate of the selected varying-period family charts is
the actual base disc coordinate. -/
theorem familyProjection_chart_symm (x : D.TotalSpace) (u : FamilyModel) :
    letI := D.periods.totalChartedSpace
    u ∈ (chartAt FamilyModel x).target →
      (D.periods.projection ((chartAt FamilyModel x).symm u) : ℂ) = u.1 := by
  let := D.periods.totalChartedSpace
  let := D.periods.coveringAction
  intro hu
  let r := CoveringQuotient.representative D.periods.quotientCoveringMap x
  change u ∈ (CoveringQuotient.chart (E := FamilyModel)
    D.periods.quotientCoveringMap x).target at hu
  have hubase : u.1 ∈ (chartAt ℂ r.1).target := hu.1.1
  have hs : ((chartAt FamilyModel x).symm : FamilyModel → D.TotalSpace) =
      fun w => D.periods.quotientMap ((chartAt ℂ r.1).symm w.1, w.2) := by
    change ((CoveringQuotient.chart (E := FamilyModel)
      D.periods.quotientCoveringMap x).symm : FamilyModel → D.TotalSpace) = _
    rw [CoveringQuotient.chart_symm]
    rfl
  rw [hs]
  exact (chartAt ℂ r.1).right_inv hubase

/-- In the selected quotient complex atlas, the actual filling projection
has the exact local equation `s ↦ s^m`. -/
theorem projection_chart_symm (v : Lattice) (hv : AdmissibleTwist j v)
    (y : D.Space v hv) (u : FamilyModel) :
    letI := D.chartedSpace v hv
    u ∈ (chartAt FamilyModel y).target →
      (D.projection v hv ((chartAt FamilyModel y).symm u) : ℂ) = u.1 ^ j.order := by
  let := D.periods.totalChartedSpace
  let := D.chartedSpace v hv
  let := D.action v hv.1
  intro hu
  let hq := D.quotientCoveringMap v hv
  let r := CoveringQuotient.representative hq y
  change u ∈ (CoveringQuotient.chart (E := FamilyModel) hq y).target at hu
  have hur : u ∈ (chartAt FamilyModel r).target := hu.1
  have hs : ((chartAt FamilyModel y).symm : FamilyModel → D.Space v hv) =
      fun w => D.quotient v hv ((chartAt FamilyModel r).symm w) := by
    change ((CoveringQuotient.chart (E := FamilyModel) hq y).symm :
      FamilyModel → D.Space v hv) = _
    rw [CoveringQuotient.chart_symm]
    rfl
  rw [hs, D.projection_quotient, discPower_coe]
  change (D.periods.projection ((chartAt FamilyModel r).symm u) : ℂ) ^ j.order = _
  rw [D.familyProjection_chart_symm r u hur]

/-- The same exact local equation on the source of each quotient chart. -/
theorem projection_chart (v : Lattice) (hv : AdmissibleTwist j v)
    (y x : D.Space v hv) :
    letI := D.chartedSpace v hv
    x ∈ (chartAt FamilyModel y).source →
      (D.projection v hv x : ℂ) = (chartAt FamilyModel y x).1 ^ j.order := by
  let := D.chartedSpace v hv
  intro hx
  have h := D.projection_chart_symm v hv y (chartAt FamilyModel y x)
    ((chartAt FamilyModel y).map_source hx)
  rwa [(chartAt FamilyModel y).left_inv hx] at h

/-- The reduced central support is a coordinate hyperplane in the
selected smooth complex atlas. -/
theorem central_chart_iff (v : Lattice) (hv : AdmissibleTwist j v)
    (y x : D.Space v hv) :
    letI := D.chartedSpace v hv
    x ∈ (chartAt FamilyModel y).source →
      (D.projection v hv x = Elliptic.discZero ↔ (chartAt FamilyModel y x).1 = 0) := by
  let := D.chartedSpace v hv
  intro hx
  rw [Subtype.ext_iff, discZero_coe, D.projection_chart v hv y x hx]
  exact pow_eq_zero_iff j.order_pos.ne'

/-- The actual projection on a transverse complex coordinate line through
a point, using the complex atlas selected by the equivariant data. -/
def transverseProjection (v : Lattice) (hv : AdmissibleTwist j v)
    (y : D.Space v hv) (z : ℂ) : ℂ :=
  letI := D.chartedSpace v hv
  D.projection v hv
    ((chartAt FamilyModel y).symm (z, (chartAt FamilyModel y y).2))

theorem transverseProjection_eventuallyEq (v : Lattice) (hv : AdmissibleTwist j v)
    (y : D.Space v hv) :
    letI := D.chartedSpace v hv
    D.transverseProjection v hv y =ᶠ[𝓝 (chartAt FamilyModel y y).1]
      (fun z : ℂ => z ^ j.order) := by
  let := D.chartedSpace v hv
  have ht : (chartAt FamilyModel y).target ∈
      𝓝 ((chartAt FamilyModel y y).1, (chartAt FamilyModel y y).2) :=
    (chartAt FamilyModel y).open_target.mem_nhds (mem_chart_target FamilyModel y)
  have hc : ContinuousAt (fun z : ℂ => (z, (chartAt FamilyModel y y).2))
      (chartAt FamilyModel y y).1 := continuousAt_id.prodMk continuousAt_const
  have he : ∀ᶠ z in 𝓝 (chartAt FamilyModel y y).1,
      (z, (chartAt FamilyModel y y).2) ∈ (chartAt FamilyModel y).target := hc ht
  exact he.mono fun z hz => D.projection_chart_symm v hv y _ hz

/-- The central multiplicity is the exact analytic order of the actual
projection on a transverse coordinate line. -/
theorem central_transverse_order (v : Lattice) (hv : AdmissibleTwist j v)
    (y : D.Space v hv) (hy : D.projection v hv y = Elliptic.discZero) :
    letI := D.chartedSpace v hv
    analyticOrderAt (D.transverseProjection v hv y) 0 = (j.order : ℕ∞) := by
  let := D.chartedSpace v hv
  have hc : (chartAt FamilyModel y y).1 = 0 :=
    (D.central_chart_iff v hv y y (mem_chart_source FamilyModel y)).mp hy
  have he := D.transverseProjection_eventuallyEq v hv y
  rw [hc] at he
  rw [analyticOrderAt_congr he, complexPower_order_at_zero]

/-- Away from the central support, the actual projection minus its value
at the point has transverse analytic order one. -/
theorem noncentral_transverse_order (v : Lattice) (hv : AdmissibleTwist j v)
    (y : D.Space v hv) (hy : D.projection v hv y ≠ Elliptic.discZero) :
    letI := D.chartedSpace v hv
    analyticOrderAt (fun z : ℂ => D.transverseProjection v hv y z -
      (D.projection v hv y : ℂ)) (chartAt FamilyModel y y).1 = 1 := by
  let := D.chartedSpace v hv
  have hc : (chartAt FamilyModel y y).1 ≠ 0 :=
    mt (D.central_chart_iff v hv y y (mem_chart_source FamilyModel y)).mpr hy
  have he : (fun z : ℂ => D.transverseProjection v hv y z -
        (D.projection v hv y : ℂ)) =ᶠ[𝓝 (chartAt FamilyModel y y).1]
      (fun z : ℂ => z ^ j.order - (chartAt FamilyModel y y).1 ^ j.order) :=
    (D.transverseProjection_eventuallyEq v hv y).mono fun z hz => by
      dsimp only at hz ⊢
      rw [hz, D.projection_chart v hv y y (mem_chart_source FamilyModel y)]
  rw [analyticOrderAt_congr he]
  exact complexPower_order_at_nonzero j.order j.order_pos _ hc

end Wikipedia.HopfProblem.Elliptic.Equivariant.Data
