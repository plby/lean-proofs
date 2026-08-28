import Wikipedia.HopfProblem.SpecialPeriodsThreefoldFibreClassificationOrders
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspNormalForms
import Wikipedia.HopfProblem.CuspSection

/-!
# Actual power charts at the three special base values

At an elliptic value we use the original global multiplicity-three or
multiplicity-four chart.  At infinity we use the actual zero-section
point on the smooth part of the toric cusp fibre, where the native
projection is a single coordinate.  All charts below are analytic for
the already constructed global atlas.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

local notation "FM" => ℂ × ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ FM
local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "E₃" => ToricCharts.CoordinateSpace 3
local notation "I₃" => modelWithCornersSelf ℂ E₃

attribute [local instance] Threefold.chartedSpace

/-- Native chart data for an actual special fibre. These data will be
constructed below for every nonregular sphere value. -/
structure SpecialBasePowerChart (b : RiemannSphere) where
  degree : ℕ
  degree_pos : 0 < degree
  baseChart : PartialDiffeomorph I₁ I₁ RiemannSphere ℂ ω
  base_mem_source : b ∈ baseChart.source
  base_value : baseChart b = 0
  point : Threefold.Space
  point_projection : projectionSphere point = b
  chart : PartialDiffeomorph IF IF Threefold.Space FM ω
  point_mem_source : point ∈ chart.source
  point_first_zero : (chart point).1 = 0
  source_projects_into : ∀ x ∈ chart.source, projectionSphere x ∈ baseChart.source
  power_equation : ∀ u ∈ chart.target,
    baseChart (projectionSphere (chart.symm u)) = u.1 ^ degree

private theorem elliptic_projection_mem_chart_of_mem_patch (j : Elliptic.Kind)
    (x : Threefold.Space) (hx : x ∈ (liftedPatch (some (some j)) : Set Threefold.Space)) :
    projectionSphere x ∈ (EllipticGeometry.sphereChart j).source := by
  have hr : x ∈ Set.range (EllipticGeometry.inclusion j) := by
    rw [EllipticGeometry.inclusion_range]
    exact hx
  obtain ⟨y, rfl⟩ := hr
  exact EllipticGeometry.projectionSphere_inclusion_mem_sphereChart_source j y

/-- The actual global elliptic power chart, of degree three or four. -/
def ellipticSpecialBasePowerChart (j : Elliptic.Kind) :
    SpecialBasePowerChart (EllipticGeometry.sphereValue j) := by
  apply Classical.choice
  obtain ⟨x, hx⟩ := projectionSphere_surjective (EllipticGeometry.sphereValue j)
  obtain ⟨e, hxe, hzero, hsource, hpower⟩ :=
    FibreClassification.elliptic_fibre_power_chart j x hx
  refine ⟨?_⟩
  refine
    { degree := j.order
      degree_pos := j.order_pos
      baseChart := EllipticGeometry.sphereChart j
      base_mem_source := ?_
      base_value := EllipticGeometry.sphereChart_value j
      point := x
      point_projection := hx
      chart := e
      point_mem_source := hxe
      point_first_zero := hzero
      source_projects_into := fun y hy =>
        elliptic_projection_mem_chart_of_mem_patch j y (hsource hy)
      power_equation := hpower }
  rw [← hx]
  exact elliptic_projection_mem_chart_of_mem_patch j x (hsource hxe)

/-- The existing complex-linear split of the toric coordinates, as an
analytic map between the original standard model spaces. -/
def cuspProductCoordinates : Diffeomorph I₃ IF E₃ FM ω where
  toEquiv := cuspModelEquiv.toLinearEquiv.toEquiv
  contMDiff_toFun := cuspModelEquiv.contDiff.contMDiff
  contMDiff_invFun := cuspModelEquiv.symm.contDiff.contMDiff

/-- The literal zero-section point in the native cusp quotient lies on
one smooth branch of its actual central fibre. -/
def cuspSmoothCentralPoint : CuspGeometry.LocalSpace :=
  CuspQuotient.zeroSection CuspGeometry.data.correction CuspGeometry.data.radius
    ⟨0, by simpa [CuspQuotient.disc] using CuspGeometry.data.radius_pos⟩

theorem cuspSmoothCentralPoint_parameter : CuspGeometry.parameter cuspSmoothCentralPoint = 0 :=
  CuspQuotient.projection_zeroSection CuspGeometry.data.correction CuspGeometry.data.radius _

theorem cuspSmoothCentralPoint_branchCount :
    CuspQuotient.branchCount CuspGeometry.data.correction CuspGeometry.data.radius
      cuspSmoothCentralPoint = 1 := by
  unfold cuspSmoothCentralPoint
  rw [CuspQuotient.branchCount_zeroSection]
  simp only [ite_true]

/-- At infinity an actual smooth cusp-fibre point gives degree one. -/
def cuspSpecialBasePowerChart : SpecialBasePowerChart (∞ : RiemannSphere) := by
  apply Classical.choice
  let x := CuspGeometry.inclusion cuspSmoothCentralPoint
  have hx : projectionSphere x = (∞ : RiemannSphere) :=
    (CuspGeometry.projectionSphere_inclusion_eq_infty_iff cuspSmoothCentralPoint).mpr
      cuspSmoothCentralPoint_parameter
  obtain ⟨e, hxe, hzero, hsource, hpower⟩ :=
    CuspNormalForms.sphere_single_local_equation cuspSmoothCentralPoint
      cuspSmoothCentralPoint_branchCount
  let e' : PartialDiffeomorph IF IF Threefold.Space FM ω :=
    e.trans cuspProductCoordinates.toPartialDiffeomorph
  refine ⟨?_⟩
  refine
    { degree := 1
      degree_pos := by decide
      baseChart := CuspGeometry.sphereChart
      base_mem_source := ?_
      base_value := CuspGeometry.sphereChart_infty
      point := x
      point_projection := hx
      chart := e'
      point_mem_source := ⟨hxe, mem_univ _⟩
      point_first_zero := ?_
      source_projects_into := ?_
      power_equation := ?_ }
  · rw [← hx]
    exact CuspGeometry.projectionSphere_inclusion_mem_sphereChart_source cuspSmoothCentralPoint
  · change (cuspModelEquiv (e x)).1 = 0
    rw [hzero]
    rfl
  · intro y hy
    exact CuspNormalForms.projectionSphere_mem_sphereChart_of_mem_cuspPatch (hsource hy.1)
  · intro u hu
    change CuspGeometry.sphereChart (projectionSphere (e.symm (cuspModelEquiv.symm u))) = u.1 ^ 1
    exact (hpower (cuspModelEquiv.symm u) hu.2).trans (pow_one u.1).symm

/-- Every actual exceptional base value has a native analytic power
chart, with all existence and geometric hypotheses discharged. -/
def specialBasePowerChart (b : RiemannSphere) (hb : b ∉ sphereRegularPatch) :
    SpecialBasePowerChart b := by
  classical
  by_cases hinf : b = (∞ : RiemannSphere)
  · subst b
    exact cuspSpecialBasePowerChart
  by_cases hzero : b = ((0 : ℂ) : RiemannSphere)
  · subst b
    simpa only [EllipticGeometry.sphereValue_three] using ellipticSpecialBasePowerChart .three
  by_cases hone : b = ((1 : ℂ) : RiemannSphere)
  · subst b
    simpa only [EllipticGeometry.sphereValue_four] using ellipticSpecialBasePowerChart .four
  exact False.elim (hb ((mem_sphereRegularPatch b).mpr ⟨hinf, hzero, hone⟩))

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
