import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCuspCoordinates
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspFibreGeometry

/-!
# The reduced cusp equation and its dense complement

The complement of the actual fibre over infinity is dense in the glued
threefold.  This follows from the genuine cusp normal-crossing charts,
not from an assumed density of a regular locus.  The standard reciprocal
sphere coordinate is a product of distinct branch coordinates times a
nonvanishing analytic unit near each central point.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCusp

attribute [local instance] Threefold.chartedSpace CuspGeometry.nativeChartedSpace

local notation "E₃" => ToricCharts.CoordinateSpace 3

/-- The actual fibre over infinity, with no change of underlying space. -/
abbrev support : Set Threefold.Space := CuspGeometry.sphereCuspFibre

theorem support_closed : IsClosed support :=
  isClosed_singleton.preimage Threefold.projectionSphere_continuous

def outside : TopologicalSpace.Opens Threefold.Space :=
  ⟨supportᶜ, support_closed.isOpen_compl⟩

@[simp] theorem mem_outside (x : Threefold.Space) :
    x ∈ outside ↔ Threefold.projectionSphere x ≠ (∞ : RiemannSphere) := Iff.rfl

theorem model_all_ne_zero_dense : Dense {w : E₃ | ∀ j, w j ≠ 0} := by
  have h := dense_pi (univ : Set (Fin 3))
    (s := fun _ : Fin 3 => ({0} : Set ℂ)ᶜ) (fun _ _ => dense_compl_singleton (0 : ℂ))
  convert h using 1
  ext w
  simp only [Set.mem_pi, mem_ofPred_eq, mem_univ, forall_const, mem_compl_iff,
    mem_singleton_iff]

/-- Every nonempty global open set meets the actual complement of the
cusp fibre, including opens centered at double and triple points. -/
theorem outside_dense : Dense (outside : Set Threefold.Space) := by
  apply dense_iff_inter_open.mpr
  intro U hU hne
  obtain ⟨x, hxU⟩ := hne
  by_cases hx : Threefold.projectionSphere x = (∞ : RiemannSphere)
  · obtain ⟨a, ha, rfl⟩ :=
      CuspGeometry.exists_cusp_representative_of_projectionSphere_eq_infty x hx
    obtain ⟨J, e, _, _, hsource, _, _, hprod⟩ :=
      CuspNormalForms.sphere_normalCrossingChart_with_branchCount a ha
    have hV : IsOpen (e '' (e.source ∩ U)) :=
      e.toOpenPartialHomeomorph.isOpen_image_source_inter hU
    have hVne : (e '' (e.source ∩ U)).Nonempty :=
      ⟨e (CuspGeometry.inclusion a), ⟨CuspGeometry.inclusion a, ⟨hsource, hxU⟩, rfl⟩⟩
    obtain ⟨u, huV, hunz⟩ :=
      model_all_ne_zero_dense.inter_open_nonempty (e '' (e.source ∩ U)) hV hVne
    obtain ⟨w, ⟨hws, hwU⟩, rfl⟩ := huV
    refine ⟨w, hwU, (mem_outside w).mpr ?_⟩
    intro hw
    have hpower := hprod (e w) (e.map_source' hws)
    have he : e.symm (e w) = w := e.left_inv' hws
    change CuspGeometry.sphereChart (Threefold.projectionSphere (e.symm (e w))) =
      ∏ j ∈ J, e w j at hpower
    rw [he, hw, CuspGeometry.sphereChart_infty] at hpower
    exact (Finset.prod_ne_zero_iff.mpr (fun j _ => hunz j)) hpower.symm
  · exact ⟨x, hxU, (mem_outside x).mpr hx⟩

/-- A positive neighborhood on which the exact coordinate factor really
is an analytic unit. -/
theorem exists_coordinateUnit_disc :
    ∃ r : ℝ, 0 < r ∧ AnalyticOnNhd ℂ coordinateUnit (Metric.ball 0 r) ∧
      ∀ q ∈ Metric.ball 0 r, coordinateUnit q ≠ 0 := by
  have h : ∀ᶠ q in 𝓝 (0 : ℂ), AnalyticAt ℂ coordinateUnit q ∧ coordinateUnit q ≠ 0 :=
    coordinateUnit_analyticAt.eventually_analyticAt.and
      (coordinateUnit_analyticAt.continuousAt.eventually_ne coordinateUnit_zero_ne_zero)
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp h
  exact ⟨r, hr, fun q hq => (hsub hq).1, fun q hq => (hsub hq).2⟩

def coordinateUnitRadius : ℝ := exists_coordinateUnit_disc.choose

theorem coordinateUnitRadius_pos : 0 < coordinateUnitRadius :=
  exists_coordinateUnit_disc.choose_spec.1

theorem coordinateUnit_analyticOnNhd :
    AnalyticOnNhd ℂ coordinateUnit (Metric.ball 0 coordinateUnitRadius) :=
  exists_coordinateUnit_disc.choose_spec.2.1

theorem coordinateUnit_ne_zero {q : ℂ} (hq : q ∈ Metric.ball 0 coordinateUnitRadius) :
    coordinateUnit q ≠ 0 := exists_coordinateUnit_disc.choose_spec.2.2 q hq

/-- The product is over a finite set of distinct coordinates. -/
def branchProduct (J : Finset (Fin 3)) (w : E₃) : ℂ := ∏ j ∈ J, w j

theorem branchProduct_holomorphic (J : Finset (Fin 3)) :
    ContDiff ℂ ω (branchProduct J) :=
  contDiff_prod (fun j _ => contDiff_apply ℂ ℂ j)

theorem branchProduct_zero (J : Finset (Fin 3)) (hJ : J.Nonempty) :
    branchProduct J 0 = 0 := by
  obtain ⟨j, hj⟩ := hJ
  exact Finset.prod_eq_zero hj rfl

/-- The actual unit in a normal-crossing model chart. -/
def branchUnit (J : Finset (Fin 3)) (w : E₃) : ℂ := coordinateUnit (branchProduct J w)

theorem branchUnit_analyticAt (J : Finset (Fin 3)) (hJ : J.Nonempty) :
    AnalyticAt ℂ (branchUnit J) 0 := by
  have hu : AnalyticAt ℂ coordinateUnit (branchProduct J 0) :=
    (branchProduct_zero J hJ).symm ▸ coordinateUnit_analyticAt
  exact hu.comp (branchProduct_holomorphic J).contDiffAt.analyticAt

theorem branchUnit_zero_ne_zero (J : Finset (Fin 3)) (hJ : J.Nonempty) :
    branchUnit J 0 ≠ 0 := by
  change coordinateUnit (branchProduct J 0) ≠ 0
  rw [branchProduct_zero J hJ]
  exact coordinateUnit_zero_ne_zero

/-- On a genuine neighborhood in the model, the exact coefficient is
analytic and nowhere zero, as required for a reduced Cartier equation. -/
theorem branchUnit_eventually_analytic_ne_zero (J : Finset (Fin 3)) (hJ : J.Nonempty) :
    ∀ᶠ w in 𝓝 (0 : E₃), AnalyticAt ℂ (branchUnit J) w ∧ branchUnit J w ≠ 0 :=
  (branchUnit_analyticAt J hJ).eventually_analyticAt.and
    ((branchUnit_analyticAt J hJ).continuousAt.eventually_ne (branchUnit_zero_ne_zero J hJ))

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCusp
