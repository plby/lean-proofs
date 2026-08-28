import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicSpecialCharts

/-!
# Punctured regular neighborhoods in the actual special power charts

The three exceptional values form the literal normalized finite set.
Removing the other two gives a neighborhood of any one of them.  In
the proved native power charts, leaving the central coordinate
hyperplane is therefore exactly returning to the actual regular base.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

local notation "FM" => ℂ × ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ FM

attribute [local instance] Threefold.chartedSpace

/-- The original sphere with the exceptional values other than `b` removed. -/
def awayFromOtherSpecialValues (b : RiemannSphere) : Opens RiemannSphere :=
  ⟨({(∞ : RiemannSphere), ((0 : ℂ) : RiemannSphere), ((1 : ℂ) : RiemannSphere)} \ {b})ᶜ,
    ((((finite_singleton ((1 : ℂ) : RiemannSphere)).insert
      ((0 : ℂ) : RiemannSphere)).insert (∞ : RiemannSphere)).sdiff).isClosed.isOpen_compl⟩

theorem mem_awayFromOtherSpecialValues_self (b : RiemannSphere) :
    b ∈ awayFromOtherSpecialValues b := by
  change b ∉ ({(∞ : RiemannSphere), ((0 : ℂ) : RiemannSphere),
    ((1 : ℂ) : RiemannSphere)} \ {b})
  simp only [Set.mem_sdiff, mem_singleton_iff, not_true_eq_false, and_false, not_false_eq_true]

theorem regular_of_mem_awayFromOtherSpecialValues {b y : RiemannSphere}
    (hy : y ∈ awayFromOtherSpecialValues b) (hne : y ≠ b) : y ∈ sphereRegularPatch := by
  change y ∉ ({(∞ : RiemannSphere), ((0 : ℂ) : RiemannSphere),
    ((1 : ℂ) : RiemannSphere)} \ {b}) at hy
  change y ∉ ({(∞ : RiemannSphere), ((0 : ℂ) : RiemannSphere),
    ((1 : ℂ) : RiemannSphere)} : Set RiemannSphere)
  exact fun h => hy ⟨h, hne⟩

namespace SpecialBasePowerChart

variable {b : RiemannSphere} (D : SpecialBasePowerChart b)

theorem center_coordinate : D.chart D.point = (0, (D.chart D.point).2) :=
  Prod.ext D.point_first_zero rfl

theorem center_mem_target : (0, (D.chart D.point).2) ∈ D.chart.target := by
  rw [← D.center_coordinate]
  exact D.chart.map_source' D.point_mem_source

/-- The central coordinate hyperplane is exactly the literal special fibre. -/
theorem projection_eq_base_iff (u : FM) (hu : u ∈ D.chart.target) :
    projectionSphere (D.chart.symm u) = b ↔ u.1 = 0 := by
  have hsource : projectionSphere (D.chart.symm u) ∈ D.baseChart.source :=
    D.source_projects_into _ (D.chart.symm.map_source' hu)
  constructor
  · intro h
    have hpower := D.power_equation u hu
    rw [h, D.base_value] at hpower
    exact (pow_eq_zero_iff D.degree_pos.ne').mp hpower.symm
  · intro h
    apply D.baseChart.toPartialEquiv.injOn hsource D.base_mem_source
    rw [D.power_equation u hu, h, zero_pow D.degree_pos.ne', D.base_value]

/-- Near the actual chart center, every noncentral coordinate point
lies over the original regular sphere domain, and conversely. -/
theorem eventually_model_regular_iff (hb : b ∉ sphereRegularPatch) :
    ∀ᶠ u in 𝓝 (0, (D.chart D.point).2), u ∈ D.chart.target ∧
      (projectionSphere (D.chart.symm u) ∈ sphereRegularPatch ↔ u.1 ≠ 0) := by
  have hx : D.chart.symm (0, (D.chart D.point).2) = D.point := by
    rw [← D.center_coordinate]
    exact D.chart.left_inv' D.point_mem_source
  have hc : ContinuousAt (fun u : FM => projectionSphere (D.chart.symm u))
      (0, (D.chart D.point).2) :=
    projectionSphere_continuous.continuousAt.comp
      ((D.chart.symm.contMDiffOn.contMDiffAt
        (D.chart.open_target.mem_nhds D.center_mem_target)).continuousAt)
  have hn : ∀ᶠ u in 𝓝 (0, (D.chart D.point).2),
      projectionSphere (D.chart.symm u) ∈ awayFromOtherSpecialValues b := by
    apply hc.eventually
    change ∀ᶠ y in 𝓝 (projectionSphere (D.chart.symm (0, (D.chart D.point).2))),
      y ∈ awayFromOtherSpecialValues b
    rw [hx, D.point_projection]
    exact (awayFromOtherSpecialValues b).isOpen.mem_nhds (mem_awayFromOtherSpecialValues_self b)
  filter_upwards [D.chart.open_target.mem_nhds D.center_mem_target, hn] with u hu haway
  refine ⟨hu, ?_⟩
  constructor
  · intro hregular hzero
    exact hb ((D.projection_eq_base_iff u hu).mpr hzero ▸ hregular)
  · intro hzero
    apply regular_of_mem_awayFromOtherSpecialValues haway
    exact fun h => hzero ((D.projection_eq_base_iff u hu).mp h)

theorem zero_mem_base_target : (0 : ℂ) ∈ D.baseChart.target := by
  rw [← D.base_value]
  exact D.baseChart.map_source' D.base_mem_source

theorem base_inverse_zero : D.baseChart.symm 0 = b := by
  rw [← D.base_value]
  exact D.baseChart.left_inv' D.base_mem_source

/-- A punctured coordinate neighborhood of zero is a genuine regular
sphere neighborhood in the original base chart. -/
theorem eventually_base_regular_iff (hb : b ∉ sphereRegularPatch) :
    ∀ᶠ t in 𝓝 (0 : ℂ), t ∈ D.baseChart.target ∧
      (D.baseChart.symm t ∈ sphereRegularPatch ↔ t ≠ 0) := by
  have hc : ContinuousAt D.baseChart.symm (0 : ℂ) :=
    (D.baseChart.symm.contMDiffOn.contMDiffAt
      (D.baseChart.open_target.mem_nhds D.zero_mem_base_target)).continuousAt
  have hn : ∀ᶠ t in 𝓝 (0 : ℂ), D.baseChart.symm t ∈ awayFromOtherSpecialValues b := by
    apply hc.eventually
    rw [D.base_inverse_zero]
    exact (awayFromOtherSpecialValues b).isOpen.mem_nhds (mem_awayFromOtherSpecialValues_self b)
  filter_upwards [D.baseChart.open_target.mem_nhds D.zero_mem_base_target, hn] with t ht haway
  refine ⟨ht, ?_⟩
  constructor
  · intro hregular hzero
    rw [hzero, D.base_inverse_zero] at hregular
    exact hb hregular
  · intro hzero
    apply regular_of_mem_awayFromOtherSpecialValues haway
    intro he
    have htzero : t = 0 := (D.baseChart.right_inv' ht).symm.trans
      ((congrArg (fun y => D.baseChart y) he).trans D.base_value)
    exact hzero htzero

end SpecialBasePowerChart

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
