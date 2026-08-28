import Wikipedia.HopfProblem.ThreefoldReducedEllipticDivisorLocal
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorSourceOrdersLocal

/-!
# Comparing the actual elliptic base charts with the finite sphere chart

Each original elliptic base chart differs from the centered finite
coordinate by an analytic nonzero factor near the marked value.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.ProjectionLocalUnit

open Elliptic EllipticGeometry ReducedEllipticDivisor

def center : Kind → ℂ
  | .three => 0
  | .four => 1

theorem sphereValue_eq_coe (j : Kind) : sphereValue j = (center j : RiemannSphere) := by
  cases j <;> simp [center]

theorem sphereValue_mem_source (j : Kind) : sphereValue j ∈ (sphereChart j).source := by
  obtain ⟨x, hx⟩ := projectionSphere_surjective (sphereValue j)
  have hp := FibreClassification.elliptic_fibre_mem_liftedPatch j x hx
  have h := projectionSphere_inclusion_mem_sphereChart_source j (localPoint j x)
  rw [inclusion_localPoint j hp, hx] at h
  exact h

/-- The standard finite parametrization, in the sphere's original atlas. -/
theorem coe_isLocalDiffeomorph :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω ((↑) : ℂ → RiemannSphere) := by
  have hp : (RiemannSphere.standardCharts.parametrization false).symm ∈
      IsManifold.maximalAtlas 𝓘(ℂ) ω RiemannSphere :=
    IsManifold.subset_maximalAtlas (mem_range_self false)
  let p : PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ℂ RiemannSphere ω :=
    { toPartialEquiv := (RiemannSphere.standardCharts.parametrization false).toPartialEquiv
      open_source := (RiemannSphere.standardCharts.parametrization false).open_source
      open_target := (RiemannSphere.standardCharts.parametrization false).open_target
      contMDiffOn_toFun := (RiemannSphere.standardCharts.affineMap_holomorphic false).contMDiffOn
      contMDiffOn_invFun := contMDiffOn_of_mem_maximalAtlas hp }
  intro z
  exact ⟨p, mem_univ z, fun _ _ => rfl⟩

def chartExpression (j : Kind) (z : ℂ) : ℂ := sphereChart j (z : RiemannSphere)

theorem chartExpression_zero (j : Kind) : chartExpression j (center j) = 0 := by
  rw [chartExpression, ← sphereValue_eq_coe, sphereChart_value]

theorem chartExpression_localDiffeomorph (j : Kind) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (chartExpression j) (center j) := by
  exact (coe_isLocalDiffeomorph (center j)).comp
    (K := 𝓘(ℂ)) (P := ℂ)
    ((sphereChart j).isLocalDiffeomorphAt _ _ _
      (by rw [← sphereValue_eq_coe]; exact sphereValue_mem_source j))

theorem exists_unit_near_center (j : Kind) :
    ∃ (V : Set ℂ) (u : ℂ → ℂ), IsOpen V ∧ center j ∈ V ∧ ContinuousOn u V ∧
      ∀ z ∈ V, u z ≠ 0 ∧ chartExpression j z = (z - center j) * u z := by
  have hd := chartExpression_localDiffeomorph j
  have ha := hd.contMDiffAt.contDiffAt.analyticAt
  have ho := MuTorsor.SourceOrders.order_eq_one_of_isLocalDiffeomorph hd
    (chartExpression_zero j)
  obtain ⟨u, hu, hne, he⟩ := ha.analyticOrderAt_eq_natCast.mp ho
  have hn : ∀ᶠ z in 𝓝 (center j), AnalyticAt ℂ u z ∧ u z ≠ 0 ∧
      chartExpression j z = (z - center j) * u z := by
    filter_upwards [hu.eventually_analyticAt, hu.continuousAt.eventually_ne hne, he]
      with z haz hnz hez
    exact ⟨haz, hnz, by simpa only [pow_one, smul_eq_mul] using hez⟩
  obtain ⟨V, hV, hVo, hcV⟩ := eventually_nhds_iff.mp hn
  exact ⟨V, u, hVo, hcV, fun z hz => (hV z hz).1.continuousAt.continuousWithinAt,
    fun z hz => (hV z hz).2⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.ProjectionLocalUnit
