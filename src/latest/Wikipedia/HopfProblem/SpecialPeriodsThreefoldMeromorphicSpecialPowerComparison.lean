import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicSpecialNeighborhoods
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicRegularDescent
import Wikipedia.HopfProblem.HolomorphicMeromorphicPartialDiffeomorphNaturality
import Wikipedia.HopfProblem.HolomorphicMeromorphicPullbackPowerProduct

/-!
# Actual meromorphic pullback in the special-fibre power coordinates

The original projection, its genuine source chart and its genuine sphere
chart form a commuting square with `(z, v) ↦ z^m`. Naturality of the native
fraction-stalk maps therefore identifies the transported arbitrary global
section with the power pullback of its already proved regular-base descent.
All chart and regular-base domains remain the actual open subsets.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

open HolomorphicMeromorphic HolomorphicMeromorphic.PartialBiholomorph

local notation "FM" => ℂ × ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ FM
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

namespace SpecialBasePowerChart

variable {b : RiemannSphere} (D : SpecialBasePowerChart b)

/-- The actual source-chart form of the proved special-fibre power equation. -/
theorem forward_power_equation (x : Threefold.Space) (hx : x ∈ D.chart.source) :
    D.baseChart (projectionSphere x) = (D.chart x).1 ^ D.degree := by
  have h := D.power_equation (D.chart x) (D.chart.map_source' hx)
  have hinv : D.chart.symm (D.chart x) = x := D.chart.left_inv' hx
  simpa only [hinv] using h

/-- The exact coordinate domain of a globally meromorphic source section. -/
def modelDomain : Opens FM := transportOpen IF IF D.chart ⊤

/-- The genuine arbitrary meromorphic section in the original source chart. -/
def modelSection (g : HolomorphicMeromorphic.Function IF Threefold.Space) :
    Section IF FM D.modelDomain := transportSection IF IF D.chart ⊤ g

/-- The exact sphere-chart domain of the regular-base section. -/
def baseDomain : Opens ℂ := transportOpen I₁ I₁ D.baseChart sphereRegularPatch

/-- The genuine regular-base section in the original special-value chart. -/
def baseSection (s : Section I₁ RiemannSphere sphereRegularPatch) :
    Section I₁ ℂ D.baseDomain := transportSection I₁ I₁ D.baseChart sphereRegularPatch s

theorem center_mem_modelDomain : (0, (D.chart D.point).2) ∈ D.modelDomain :=
  ⟨D.center_mem_target, by trivial⟩

/-- At a regular source point, genuine section transport and the actual
projection pullback agree with the literal power-projection pullback. -/
theorem modelSection_power_germ_at_source
    (g : HolomorphicMeromorphic.Function IF Threefold.Space)
    (s : Section I₁ RiemannSphere sphereRegularPatch)
    (hdescent : pullbackSection IF I₁ sphereProjection sphereProjection_isOpenMap
      sphereRegularPatch s = restrict IF Threefold.Space (show
        pullbackOpen IF I₁ sphereProjection sphereRegularPatch ≤ ⊤ from le_top) g)
    (x : Threefold.Space) (hx : x ∈ D.chart.source)
    (hregular : projectionSphere x ∈ sphereRegularPatch) :
    ∃ ht : (D.chart x).1 ^ D.degree ∈ D.baseDomain,
      D.modelSection g (transportPoint IF IF D.chart ⊤ ⟨x, by trivial⟩ hx) =
        germPullback IF I₁ (powerFstMap D.degree)
          (powerFstMap_isOpenMap D.degree D.degree_pos) (D.chart x)
          (D.baseSection s ⟨(D.chart x).1 ^ D.degree, ht⟩) := by
  have hbase : D.baseChart (projectionSphere x) ∈ D.baseDomain :=
    (transportPoint I₁ I₁ D.baseChart sphereRegularPatch ⟨projectionSphere x, hregular⟩
      (D.source_projects_into x hx)).property
  have ht : (D.chart x).1 ^ D.degree ∈ D.baseDomain :=
    D.forward_power_equation x hx ▸ hbase
  refine ⟨ht, ?_⟩
  apply (germEquiv IF IF D.chart x hx).injective
  have hnat := germEquiv_pullback_naturality IF I₁ IF I₁ D.chart D.baseChart
    sphereProjection sphereProjection_isOpenMap (powerFstMap D.degree)
    (powerFstMap_isOpenMap D.degree D.degree_pos) D.source_projects_into
    (fun y hy => D.forward_power_equation y hy) D.baseDomain (D.baseSection s) x hx ht hbase
  have htransport := germEquiv_transportSection I₁ I₁ D.baseChart sphereRegularPatch s
    ⟨projectionSphere x, hregular⟩ (D.source_projects_into x hx)
  have hdesc := congrArg
    (fun a : Section IF Threefold.Space
      (pullbackOpen IF I₁ sphereProjection sphereRegularPatch) => a ⟨x, hregular⟩) hdescent
  exact (germEquiv_transportSection IF IF D.chart ⊤ g ⟨x, by trivial⟩ hx).trans
    (hdesc.symm.trans
      (hnat.trans (congrArg
        (germPullback IF I₁ sphereProjection sphereProjection_isOpenMap x) htransport)).symm)

/-- The same equality at every actual coordinate point above the regular base. -/
theorem modelSection_power_germ
    (g : HolomorphicMeromorphic.Function IF Threefold.Space)
    (s : Section I₁ RiemannSphere sphereRegularPatch)
    (hdescent : pullbackSection IF I₁ sphereProjection sphereProjection_isOpenMap
      sphereRegularPatch s = restrict IF Threefold.Space (show
        pullbackOpen IF I₁ sphereProjection sphereRegularPatch ≤ ⊤ from le_top) g)
    (u : D.modelDomain)
    (hregular : projectionSphere (D.chart.symm u.val) ∈ sphereRegularPatch) :
    ∃ ht : u.val.1 ^ D.degree ∈ D.baseDomain,
      D.modelSection g u = germPullback IF I₁ (powerFstMap D.degree)
        (powerFstMap_isOpenMap D.degree D.degree_pos) u.val
        (D.baseSection s ⟨u.val.1 ^ D.degree, ht⟩) := by
  obtain ⟨x, hx, rfl⟩ := exists_transportPoint IF IF D.chart ⊤ u
  change projectionSphere (D.chart.symm (D.chart x.val)) ∈ sphereRegularPatch at hregular
  have hinv : D.chart.symm (D.chart x.val) = x.val := D.chart.left_inv' hx
  rw [hinv] at hregular
  exact D.modelSection_power_germ_at_source g s hdescent x.val hx hregular

/-- Near the actual special source point, the genuine coordinate section
is the power pullback of the actual regular descent at every noncentral point. -/
theorem eventually_modelSection_power_germ
    (g : HolomorphicMeromorphic.Function IF Threefold.Space)
    (hg : ¬ (MeromorphicRegularCover.constantRegularFibres g).Countable)
    (hb : b ∉ sphereRegularPatch) :
    ∀ᶠ u in 𝓝 (0, (D.chart D.point).2), ∃ hu : u ∈ D.modelDomain,
      u.1 ≠ 0 → ∃ ht : u.1 ^ D.degree ∈ D.baseDomain,
        D.modelSection g ⟨u, hu⟩ = germPullback IF I₁ (powerFstMap D.degree)
          (powerFstMap_isOpenMap D.degree D.degree_pos) u
          (D.baseSection (regularSphereDescent g hg) ⟨u.1 ^ D.degree, ht⟩) := by
  filter_upwards [D.eventually_model_regular_iff hb] with u hu
  refine ⟨⟨hu.1, by trivial⟩, fun hzero => ?_⟩
  exact D.modelSection_power_germ g (regularSphereDescent g hg)
    (regularSphereDescent_pullback g hg) ⟨u, hu.1, by trivial⟩ (hu.2.mpr hzero)

end SpecialBasePowerChart

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
