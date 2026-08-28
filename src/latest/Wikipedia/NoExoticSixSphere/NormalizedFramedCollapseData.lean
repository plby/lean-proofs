import Wikipedia.NoExoticSixSphere.FramedCollapseNormalComparison

/-!
# Actual collapse data with radius normalized to one

Rescale the original target compactification by the positive tube radius.
The normalized finite coordinates have the identity as their derivative
on the given normal frame. The map remains the actual rescaled collapse.
-/

noncomputable section

open Set Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel}
  (d : e.FramedCollapseData a)

def radiusCoordinates : e.NormalModel ≃L[ℝ] e.NormalModel :=
  (LinearEquiv.smulOfNeZero ℝ e.NormalModel d.radius d.radius_pos.ne').toContinuousLinearEquiv

theorem radiusCoordinates_apply (v : e.NormalModel) :
    d.radiusCoordinates v = d.radius • v := rfl

def normalizedMap : C(OnePoint (EuclideanSpace ℝ (Fin e.ambientDimension)),
    OnePoint e.NormalModel) :=
  d.radiusCoordinates.toHomeomorph.onePointCongr.toHomotopyEquiv.toFun.comp d.map

theorem normalizedMap_infty : d.normalizedMap OnePoint.infty = OnePoint.infty := by
  change d.radiusCoordinates.toHomeomorph.onePointCongr (d.map OnePoint.infty) = OnePoint.infty
  rw [d.map_infty]
  rfl

theorem normalizedMap_zero_fiber (y : OnePoint (EuclideanSpace ℝ (Fin e.ambientDimension))) :
    d.normalizedMap y = (↑(0 : e.NormalModel)) ↔
      ∃ x, (e.toFun x : OnePoint (EuclideanSpace ℝ (Fin e.ambientDimension))) = y := by
  have hz : d.radiusCoordinates.toHomeomorph.onePointCongr (↑(0 : e.NormalModel)) =
      (↑(0 : e.NormalModel)) := congrArg OnePoint.some (map_zero d.radiusCoordinates)
  change d.radiusCoordinates.toHomeomorph.onePointCongr (d.map y) = _ ↔ _
  rw [← hz, d.radiusCoordinates.toHomeomorph.onePointCongr.injective.eq_iff]
  exact d.zero_fiber y

theorem normalizedMap_local_formula (y : EuclideanSpace ℝ (Fin e.ambientDimension))
    (hy : y ∈ d.neighborhood) :
    d.normalizedMap (↑y) = (↑(d.normalizedCoordinates y) : OnePoint _) := by
  change d.radiusCoordinates.toHomeomorph.onePointCongr (d.map ↑y) = _
  rw [d.local_formula y hy]
  rfl

def normalized : e.FramedCollapseData a where
  radius := 1
  radius_pos := zero_lt_one
  neighborhood := d.neighborhood
  open_neighborhood := d.open_neighborhood
  range_subset := d.range_subset
  coordinates := d.normalizedCoordinates
  smooth_coordinates := d.contDiffOn_normalizedCoordinates
  surjective_differential := by
    intro y hy
    have hd₀ := d.smooth_coordinates.contDiffAt (d.open_neighborhood.mem_nhds hy)
    have hd := hd₀.differentiableAt (by simp)
    have he := hd.hasFDerivAt.const_smul d.radius
    change HasFDerivAt d.normalizedCoordinates _ y at he
    rw [he.fderiv]
    intro v
    obtain ⟨w, hw⟩ := d.surjective_differential y hy (d.radius⁻¹ • v)
    refine ⟨w, ?_⟩
    change d.radius • fderiv ℝ d.coordinates y w = v
    rw [hw, smul_smul, mul_inv_cancel₀ d.radius_pos.ne', one_smul]
  differential_frame := by
    intro x v
    rw [one_smul]
    exact congrArg (fun L : e.NormalModel →L[ℝ] e.NormalModel ↦ L v)
      (d.normalizedCoordinates_differential_frame x)
  map := d.normalizedMap
  map_infty := d.normalizedMap_infty
  zero_fiber := d.normalizedMap_zero_fiber
  local_formula := d.normalizedMap_local_formula

theorem normalized_radius : d.normalized.radius = 1 := rfl

end NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData
