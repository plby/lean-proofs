import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionMultiplicative
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedToricScaling
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspChart
import Wikipedia.HopfProblem.CuspPuncturedManifold

/-!
# Actual toric coordinate covers for the vertical action

Every original affine toric chart is restricted to the actual cusp tube,
then mapped through its original covering quotient and the actual open
cusp inclusion. These maps are locally biholomorphic for the unchanged
atlases. The global multiplicative action intertwines them with the
literal diagonal action of weights `(-1,0,1)`.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates

open ToricCharts ToricFan

local notation "E₃" => CoordinateSpace 3
local notation "I₃" => modelWithCornersSelf ℂ E₃
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "CD" => CuspGeometry.data

attribute [local instance] CuspGeometry.nativeChartedSpace Threefold.chartedSpace
  Threefold.space_isManifold

/-- The original open coordinate domain of the chosen cusp tube. -/
abbrev Domain := HolomorphicForms.Cusp.referenceDomain

/-- The original affine toric map, restricted to the actual open tube. -/
def tubeMap (a : Triangle) (z : Domain) : ToricSpace.Tube (CuspQuotient.disc (CD).radius) :=
  ⟨ToricSpace.inclusion a z, by
    change ToricSpace.time (ToricSpace.inclusion a z) ∈ Metric.ball 0 (CD).radius
    rw [ToricSpace.time_inclusion, Metric.mem_ball, dist_zero_right]
    exact z.property⟩

@[simp] theorem tubeMap_coe (a : Triangle) (z : Domain) :
    (tubeMap a z : ToricSpace.Space) = ToricSpace.inclusion a z := rfl

/-- The actual native cusp quotient of a toric coordinate point. -/
def quotientMap (a : Triangle) (z : Domain) : CuspGeometry.LocalSpace :=
  CuspQuotient.quotientMap (CD).correction (CD).radius (tubeMap a z)

/-- The actual coordinate covering into the unchanged glued threefold. -/
def globalMap (a : Triangle) : Domain → Threefold.Space :=
  CuspGeometry.inclusion ∘ quotientMap a

theorem toricInclusion_isLocalDiffeomorph (a : Triangle) :
    IsLocalDiffeomorph I₃ I₃ ω (ToricSpace.inclusion a) := by
  have he : (ToricSpace.parametrization a).symm ∈
      IsManifold.maximalAtlas I₃ ω ToricSpace.Space :=
    IsManifold.subset_maximalAtlas (mem_range_self a)
  intro z
  refine ⟨{
    toPartialEquiv := (ToricSpace.parametrization a).toPartialEquiv
    open_source := (ToricSpace.parametrization a).open_source
    open_target := (ToricSpace.parametrization a).open_target
    contMDiffOn_toFun := contMDiffOn_symm_of_mem_maximalAtlas he
    contMDiffOn_invFun := contMDiffOn_of_mem_maximalAtlas he }, mem_univ z, ?_⟩
  intro w _
  rfl

theorem tubeMap_isLocalDiffeomorph (a : Triangle) :
    IsLocalDiffeomorph I₃ I₃ ω (tubeMap a) :=
  isLocalDiffeomorph_restrictOpens I₃ I₃ (toricInclusion_isLocalDiffeomorph a) Domain
    (ToricSpace.tubeOpen (CuspQuotient.disc (CD).radius))
    (fun z hz => (tubeMap a ⟨z, hz⟩).property)

theorem quotientMap_isLocalDiffeomorph (a : Triangle) :
    IsLocalDiffeomorph I₃ I₃ ω (quotientMap a) := by
  let := CuspQuotient.chartedSpace (CD).correction (CD).radius (CD).radius_pos
    (CD).radius_lt_one (CD).holomorphic (CD).smallDrift
  let : ChartedSpace E₃ CuspGeometry.LocalSpace := CuspGeometry.nativeChartedSpace
  intro z
  exact (tubeMap_isLocalDiffeomorph a z).comp (K := I₃) (P := CuspGeometry.LocalSpace)
    (CuspUniformization.quotientMap_isLocalDiffeomorph (CD).correction (CD).radius
      (CD).radius_pos (CD).radius_lt_one (CD).holomorphic (CD).smallDrift (tubeMap a z))

theorem globalMap_isLocalDiffeomorph (a : Triangle) :
    IsLocalDiffeomorph I₃ IF ω (globalMap a) := by
  intro z
  exact (quotientMap_isLocalDiffeomorph a z).comp (K := IF) (P := Threefold.Space)
    (CuspGeometry.inclusion_isLocalDiffeomorph (quotientMap a z))

theorem globalMap_holomorphic (a : Triangle) : ContMDiff I₃ IF ω (globalMap a) :=
  (globalMap_isLocalDiffeomorph a).contMDiff

/-- The actual differential of the coordinate cover is a complex-linear
equivalence onto the native tangent space of the threefold. -/
def tangentEquiv (a : Triangle) (z : Domain) :
    E₃ ≃L[ℂ] TangentSpace IF (globalMap a z) :=
  (globalMap_isLocalDiffeomorph a z).mfderivToContinuousLinearEquiv (by simp)

@[simp] theorem tangentEquiv_apply (a : Triangle) (z : Domain) (v : E₃) :
    tangentEquiv a z v = mfderiv I₃ IF (globalMap a) z v := rfl

/-- The literal diagonal complex-linear map in every toric chart. -/
def diagonal (u : ℂˣ) : E₃ →L[ℂ] E₃ :=
  ContinuousLinearMap.pi fun j =>
    (![(u : ℂ)⁻¹, 1, (u : ℂ)] j) • ContinuousLinearMap.proj j

@[simp] theorem diagonal_apply (u : ℂˣ) (z : E₃) :
    diagonal u z = ![(u : ℂ)⁻¹ * z 0, z 1, (u : ℂ) * z 2] := by
  ext j
  fin_cases j <;> simp [diagonal]

theorem diagonal_eq_scale (u : ℂˣ) (a : Triangle) (z : E₃) :
    diagonal u z = ToricSpace.scale a (ToricSpace.fibreMultiplier ![1, u]) z := by
  rw [diagonal_apply, FixedToric.scale_verticalMultiplier]

@[simp] theorem time_diagonal (u : ℂˣ) (z : E₃) :
    Triangle.time (diagonal u z) = Triangle.time z := by
  rw [diagonal_apply]
  change (u : ℂ)⁻¹ * z 0 * z 1 * ((u : ℂ) * z 2) = z 0 * z 1 * z 2
  field_simp

/-- The diagonal map preserves the full actual cusp coordinate domain. -/
def coordinateAction (u : ℂˣ) (z : Domain) : Domain :=
  ⟨diagonal u z, by
    change ‖Triangle.time (diagonal u z)‖ < (CD).radius
    rw [time_diagonal]
    exact z.property⟩

@[simp] theorem coordinateAction_coe (u : ℂˣ) (z : Domain) :
    (coordinateAction u z : E₃) = diagonal u z := rfl

theorem tubeMap_coordinateAction (s : ℂ) (a : Triangle) (z : Domain) :
    tubeMap a (coordinateAction (Exponential.normalizedExponential s) z) =
      Cusp.tubeFlow (CuspQuotient.disc (CD).radius) s (tubeMap a z) := by
  apply Subtype.ext
  change ToricSpace.inclusion a (diagonal (Exponential.normalizedExponential s) z) =
    Cusp.toricFlow s (ToricSpace.inclusion a z)
  rw [Cusp.toricFlow_inclusion, FixedToric.multiplier_eq_verticalMultiplier,
    diagonal_eq_scale _ a]

/-- Exact equivariance through both actual quotient and gluing maps. -/
theorem globalMap_coordinateAction (u : ℂˣ) (a : Triangle) (z : Domain) :
    actionBiholomorph u (globalMap a z) = globalMap a (coordinateAction u z) := by
  obtain ⟨s, rfl⟩ := Exponential.normalizedExponential_surjective u
  rw [actionBiholomorph_exponential]
  change flow s (CuspGeometry.inclusion (quotientMap a z)) = _
  rw [flow_cusp]
  change CuspGeometry.inclusion
    (Cusp.flow (CD).correction (CD).radius s
      (CuspQuotient.quotientMap (CD).correction (CD).radius (tubeMap a z))) = _
  rw [Cusp.flow_quotientMap, ← tubeMap_coordinateAction]
  rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates
