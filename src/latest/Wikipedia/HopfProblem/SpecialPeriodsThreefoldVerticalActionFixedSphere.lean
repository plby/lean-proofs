import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedLocus
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedCurveImmersion

/-!
# The named fixed curve is an actual embedded Riemann sphere

The manifold structure is the two-axis atlas on the literal named
subspace of the original threefold. Its sphere parametrization is the
previously constructed native cusp curve, and both original triple
points are its marked endpoints.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold Threefold.space_t2Space

/-- The actual two-axis manifold atlas on the named fixed-curve subtype. -/
@[instance_reducible] def D₀_chartedSpace : ChartedSpace ℂ D₀ := FixedCurve.chartedSpace 1

theorem D₀_isManifold : letI := D₀_chartedSpace; IsManifold 𝓘(ℂ) ω D₀ :=
  FixedCurve.isManifold 1

/-- The genuine biholomorphism from the standard Riemann sphere to the
literal named fixed curve with its actual two-axis atlas. -/
def D₀_biholomorph :
    letI := D₀_chartedSpace
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) RiemannSphere D₀ ω :=
  FixedCurve.sphereBiholomorph 1

@[simp] theorem D₀_biholomorph_val (z : RiemannSphere) :
    letI := D₀_chartedSpace
    (D₀_biholomorph z : Space) = CuspGeometry.doubleCurveParametrization 1 z :=
  FixedCurve.sphereBiholomorph_val 1 z

theorem D₀_inclusion_holomorphic :
    letI := D₀_chartedSpace
    ContMDiff 𝓘(ℂ) IF ω (Subtype.val : D₀ → Space) :=
  FixedCurve.inclusion_holomorphic 1

theorem D₀_inclusion_isImmersion :
    letI := D₀_chartedSpace
    Manifold.IsImmersion 𝓘(ℂ) IF ω (Subtype.val : D₀ → Space) :=
  FixedCurve.inclusion_isImmersion 1

/-- The actual ambient sphere parametrization is a closed embedding. -/
theorem D₀_parametrization_isClosedEmbedding :
    IsClosedEmbedding (CuspGeometry.doubleCurveParametrization 1) :=
  CuspGeometry.doubleCurveParametrization_isClosedEmbedding 1

theorem D₀_parametrization_holomorphic :
    ContMDiff 𝓘(ℂ) IF ω (CuspGeometry.doubleCurveParametrization 1) :=
  CuspGeometry.doubleCurveParametrization_holomorphic 1

theorem D₀_parametrization_isImmersion :
    Manifold.IsImmersion 𝓘(ℂ) IF ω (CuspGeometry.doubleCurveParametrization 1) := by
  let := D₀_chartedSpace
  have heq : (Subtype.val : D₀ → Space) ∘ D₀_biholomorph =
      CuspGeometry.doubleCurveParametrization 1 := funext D₀_biholomorph_val
  rw [← heq]
  apply Manifold.IsImmersionOfComplement.isImmersion (F := ToricCharts.CoordinateSpace 2)
  apply RiemannSphere.standardCharts.immersion_of_comp_affineMaps _
    (continuous_subtype_val.comp D₀_biholomorph.contMDiff.continuous)
  intro b
  change Manifold.IsImmersionOfComplement (ToricCharts.CoordinateSpace 2) 𝓘(ℂ) IF ω
    ((Subtype.val ∘ (FixedCurve.charts 1).homeomorph) ∘
      RiemannSphere.standardCharts.affineMap b)
  rw [Function.comp_assoc, RiemannSphere.homeomorph_comp_standardCharts]
  cases b
  · exact FixedCurve.axisMap_inclusion_isImmersionOfComplement ToricSpace.referenceTriangle 1
  · exact FixedCurve.axisMap_inclusion_isImmersionOfComplement
      (ToricFan.Triangle.upperNeighbour 1) 1

theorem D₀_parametrization_range : Set.range (CuspGeometry.doubleCurveParametrization 1) = D₀ :=
  CuspGeometry.doubleCurveParametrization_range 1

@[simp] theorem D₀_biholomorph_zero :
    letI := D₀_chartedSpace
    (D₀_biholomorph ((0 : ℂ) : RiemannSphere) : Space) = CuspGeometry.lowerTriplePoint :=
  FixedCurve.sphereBiholomorph_zero 1

@[simp] theorem D₀_biholomorph_infty :
    letI := D₀_chartedSpace
    (D₀_biholomorph (∞ : RiemannSphere) : Space) = CuspGeometry.upperTriplePoint :=
  FixedCurve.sphereBiholomorph_infty 1

/-- The common fixed points are exactly the image of the actual native
closed holomorphic sphere embedding. -/
theorem fixedPoints_eq_sphere_range :
    letI := action
    MulAction.fixedPoints ℂˣ Space = Set.range (CuspGeometry.doubleCurveParametrization 1) :=
  fixedPoints_eq_D₀.trans D₀_parametrization_range.symm

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction
