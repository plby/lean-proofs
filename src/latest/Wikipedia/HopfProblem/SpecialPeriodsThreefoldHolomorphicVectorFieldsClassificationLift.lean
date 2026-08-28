import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicVectorFieldsClassificationPullback
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicVectorFieldsVerticalDescent
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsDetectionCover

/-!
# The native lift to the regular period-vector cover

A genuine holomorphic vector field on the constructed threefold lifts
through the actual locally biholomorphic period-vector cover. Since the
preferred charts of this cover are constant, the literal native tangent
values of the lift form a holomorphic vector-valued function.
-/

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields.Classification

section ConstantCharts

variable (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]

/-- When the actual preferred charts are constant, the literal native
values of a holomorphic tangent section are holomorphic. -/
theorem nativeValue_holomorphic_of_constant_charts
    (hchart : ∀ x y : M, chartAt E x = chartAt E y)
    (v : Wikipedia.HopfProblem.HolomorphicVectorFields.Field E M) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x => (v x : E)) := by
  intro x₀
  apply (Wikipedia.HopfProblem.HolomorphicVectorFields.inCoordinates_holomorphicAt
    E M v x₀).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun x => by
    rw [Wikipedia.HopfProblem.HolomorphicVectorFields.inCoordinates,
      HolomorphicDifferentialForms.tangent_trivialization_eq_of_constant_charts
        E M hchart x₀ x]
    exact (Wikipedia.HopfProblem.HolomorphicVectorFields.tangentCoordinates_self
      E M x (v x)).symm

end ConstantCharts

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  HolomorphicForms.RegularCover.coverChartedSpace
  HolomorphicForms.RegularCover.cover_isManifold

/-- Lift through the actual period-lattice, triangle-quotient, and inclusion
map, using its genuine invertible manifold differential. -/
noncomputable def regularLift (v : Threefold.HolomorphicVectorFields.Field) :
    Wikipedia.HopfProblem.HolomorphicVectorFields.Field
      (ℂ × ComplexPlane₂) HolomorphicForms.RegularCover.Cover :=
  pullback HolomorphicForms.RegularCover.globalCover
    HolomorphicForms.RegularCover.globalCover_isLocalDiffeomorph v

/-- The genuine differential of the cover sends the lifted value back to
the original vector field. -/
theorem regularLift_map (v : Threefold.HolomorphicVectorFields.Field)
    (x : HolomorphicForms.RegularCover.Cover) :
    mfderiv IF IF HolomorphicForms.RegularCover.globalCover x (regularLift v x) =
      v (HolomorphicForms.RegularCover.globalCover x) :=
  pullback_map HolomorphicForms.RegularCover.globalCover
    HolomorphicForms.RegularCover.globalCover_isLocalDiffeomorph v x

/-- The original scalar base component and two native period-vector
components of the lifted field, with no replacement tangent coordinates. -/
noncomputable def regularCoefficients (v : Threefold.HolomorphicVectorFields.Field)
    (x : HolomorphicForms.RegularCover.Cover) : ℂ × ComplexPlane₂ :=
  regularLift v x

/-- The native coefficients are holomorphic for the unchanged cover atlas. -/
theorem regularCoefficients_holomorphic (v : Threefold.HolomorphicVectorFields.Field) :
    ContMDiff IF IF ω (regularCoefficients v) :=
  nativeValue_holomorphic_of_constant_charts
    (ℂ × ComplexPlane₂) HolomorphicForms.RegularCover.Cover
    HolomorphicForms.RegularCover.cover_chart_eq (regularLift v)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields.Classification
