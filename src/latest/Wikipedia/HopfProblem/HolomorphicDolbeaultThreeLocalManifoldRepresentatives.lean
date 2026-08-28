import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeClosedCoordinates

/-!
# Original chart representatives at actual manifold points

The coordinate representative of a native form agrees with its original
cotangent coordinates wherever the point lies in the original chart and
section domains. Only the actual inverse-chart identity is used.
-/

noncomputable section

open Bundle TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.LocalManifold

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

omit [NormedSpace ℝ E] in
/-- An actual chart-domain point of an original open set gives a point
of exactly that open set's original coordinate domain. -/
theorem chart_mem_coordinateDomain (U : Opens M) (x₀ x : M)
    (hx : x ∈ (chartAt E x₀).source) (hU : x ∈ U) :
    chartAt E x₀ x ∈ ClosedForms.coordinateDomain E M U x₀ := by
  refine ⟨(chartAt E x₀).map_source hx, ?_⟩
  change (chartAt E x₀).symm (chartAt E x₀ x) ∈ U
  simpa only [(chartAt E x₀).left_inv hx] using hU

variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual chart representative evaluated at a manifold point is
its original native cotangent coordinate, with the same chart centre. -/
theorem coordinateForm_at_chart (U : Opens M)
    (a : ∀ x : U, Forms.Covector E M (x : M)) (x₀ : M) (x : U)
    (hx : (x : M) ∈ (chartAt E x₀).source) :
    ClosedForms.coordinateForm E M U a x₀ (chartAt E x₀ (x : M)) =
      Forms.inCoordinates E M a x₀ x := by
  have hz := chart_mem_coordinateDomain E M U x₀ x hx x.property
  have hpoint : (⟨(chartAt E x₀).symm (chartAt E x₀ (x : M)), hz.2⟩ : U) = x :=
    Subtype.ext ((chartAt E x₀).left_inv hx)
  rw [ClosedForms.coordinateForm_eq_inCoordinates E M U a x₀
    (chartAt E x₀ (x : M)) hz, hpoint]

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.LocalManifold
