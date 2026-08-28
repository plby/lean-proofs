import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeFormsBundle

/-!
# Detecting native cotangent values in an original chart

The inverse tangent trivialization is the inverse of the actual native
linear coordinate map on its chart domain. Equality of the original
cotangent coordinates there therefore implies equality in the original
cotangent fibre, without assuming a global trivialization.
-/

noncomputable section

open Bundle TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.LocalManifold

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Genuine native cotangent coordinates determine the original fibre
value at every point of the actual chart domain. -/
theorem eq_at_of_inCoordinates_eq {U : Opens M}
    (a b : ∀ x : U, Forms.Covector E M (x : M)) (x₀ : M) (x : U)
    (hx : (x : M) ∈ (chartAt E x₀).source)
    (h : Forms.inCoordinates E M a x₀ x = Forms.inCoordinates E M b x₀ x) :
    a x = b x := by
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E) : M → Type) x₀
  have hx' : (x : M) ∈ e.baseSet := by
    simpa only [e, TangentBundle.trivializationAt_baseSet] using hx
  ext v
  have he := congrArg (fun L : E →L[ℝ] ℂ =>
    L (e.continuousLinearMapAt ℝ (x : M) v)) h
  rw [Forms.inCoordinates_apply, Forms.inCoordinates_apply] at he
  change a x (e.symmL ℝ (x : M) (e.continuousLinearMapAt ℝ (x : M) v)) =
    b x (e.symmL ℝ (x : M) (e.continuousLinearMapAt ℝ (x : M) v)) at he
  simpa only [e.symmL_continuousLinearMapAt hx' v] using he

/-- Native coordinate values commute with literal restriction to a
smaller original open set, without changing the chart centre. -/
theorem inCoordinates_restriction {U V : Opens M} (h : U ≤ V)
    (a : ∀ x : V, Forms.Covector E M (x : M)) (x₀ : M) (x : U) :
    Forms.inCoordinates E M (fun y => a ⟨(y : M), h y.property⟩) x₀ x =
      Forms.inCoordinates E M a x₀ ⟨(x : M), h x.property⟩ := rfl

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.LocalManifold
