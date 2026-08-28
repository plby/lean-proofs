import Wikipedia.NoExoticSixSphere.OrthogonalPolygonStationarity

/-!
# First variation along an exponential vertex curve at every parameter

The body derivative of `a * exp(s K)` is constantly `K`. Consequently the
polygon energy derivative along a fixed vertex direction pairs that direction
with the velocity jumps at the current vertices, not just at parameter zero.
-/

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization OrthogonalPaths CayleyTransform OrthogonalExponential
  OrthogonalVertexSpace OrthogonalFirstVariation HilbertSchmidt

variable {n m : ℕ}

theorem endpointBody_left_exp_at (a : OrthogonalOperators n) (K : SkewOperators n) (s : ℝ) :
    endpointBody (fun r ↦ a * exp (r • K)) s = (K : Vector n →L[ℝ] Vector n) := by
  unfold endpointBody
  rw [(OrthogonalPathEnergy.hasDerivAt_left_exp a K s).deriv]
  apply ContinuousLinearMap.ext
  intro x
  exact inverse_apply_self (a * exp (s • K)) ((K : Vector n →L[ℝ] Vector n) x)

theorem endpointBody_vertexVariation_at (a b : OrthogonalOperators n)
    (v : Space n m) (W : Model n m) (s : ℝ) (i : Fin (m + 2)) :
    endpointBody (fun r ↦ vertices a b (vertexVariation v W r) i) s =
      (vertexField W i : Vector n →L[ℝ] Vector n) := by
  have heq : (fun r ↦ vertices a b (vertexVariation v W r) i) =
      (fun r ↦ vertices a b v i * exp (r • vertexField W i)) := by
    funext r
    exact vertices_vertexVariation a b v W r i
  rw [heq, endpointBody_left_exp_at]

theorem hasDerivAt_energy_vertexVariation_at (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (v : Space n m) (W : Model n m) (s : ℝ)
    (hs : vertexVariation v W s ∈ admissible a b m) :
    HasDerivAt (fun r ↦ energy a b τ (vertexVariation v W r))
      (2 * ∑ j : Fin m,
        innerForm (velocityJump a b τ (vertexVariation v W s) j : Vector n →L[ℝ] Vector n)
          (W j : Vector n →L[ℝ] Vector n)) s := by
  have hd := hasDerivAt_energy a b τ (contMDiff_vertexVariation v W) hs
  simp only [endpointBody_vertexVariation_at] at hd
  rw [sum_variation_edges] at hd
  exact hd

end NoExoticSixSphere.OrthogonalPolygon
