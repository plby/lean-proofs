import Wikipedia.NoExoticSixSphere.OrthogonalPolygonFirstVariation

/-!
# Actual vertex variations in arbitrary skew directions

Each interior vertex is multiplied by a one-parameter exponential. The
resulting curve is smooth in the original product Cayley atlas, and its
body derivative realizes the prescribed skew operator at every vertex.
The two fixed endpoints have zero variation.
-/

open scoped Manifold ContDiff

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization OrthogonalPaths CayleyTransform OrthogonalExponential
  OrthogonalVertexSpace OrthogonalFirstVariation HilbertSchmidt

variable {n m : ℕ}

noncomputable def vertexVariation (v : Space n m) (W : Model n m) (s : ℝ) : Space n m :=
  fun i ↦ v i * exp (s • W i)

theorem contMDiff_vertexVariation (v : Space n m) (W : Model n m) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Model n m) ∞ (vertexVariation v W) := by
  apply contMDiff_iff_coordinatewise.mpr
  intro i
  exact contMDiff_const.mul (contMDiff_exp_smul (W i))

theorem vertexVariation_zero (v : Space n m) (W : Model n m) : vertexVariation v W 0 = v := by
  funext i
  simp only [vertexVariation, zero_smul, exp_zero, mul_one]

noncomputable def vertexField (W : Model n m) : Fin (m + 2) → SkewOperators n :=
  Fin.cons 0 (Fin.snoc W 0)

theorem vertexField_zero (W : Model n m) : vertexField W 0 = 0 := rfl

theorem vertexField_last (W : Model n m) : vertexField W (Fin.last (m + 1)) = 0 := by
  change Fin.snoc (α := fun _ : Fin (m + 1) ↦ SkewOperators n) W 0 (Fin.last m) = 0
  simp only [Fin.snoc_last]

theorem vertexField_interior (W : Model n m) (i : Fin m) :
    vertexField W i.castSucc.succ = W i := by
  change Fin.snoc (α := fun _ : Fin (m + 1) ↦ SkewOperators n) W 0 i.castSucc = W i
  simp only [Fin.snoc_castSucc]

theorem vertices_vertexVariation (a b : OrthogonalOperators n)
    (v : Space n m) (W : Model n m) (s : ℝ) (i : Fin (m + 2)) :
    vertices a b (vertexVariation v W s) i =
      vertices a b v i * exp (s • vertexField W i) := by
  induction i using Fin.cases with
  | zero => simp only [vertices_zero, vertexField_zero, smul_zero, exp_zero, mul_one]
  | succ i =>
    induction i using Fin.lastCases with
    | last =>
      change vertices a b (vertexVariation v W s) (Fin.last (m + 1)) =
        vertices a b v (Fin.last (m + 1)) * exp (s • vertexField W (Fin.last (m + 1)))
      simp only [vertices_last, vertexField_last, smul_zero, exp_zero, mul_one]
    | cast i =>
      simp only [vertices_interior, vertexField_interior]
      rfl

theorem endpointBody_left_exp_zero (a : OrthogonalOperators n) (K : SkewOperators n) :
    endpointBody (fun r ↦ a * exp (r • K)) 0 = (K : Vector n →L[ℝ] Vector n) := by
  unfold endpointBody
  rw [(OrthogonalPathEnergy.hasDerivAt_left_exp a K 0).deriv]
  simp only [zero_smul, exp_zero, mul_one]
  apply ContinuousLinearMap.ext
  intro x
  exact inverse_apply_self a ((K : Vector n →L[ℝ] Vector n) x)

theorem endpointBody_vertexVariation (a b : OrthogonalOperators n)
    (v : Space n m) (W : Model n m) (i : Fin (m + 2)) :
    endpointBody (fun r ↦ vertices a b (vertexVariation v W r) i) 0 =
      (vertexField W i : Vector n →L[ℝ] Vector n) := by
  have heq : (fun r ↦ vertices a b (vertexVariation v W r) i) =
      (fun r ↦ vertices a b v i * exp (r • vertexField W i)) := by
    funext r
    exact vertices_vertexVariation a b v W r i
  rw [heq, endpointBody_left_exp_zero]

theorem hasDerivAt_energy_vertexVariation_edges (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (v : Space n m) (hv : v ∈ admissible a b m) (W : Model n m) :
    HasDerivAt (fun r ↦ energy a b τ (vertexVariation v W r))
      (∑ i : Fin (m + 1),
        2 * (innerForm (generator a b v i : Vector n →L[ℝ] Vector n)
          (vertexField W i.succ : Vector n →L[ℝ] Vector n) -
          innerForm (generator a b v i : Vector n →L[ℝ] Vector n)
            (vertexField W i.castSucc : Vector n →L[ℝ] Vector n)) /
          (τ i.succ - τ i.castSucc)) 0 := by
  have hs : vertexVariation v W 0 ∈ admissible a b m := by rwa [vertexVariation_zero]
  simpa only [vertexVariation_zero, endpointBody_vertexVariation] using
    hasDerivAt_energy a b τ (contMDiff_vertexVariation v W) hs

end NoExoticSixSphere.OrthogonalPolygon
