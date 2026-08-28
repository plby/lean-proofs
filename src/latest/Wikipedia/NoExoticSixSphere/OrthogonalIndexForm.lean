import Wikipedia.NoExoticSixSphere.OrthogonalCommutator
import Wikipedia.NoExoticSixSphere.HilbertSchmidtIntegration

/-!
# The quadratic index form for an orthogonal exponential path

This module proves its completed-square formula and the integration-by-parts
identity used to identify it with the second derivative of energy. No Morse
index or global homotopy consequence is asserted here.
-/

namespace NoExoticSixSphere.OrthogonalIndexForm

open GLOrthonormalization CayleyTransform HilbertSchmidt OrthogonalCommutator

variable {n : ℕ}

noncomputable def density (K : SkewOperators n)
    (W W' : Vector n →L[ℝ] Vector n) : ℝ :=
  squareNorm W' + innerForm W' (commutator (K : Vector n →L[ℝ] Vector n) W)

theorem density_completedSquare (K : SkewOperators n)
    (W W' : Vector n →L[ℝ] Vector n) :
    density K W W' =
      squareNorm (W' + (1 / 2 : ℝ) • commutator (K : Vector n →L[ℝ] Vector n) W) -
        (1 / 4 : ℝ) * squareNorm (commutator (K : Vector n →L[ℝ] Vector n) W) := by
  rw [squareNorm_add, squareNorm_smul, innerForm_smul_right]
  unfold density
  ring

theorem continuous_commutator (K : SkewOperators n)
    {W : ℝ → Vector n →L[ℝ] Vector n} (hW : Continuous W) :
    Continuous (fun t ↦ commutator (K : Vector n →L[ℝ] Vector n) (W t)) :=
  (continuous_const.clm_comp hW).sub (hW.clm_comp continuous_const)

theorem integral_secondDerivative (K : SkewOperators n)
    {W W' W'' : ℝ → Vector n →L[ℝ] Vector n}
    (hW : Continuous W) (hW' : Continuous W') (hW'' : Continuous W'')
    (hdW : ∀ t, HasDerivAt W (W' t) t) (hdW' : ∀ t, HasDerivAt W' (W'' t) t)
    (l u : ℝ) (hl : W l = 0) (hu : W u = 0) :
    (-2 * ∫ t in l..u, innerForm
      (W'' t + commutator (K : Vector n →L[ℝ] Vector n) (W' t)) (W t)) =
      2 * ∫ t in l..u, density K (W t) (W' t) := by
  have hacc := continuous_innerForm_comp hW'' hW
  have hcross := continuous_innerForm_comp hW' (continuous_commutator K hW)
  have hspeed := continuous_innerForm_comp hW' hW'
  have hparts := integral_innerForm_derivative hW' hW hW'' hW' hdW' hdW l u
  have hz (A : Vector n →L[ℝ] Vector n) : innerForm A 0 = 0 := by simp [innerForm]
  rw [hl, hu, hz, hz, sub_self, zero_sub] at hparts
  have heq : (∫ t in l..u, innerForm
      (W'' t + commutator (K : Vector n →L[ℝ] Vector n) (W' t)) (W t)) =
      (∫ t in l..u, innerForm (W'' t) (W t)) -
        ∫ t in l..u, innerForm (W' t) (commutator (K : Vector n →L[ℝ] Vector n) (W t)) := by
    calc
      _ = ∫ t in l..u, innerForm (W'' t) (W t) -
          innerForm (W' t) (commutator (K : Vector n →L[ℝ] Vector n) (W t)) := by
        apply intervalIntegral.integral_congr
        intro t _
        dsimp only
        rw [innerForm_add_left, innerForm_commutator]
        rfl
      _ = _ := intervalIntegral.integral_sub
        (hacc.intervalIntegrable l u) (hcross.intervalIntegrable l u)
  have hsum : (∫ t in l..u, density K (W t) (W' t)) =
      (∫ t in l..u, innerForm (W' t) (W' t)) +
        ∫ t in l..u, innerForm (W' t) (commutator (K : Vector n →L[ℝ] Vector n) (W t)) :=
    intervalIntegral.integral_add (hspeed.intervalIntegrable l u) (hcross.intervalIntegrable l u)
  rw [heq, hsum, hparts]
  ring

end NoExoticSixSphere.OrthogonalIndexForm
