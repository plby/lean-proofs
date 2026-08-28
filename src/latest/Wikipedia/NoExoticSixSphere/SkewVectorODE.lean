import Wikipedia.NoExoticSixSphere.SkewExponentialConjugation

/-!
# Uniqueness for the actual skew-adjoint vector equation

The squared distance between two solutions of `v' = K v` is constant.
Consequently a solution with given initial value agrees with the actual
operator exponential applied to that vector.
-/

namespace NoExoticSixSphere.SkewVectorODE

open GLOrthonormalization CayleyTransform OrthogonalExponential

variable {n : ℕ}

theorem eq_of_solutions (K : SkewOperators n) {f g : ℝ → Vector n}
    (hf : ∀ t, HasDerivAt f ((K : Vector n →L[ℝ] Vector n) (f t)) t)
    (hg : ∀ t, HasDerivAt g ((K : Vector n →L[ℝ] Vector n) (g t)) t)
    (hzero : f 0 = g 0) (t : ℝ) : f t = g t := by
  have hd (r : ℝ) : HasDerivAt (fun s ↦ ‖f s - g s‖ ^ 2) 0 r := by
    have h := ((hf r).sub (hg r)).norm_sq
    simp only [Pi.sub_apply] at h
    rw [← map_sub, inner_skew_self, mul_zero] at h
    exact h
  have he := is_const_of_deriv_eq_zero (fun r ↦ (hd r).differentiableAt)
    (fun r ↦ (hd r).deriv) t 0
  rw [hzero, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] at he
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp he))

theorem hasDerivAt_exp_apply (K : SkewOperators n) (x : Vector n) (t : ℝ) :
    HasDerivAt (fun r ↦ (exp (r • K)).1.1 x)
      ((K : Vector n →L[ℝ] Vector n) ((exp (t • K)).1.1 x)) t := by
  have hd := HilbertSchmidt.hasDerivAt_apply (hasDerivAt_exp_smul_operator K t) x
  exact hd.congr_deriv (DFunLike.congr_fun (SkewConjugation.exp_smul_commute K t) x)

theorem solution_eq_exp_apply (K : SkewOperators n) {f : ℝ → Vector n}
    (hf : ∀ t, HasDerivAt f ((K : Vector n →L[ℝ] Vector n) (f t)) t) (t : ℝ) :
    f t = (exp (t • K)).1.1 (f 0) := by
  apply eq_of_solutions K hf (hasDerivAt_exp_apply K (f 0)) _ t
  rw [zero_smul, exp_zero]
  rfl

theorem exp_apply_of_zero (K : SkewOperators n) {x : Vector n}
    (hx : (K : Vector n →L[ℝ] Vector n) x = 0) (t : ℝ) :
    (exp (t • K)).1.1 x = x := by
  symm
  apply solution_eq_exp_apply K (f := fun _ ↦ x) _ t
  intro r
  rw [hx]
  exact hasDerivAt_const r x

end NoExoticSixSphere.SkewVectorODE
