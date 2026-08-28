import Wikipedia.NoExoticSixSphere.SkewVectorODE
import Wikipedia.NoExoticSixSphere.SkewSpectralPlane
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Exponentials on actual rotation planes

The vector ODE proves the sine-cosine formula for the operator exponential on
an invariant rotation plane. An antipodal endpoint forces the positive rotation
speed to be an odd multiple of `π`.
-/

namespace NoExoticSixSphere.SkewRotationExponential

open GLOrthonormalization CayleyTransform OrthogonalExponential SkewVectorODE

variable {n : ℕ}

theorem hasDerivAt_rotation (K : SkewOperators n) {α : ℝ} {x y : Vector n}
    (hx : (K : Vector n →L[ℝ] Vector n) x = α • y)
    (hy : (K : Vector n →L[ℝ] Vector n) y = (-α) • x) (t : ℝ) :
    HasDerivAt (fun r ↦ Real.cos (α * r) • x + Real.sin (α * r) • y)
      ((K : Vector n →L[ℝ] Vector n) (Real.cos (α * t) • x + Real.sin (α * t) • y)) t := by
  have hl : HasDerivAt (fun r : ℝ ↦ α * r) α t := by
    simpa only [mul_one, id_eq] using! (hasDerivAt_id t).const_mul α
  have hc := (Real.hasDerivAt_cos (α * t)).comp t hl
  have hs := (Real.hasDerivAt_sin (α * t)).comp t hl
  apply ((hc.smul_const x).add (hs.smul_const y)).congr_deriv
  rw [map_add, map_smul, map_smul, hx, hy, smul_smul, smul_smul]
  rw [mul_neg, neg_mul, add_comm]

theorem exp_apply_rotation (K : SkewOperators n) {α : ℝ} {x y : Vector n}
    (hx : (K : Vector n →L[ℝ] Vector n) x = α • y)
    (hy : (K : Vector n →L[ℝ] Vector n) y = (-α) • x) (t : ℝ) :
    (exp (t • K)).1.1 x = Real.cos (α * t) • x + Real.sin (α * t) • y := by
  have he := solution_eq_exp_apply K (hasDerivAt_rotation K hx hy) t
  simpa only [mul_zero, Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero] using he.symm

theorem cos_speed_eq_neg_one (K : SkewOperators n) {α : ℝ} {x y : Vector n}
    (hx : (K : Vector n →L[ℝ] Vector n) x = α • y)
    (hy : (K : Vector n →L[ℝ] Vector n) y = (-α) • x)
    (hn : ‖x‖ = 1) (hxy : inner ℝ x y = 0)
    (he : (exp K).1.1 = -(1 : Vector n →L[ℝ] Vector n)) : Real.cos α = -1 := by
  have hp := exp_apply_rotation K hx hy 1
  rw [one_smul, he, mul_one] at hp
  change -x = Real.cos α • x + Real.sin α • y at hp
  have hi := congrArg (fun z ↦ inner ℝ x z) hp
  simpa only [inner_neg_right, inner_add_right, inner_smul_right,
    real_inner_self_eq_norm_sq, hn, one_pow, hxy, mul_one, mul_zero, add_zero] using hi.symm

theorem speed_eq_odd_pi {α : ℝ} (hα : 0 < α) (hc : Real.cos α = -1) :
    ∃ m : ℕ, α = (2 * (m : ℝ) + 1) * Real.pi := by
  obtain ⟨k, hk⟩ := Real.cos_eq_neg_one_iff.mp hc
  have hk0 : 0 ≤ k := by
    by_contra h
    have hk1 : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
    nlinarith [Real.pi_pos]
  lift k to ℕ using hk0
  simp only [Int.cast_natCast] at hk
  refine ⟨k, ?_⟩
  nlinarith [hk]

theorem speed_gap {α : ℝ} (hα : 0 < α) (hc : Real.cos α = -1) :
    α = Real.pi ∨ 3 * Real.pi ≤ α := by
  obtain ⟨m, hm⟩ := speed_eq_odd_pi hα hc
  rcases Nat.eq_zero_or_pos m with h | h
  · left
    simp only [h, Nat.cast_zero, mul_zero, zero_add, one_mul] at hm
    exact hm
  · right
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast h
    nlinarith [Real.pi_pos]

end NoExoticSixSphere.SkewRotationExponential
