import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Regularized angles along unit-sphere curves

For `0 ≤ r < 1`, the angle `arccos (r ⟪x, γ(t)⟫)` is differentiable even
when the curve passes through `x` or `-x`. Its derivative has squared size
at most the squared speed of the curve. This avoids differentiating the
unregularized angle at its singular endpoints.
-/

open scoped ContDiff

namespace NoExoticSixSphere.SphereCurveAngle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem inner_tangent_sq_le {x u v : E} (hx : ‖x‖ = 1) (hu : ‖u‖ = 1)
    (huv : inner ℝ u v = 0) :
    (inner ℝ x v) ^ 2 ≤ (1 - (inner ℝ x u) ^ 2) * ‖v‖ ^ 2 := by
  let z := x - inner ℝ x u • u
  have hzv : inner ℝ z v = inner ℝ x v := by
    simp only [z, inner_sub_left, inner_smul_left, RCLike.conj_to_real, huv,
      mul_zero, sub_zero]
  have hzz : inner ℝ z z = 1 - (inner ℝ x u) ^ 2 := by
    simp only [z, inner_sub_left, inner_sub_right, inner_smul_left,
      inner_smul_right, RCLike.conj_to_real, real_inner_self_eq_norm_sq, hx, hu, one_pow]
    rw [real_inner_comm x u]
    ring
  have h := real_inner_mul_inner_self_le z v
  rw [hzv, hzz, real_inner_self_eq_norm_sq, ← pow_two] at h
  exact h

theorem inner_velocity_zero {γ : ℝ → E} {v : E} {t : ℝ}
    (hγ : HasDerivAt γ v t) (hn : ∀ s, ‖γ s‖ = 1) : inner ℝ (γ t) v = 0 := by
  have hd := hγ.norm_sq
  have he : (fun s ↦ ‖γ s‖ ^ 2) = fun _ : ℝ ↦ (1 : ℝ) := by
    funext s
    rw [hn s, one_pow]
  rw [he] at hd
  have hz := hd.unique (hasDerivAt_const t (1 : ℝ))
  linarith

theorem abs_scaled_inner_lt_one {x u : E} (hx : ‖x‖ = 1) (hu : ‖u‖ = 1)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) : |r * inner ℝ x u| < 1 := by
  have hi : |inner ℝ x u| ≤ 1 := by
    simpa only [Real.norm_eq_abs, hx, hu, one_mul] using norm_inner_le_norm (𝕜 := ℝ) x u
  rw [abs_mul, abs_of_nonneg hr]
  exact (mul_le_mul_of_nonneg_left hi hr).trans_lt (by simpa using hr1)

noncomputable def angle (x : E) (γ : ℝ → E) (r t : ℝ) : ℝ :=
  Real.arccos (r * inner ℝ x (γ t))

noncomputable def angleDerivative (x : E) (γ γ' : ℝ → E) (r t : ℝ) : ℝ :=
  -(r * inner ℝ x (γ' t)) / Real.sqrt (1 - (r * inner ℝ x (γ t)) ^ 2)

theorem hasDerivAt_angle {x : E} {γ γ' : ℝ → E} {r t : ℝ}
    (hx : ‖x‖ = 1) (hn : ‖γ t‖ = 1) (hr : 0 ≤ r) (hr1 : r < 1)
    (hγ : HasDerivAt γ (γ' t) t) :
    HasDerivAt (angle x γ r) (angleDerivative x γ γ' r t) t := by
  have ha := abs_lt.mp (abs_scaled_inner_lt_one hx hn hr hr1)
  have hi := ((hasDerivAt_const t x).inner ℝ hγ).const_mul r
  have hd := (Real.hasDerivAt_arccos (ne_of_gt ha.1) (ne_of_lt ha.2)).comp t hi
  convert! hd using 1
  simp only [angleDerivative, inner_zero_left]
  ring

theorem contDiff_angle {x : E} {γ : ℝ → E} {r : ℝ}
    (hx : ‖x‖ = 1) (hn : ∀ t, ‖γ t‖ = 1) (hr : 0 ≤ r) (hr1 : r < 1)
    (hγ : ContDiff ℝ ∞ γ) : ContDiff ℝ ∞ (angle x γ r) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  have ha := abs_lt.mp (abs_scaled_inner_lt_one hx (hn t) hr hr1)
  exact (Real.contDiffAt_arccos (ne_of_gt ha.1) (ne_of_lt ha.2)).comp t
    (contDiffAt_const.mul (contDiffAt_const.inner ℝ hγ.contDiffAt))

theorem angleDerivative_sq_le {x : E} {γ γ' : ℝ → E} {r t : ℝ}
    (hx : ‖x‖ = 1) (hn : ∀ s, ‖γ s‖ = 1) (hr : 0 ≤ r) (hr1 : r < 1)
    (hγ : HasDerivAt γ (γ' t) t) :
    (angleDerivative x γ γ' r t) ^ 2 ≤ ‖γ' t‖ ^ 2 := by
  have hi := inner_tangent_sq_le hx (hn t) (inner_velocity_zero hγ hn)
  have ha := abs_scaled_inner_lt_one hx (hn t) hr hr1
  have hd : 0 < 1 - (r * inner ℝ x (γ t)) ^ 2 := by
    have hs := (sq_lt_one_iff_abs_lt_one _).mpr ha
    linarith
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hi (sq_nonneg r)
  have hspeed := mul_le_mul_of_nonneg_right hr2 (sq_nonneg ‖γ' t‖)
  rw [angleDerivative, div_pow, neg_sq, Real.sq_sqrt hd.le]
  apply (div_le_iff₀ hd).mpr
  nlinarith

end NoExoticSixSphere.SphereCurveAngle
