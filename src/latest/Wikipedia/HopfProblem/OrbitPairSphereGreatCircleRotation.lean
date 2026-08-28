import Wikipedia.HopfProblem.OrbitPairSphereCanonicalSegment

/-!
# Rotated orthonormal planes and short great-circle logarithms

The tangent direction rotates with its base point. The resulting two vectors
remain orthonormal and describe every shifted portion of the same great circle.
On an angular interval strictly shorter than pi the actual endpoint logarithm
is exactly the angular displacement times this rotated direction.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.OrbitPair.SphereGreatCircle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def normalDirection (x y : E) (w t : ℝ) : E :=
  (-Real.sin (w * t)) • x + Real.cos (w * t) • y

theorem norm_normalDirection {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : inner ℝ x y = 0) (w t : ℝ) : ‖normalDirection x y w t‖ = 1 := by
  have hs : ‖normalDirection x y w t‖ ^ 2 = 1 := by
    rw [normalDirection, norm_sq_plane hx hy hxy, neg_sq, Real.sin_sq_add_cos_sq]
  nlinarith [norm_nonneg (normalDirection x y w t)]

theorem inner_curve_normalDirection {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : inner ℝ x y = 0) (w t : ℝ) :
    inner ℝ (curve x y w t) (normalDirection x y w t) = 0 := by
  have hyx : inner ℝ y x = 0 := by simpa only [real_inner_comm] using hxy
  simp only [curve, normalDirection, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
    hx, hy, hxy, hyx, one_pow, mul_one, mul_zero, add_zero, zero_add]
  ring

theorem curve_shift (x y : E) (w s t : ℝ) :
    curve (curve x y w s) (normalDirection x y w s) w t = curve x y w (s + t) := by
  simp only [curve, normalDirection, mul_add, Real.cos_add, Real.sin_add,
    smul_add, smul_smul]
  module

theorem curve_speed_mul (x y : E) (w c t : ℝ) :
    curve x y (w * c) t = curve x y w (c * t) := by
  simp only [curve, mul_assoc]

theorem inner_base_curve {x y : E} (hx : ‖x‖ = 1) (hxy : inner ℝ x y = 0)
    (w t : ℝ) : inner ℝ x (curve x y w t) = Real.cos (w * t) := by
  simp only [curve, inner_add_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hx, hxy, one_pow, mul_one, mul_zero, add_zero]

theorem logVector_curve {x y : E} (hx : ‖x‖ = 1) (hxy : inner ℝ x y = 0)
    {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) Real.pi) :
    SphereAngle.logVector x (curve x y 1 θ) = θ • y := by
  have hc : inner ℝ x (curve x y 1 θ) = Real.cos θ := by
    simpa only [one_mul] using inner_base_curve hx hxy (1 : ℝ) θ
  have ha : Real.arccos (Real.cos θ) = θ := Real.arccos_cos hθ.1.le hθ.2.le
  have hs : Real.sqrt (1 - Real.cos θ ^ 2) = Real.sin θ := by
    rw [← Real.sin_arccos, ha]
  have hsin : Real.sin θ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)
  have ht : curve x y 1 θ - Real.cos θ • x = Real.sin θ • y := by
    simp only [curve, one_mul]
    module
  rw [SphereAngle.logVector, hc, ht, SphereAngle.factor, ha, hs, smul_smul,
    div_mul_cancel₀ _ hsin]

end Wikipedia.HopfProblem.OrbitPair.SphereGreatCircle
