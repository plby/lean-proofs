import Wikipedia.HopfProblem.OrbitPairSphereNormalVariation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Two independent endpoint-zero modes for the sphere index form

The sine modes of frequencies π and 2π are orthogonal in the actual interval
integral. Their derivative energies are computed as well. Both modes are
needed for the sphere suspension range: a nonminimal antipodal great circle
has two negative modes for every direction normal to its two-plane.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.OrbitPair.SphereSineModes

theorem integral_cos_nat_pi (n : ℕ) (hn : n ≠ 0) :
    (∫ t : ℝ in 0..1, Real.cos ((n : ℝ) * Real.pi * t)) = 0 := by
  have h : (n : ℝ) * Real.pi ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.mpr hn) Real.pi_ne_zero
  rw [intervalIntegral.integral_comp_mul_left Real.cos h]
  simp only [mul_zero, mul_one, integral_cos, Real.sin_nat_mul_pi, Real.sin_zero,
    sub_zero, smul_zero]

theorem integral_sin_nat_pi_sq (n : ℕ) (hn : n ≠ 0) :
    (∫ t : ℝ in 0..1, Real.sin ((n : ℝ) * Real.pi * t) ^ 2) = 1 / 2 := by
  have h : (n : ℝ) * Real.pi ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.mpr hn) Real.pi_ne_zero
  rw [intervalIntegral.integral_comp_mul_left (fun t : ℝ => Real.sin t ^ 2) h]
  simp only [mul_zero, mul_one, integral_sin_sq, Real.sin_nat_mul_pi, Real.sin_zero,
    Real.cos_zero, zero_mul, sub_zero, zero_add, smul_eq_mul]
  field_simp

theorem integral_cos_nat_pi_sq (n : ℕ) (hn : n ≠ 0) :
    (∫ t : ℝ in 0..1, Real.cos ((n : ℝ) * Real.pi * t) ^ 2) = 1 / 2 := by
  have h : (n : ℝ) * Real.pi ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.mpr hn) Real.pi_ne_zero
  rw [intervalIntegral.integral_comp_mul_left (fun t : ℝ => Real.cos t ^ 2) h]
  simp only [mul_zero, mul_one, integral_cos_sq, Real.sin_nat_mul_pi, Real.sin_zero,
    Real.cos_zero, mul_zero, sub_zero, zero_add, smul_eq_mul]
  field_simp

theorem sin_cross (t : ℝ) :
    Real.sin (Real.pi * t) * Real.sin (2 * Real.pi * t) =
      (Real.cos (Real.pi * t) - Real.cos (3 * Real.pi * t)) / 2 := by
  have hs := Real.cos_sub (Real.pi * t) (2 * Real.pi * t)
  have ha := Real.cos_add (Real.pi * t) (2 * Real.pi * t)
  rw [show Real.pi * t - 2 * Real.pi * t = -(Real.pi * t) by ring, Real.cos_neg] at hs
  rw [show Real.pi * t + 2 * Real.pi * t = 3 * Real.pi * t by ring] at ha
  linarith

theorem cos_cross (t : ℝ) :
    Real.cos (Real.pi * t) * Real.cos (2 * Real.pi * t) =
      (Real.cos (Real.pi * t) + Real.cos (3 * Real.pi * t)) / 2 := by
  have hs := Real.cos_sub (Real.pi * t) (2 * Real.pi * t)
  have ha := Real.cos_add (Real.pi * t) (2 * Real.pi * t)
  rw [show Real.pi * t - 2 * Real.pi * t = -(Real.pi * t) by ring, Real.cos_neg] at hs
  rw [show Real.pi * t + 2 * Real.pi * t = 3 * Real.pi * t by ring] at ha
  linarith

theorem integral_sin_cross :
    (∫ t : ℝ in 0..1, Real.sin (Real.pi * t) * Real.sin (2 * Real.pi * t)) = 0 := by
  have h₁ : Continuous (fun t : ℝ => Real.cos (Real.pi * t)) := by fun_prop
  have h₃ : Continuous (fun t : ℝ => Real.cos (3 * Real.pi * t)) := by fun_prop
  simp_rw [sin_cross]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    (h₁.intervalIntegrable 0 1) (h₃.intervalIntegrable 0 1)]
  have h := integral_cos_nat_pi 1 (by decide)
  norm_num only [Nat.cast_one, one_mul] at h
  rw [h, show (3 : ℝ) = (3 : ℕ) by norm_num, integral_cos_nat_pi 3 (by decide)]
  norm_num

theorem integral_cos_cross :
    (∫ t : ℝ in 0..1, Real.cos (Real.pi * t) * Real.cos (2 * Real.pi * t)) = 0 := by
  have h₁ : Continuous (fun t : ℝ => Real.cos (Real.pi * t)) := by fun_prop
  have h₃ : Continuous (fun t : ℝ => Real.cos (3 * Real.pi * t)) := by fun_prop
  simp_rw [cos_cross]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    (h₁.intervalIntegrable 0 1) (h₃.intervalIntegrable 0 1)]
  have h := integral_cos_nat_pi 1 (by decide)
  norm_num only [Nat.cast_one, one_mul] at h
  rw [h, show (3 : ℝ) = (3 : ℕ) by norm_num, integral_cos_nat_pi 3 (by decide)]
  norm_num

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem integral_norm_sq_two_modes (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hff : (∫ t : ℝ in 0..1, f t ^ 2) = 1 / 2)
    (hgg : (∫ t : ℝ in 0..1, g t ^ 2) = 1 / 2)
    (hfg : (∫ t : ℝ in 0..1, f t * g t) = 0) (u v : E) :
    (∫ t : ℝ in 0..1, ‖f t • u + g t • v‖ ^ 2) =
      (‖u‖ ^ 2 + ‖v‖ ^ 2) / 2 := by
  have he (t : ℝ) : ‖f t • u + g t • v‖ ^ 2 =
      f t ^ 2 * ‖u‖ ^ 2 + (2 * inner ℝ u v) * (f t * g t) + g t ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      real_inner_smul_left, real_inner_smul_right]
    simp only [mul_pow, sq_abs]
    ring
  have h₁ : Continuous (fun t => f t ^ 2 * ‖u‖ ^ 2) := (hf.pow 2).mul continuous_const
  have h₂ : Continuous (fun t => (2 * inner ℝ u v) * (f t * g t)) :=
    continuous_const.mul (hf.mul hg)
  have h₃ : Continuous (fun t => g t ^ 2 * ‖v‖ ^ 2) := (hg.pow 2).mul continuous_const
  have h₁₂ : Continuous (fun t => f t ^ 2 * ‖u‖ ^ 2 +
      (2 * inner ℝ u v) * (f t * g t)) := h₁.add h₂
  simp_rw [he]
  rw [intervalIntegral.integral_add (h₁₂.intervalIntegrable 0 1)
    (h₃.intervalIntegrable 0 1), intervalIntegral.integral_add
    (h₁.intervalIntegrable 0 1) (h₂.intervalIntegrable 0 1)]
  simp only [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
    hff, hgg, hfg, mul_zero, add_zero]
  ring

def field (u v : E) (t : ℝ) : E :=
  Real.sin (Real.pi * t) • u + Real.sin (2 * Real.pi * t) • v

def velocity (u v : E) (t : ℝ) : E :=
  Real.cos (Real.pi * t) • (Real.pi • u) + Real.cos (2 * Real.pi * t) • ((2 * Real.pi) • v)

theorem contDiff_field (u v : E) : ContDiff ℝ ∞ (field u v) := by
  unfold field
  fun_prop

theorem field_zero (u v : E) : field u v 0 = 0 := by simp [field]

theorem field_one (u v : E) : field u v 1 = 0 := by
  simp [field, Real.sin_two_mul]

theorem hasDerivAt_field (u v : E) (t : ℝ) : HasDerivAt (field u v) (velocity u v t) t := by
  have h₁ : HasDerivAt (fun r : ℝ => Real.pi * r) Real.pi t := by
    simpa only [id_eq, mul_one] using! (hasDerivAt_id t).const_mul Real.pi
  have h₂ : HasDerivAt (fun r : ℝ => 2 * Real.pi * r) (2 * Real.pi) t := by
    simpa only [id_eq, mul_one] using! (hasDerivAt_id t).const_mul (2 * Real.pi)
  simpa only [field, velocity, smul_smul] using!
    (((Real.hasDerivAt_sin _).comp t h₁).smul_const u).add
      (((Real.hasDerivAt_sin _).comp t h₂).smul_const v)

theorem integral_norm_sq_field (u v : E) :
    (∫ t : ℝ in 0..1, ‖field u v t‖ ^ 2) = (‖u‖ ^ 2 + ‖v‖ ^ 2) / 2 := by
  apply integral_norm_sq_two_modes _ _ (by fun_prop) (by fun_prop) _ _ integral_sin_cross u v
  · simpa only [Nat.cast_one, one_mul] using integral_sin_nat_pi_sq 1 (by decide)
  · simpa only [Nat.cast_ofNat] using integral_sin_nat_pi_sq 2 (by decide)

theorem integral_norm_sq_deriv_field (u v : E) :
    (∫ t : ℝ in 0..1, ‖deriv (field u v) t‖ ^ 2) =
      (Real.pi ^ 2 * ‖u‖ ^ 2 + 4 * Real.pi ^ 2 * ‖v‖ ^ 2) / 2 := by
  have h₁ : (∫ t : ℝ in 0..1, Real.cos (Real.pi * t) ^ 2) = 1 / 2 := by
    simpa only [Nat.cast_one, one_mul] using integral_cos_nat_pi_sq 1 (by decide)
  have h₂ : (∫ t : ℝ in 0..1, Real.cos (2 * Real.pi * t) ^ 2) = 1 / 2 := by
    simpa only [Nat.cast_ofNat] using integral_cos_nat_pi_sq 2 (by decide)
  have h := integral_norm_sq_two_modes _ _ (by fun_prop) (by fun_prop)
    h₁ h₂ integral_cos_cross (Real.pi • u) ((2 * Real.pi) • v)
  simp_rw [(hasDerivAt_field u v _).deriv]
  rw [show (∫ t : ℝ in 0..1, ‖velocity u v t‖ ^ 2) =
    (‖Real.pi • u‖ ^ 2 + ‖(2 * Real.pi) • v‖ ^ 2) / 2 from h]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem index_field (u v : E) (w : ℝ) :
    (2 * ∫ t : ℝ in 0..1, (‖deriv (field u v) t‖ ^ 2 - w ^ 2 * ‖field u v t‖ ^ 2)) =
      (Real.pi ^ 2 - w ^ 2) * ‖u‖ ^ 2 + (4 * Real.pi ^ 2 - w ^ 2) * ‖v‖ ^ 2 := by
  have hd := ((contDiff_field u v).deriv' (n := ∞)).continuous
  have hd₂ : Continuous (fun t => ‖deriv (field u v) t‖ ^ 2) := hd.norm.pow 2
  have hs : Continuous (fun t => w ^ 2 * ‖field u v t‖ ^ 2) :=
    continuous_const.mul ((contDiff_field u v).continuous.norm.pow 2)
  rw [intervalIntegral.integral_sub (hd₂.intervalIntegrable 0 1)
    (hs.intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul, integral_norm_sq_deriv_field, integral_norm_sq_field]
  ring

end Wikipedia.HopfProblem.OrbitPair.SphereSineModes
