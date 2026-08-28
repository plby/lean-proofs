import Wikipedia.HopfProblem.OrbitPairSpherePathSecondVariation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Great-circle paths in the original Euclidean sphere

The displayed trigonometric curves, their actual derivatives and their
constant-speed acceleration are proved directly in the ambient inner product
space. The normal variation spaces used later are orthogonal to this same
two-plane.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.OrbitPair.SphereGreatCircle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def curve (x y : E) (w t : ℝ) : E :=
  Real.cos (w * t) • x + Real.sin (w * t) • y

def velocity (x y : E) (w t : ℝ) : E :=
  (-Real.sin (w * t) * w) • x + (Real.cos (w * t) * w) • y

theorem contDiff_curve (x y : E) (w : ℝ) : ContDiff ℝ ∞ (curve x y w) :=
  ((Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)).smul contDiff_const).add
    ((Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).smul contDiff_const)

theorem hasDerivAt_curve (x y : E) (w t : ℝ) :
    HasDerivAt (curve x y w) (velocity x y w t) t := by
  have hw : HasDerivAt (fun r : ℝ => w * r) w t := by
    simpa only [mul_one, id_eq] using (hasDerivAt_id t).const_mul w
  exact ((Real.hasDerivAt_cos (w * t)).comp t hw).smul_const x |>.add
    (((Real.hasDerivAt_sin (w * t)).comp t hw).smul_const y)

theorem hasDerivAt_velocity (x y : E) (w t : ℝ) :
    HasDerivAt (velocity x y w) ((-w ^ 2) • curve x y w t) t := by
  have hw : HasDerivAt (fun r : ℝ => w * r) w t := by
    simpa only [mul_one, id_eq] using (hasDerivAt_id t).const_mul w
  have hd := ((((Real.hasDerivAt_sin (w * t)).comp t hw).neg.mul_const w).smul_const x).add
    ((((Real.hasDerivAt_cos (w * t)).comp t hw).mul_const w).smul_const y)
  convert! hd using 1
  dsimp [curve]
  module

theorem deriv_curve (x y : E) (w t : ℝ) : deriv (curve x y w) t = velocity x y w t :=
  (hasDerivAt_curve x y w t).deriv

theorem deriv_deriv_curve (x y : E) (w t : ℝ) :
    deriv (deriv (curve x y w)) t = (-w ^ 2) • curve x y w t := by
  have he : deriv (curve x y w) = velocity x y w := funext (deriv_curve x y w)
  rw [he, (hasDerivAt_velocity x y w t).deriv]

theorem norm_sq_plane {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : inner ℝ x y = 0) (a b : ℝ) : ‖a • x + b • y‖ ^ 2 = a ^ 2 + b ^ 2 := by
  have hyx : inner ℝ y x = 0 := by rwa [real_inner_comm]
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs,
    hx, hy, hxy, hyx, mul_one, mul_zero, add_zero, zero_add, sq_abs]

theorem norm_curve {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : inner ℝ x y = 0) (w t : ℝ) : ‖curve x y w t‖ = 1 := by
  have hn : ‖curve x y w t‖ ^ 2 = 1 := by
    rw [curve, norm_sq_plane hx hy hxy, Real.cos_sq_add_sin_sq]
  nlinarith [norm_nonneg (curve x y w t)]

theorem speed_sq {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : inner ℝ x y = 0) (w t : ℝ) : ‖velocity x y w t‖ ^ 2 = w ^ 2 := by
  rw [velocity, norm_sq_plane hx hy hxy]
  nlinarith [Real.sin_sq_add_cos_sq (w * t)]

theorem energy_curve {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : inner ℝ x y = 0) (w : ℝ) : SpherePathEnergy.energy (curve x y w) 0 1 = w ^ 2 := by
  unfold SpherePathEnergy.energy
  simp_rw [deriv_curve, speed_sq hx hy hxy]
  simp

theorem curve_zero (x y : E) (w : ℝ) : curve x y w 0 = x := by
  simp [curve]

theorem curve_pi_one (x y : E) : curve x y Real.pi 1 = -x := by
  simp [curve]

theorem inner_curve_eq_zero {x y z : E} (hxz : inner ℝ x z = 0)
    (hyz : inner ℝ y z = 0) (w t : ℝ) : inner ℝ (curve x y w t) z = 0 := by
  simp only [curve, inner_add_left, real_inner_smul_left, hxz, hyz, mul_zero, add_zero]

end Wikipedia.HopfProblem.OrbitPair.SphereGreatCircle
