import Wikipedia.HopfProblem.OrbitPairSphereGreatCircle
import Wikipedia.HopfProblem.OrbitPairSphereAngleLogarithm
import Wikipedia.NoExoticSixSphere.SphereNormalization

/-!
# Recovering a semicircle direction from an interior point

Orthogonal projection onto the tangent hyperplane followed by normalization
recovers the unit direction of an antipodal semicircle at every interior time.
The construction is continuous on its explicit open domain. No choice of a
geodesic at an antipodal pair is used.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.OrbitPair.SphereSemicircle

open NoExoticSixSphere GLOrthonormalization

variable {n : ℕ}

abbrev Direction (a : Sphere n) :=
  {y : Vector (n + 1) // ‖y‖ = 1 ∧ inner ℝ a.val y = 0}

def tangentComponent (a : Sphere n) (z : Vector (n + 1)) : Vector (n + 1) :=
  z - inner ℝ a.val z • a.val

theorem continuous_tangentComponent (a : Sphere n) : Continuous (tangentComponent a) := by
  have hc : Continuous (fun z : Vector (n + 1) => inner ℝ a.val z) :=
    continuous_const.inner continuous_id
  exact continuous_id.sub (hc.smul continuous_const)

theorem inner_tangentComponent (a : Sphere n) (z : Vector (n + 1)) :
    inner ℝ a.val (tangentComponent a z) = 0 := by
  simp [tangentComponent, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, ClosedHemisphere.unit_norm]

def directionDomain (a : Sphere n) : Set (Vector (n + 1)) :=
  {z | tangentComponent a z ≠ 0}

theorem isOpen_directionDomain (a : Sphere n) : IsOpen (directionDomain a) :=
  isOpen_ne_fun (continuous_tangentComponent a) continuous_const

def directionRetraction (a : Sphere n) : C(directionDomain a, Direction a) where
  toFun z := ⟨NormedSpace.normalize (tangentComponent a z.1),
    NormedSpace.norm_normalize z.2, by
      simp only [NormedSpace.normalize, real_inner_smul_right,
        inner_tangentComponent, mul_zero]⟩
  continuous_toFun := by
    have hc : Continuous (fun z : directionDomain a => tangentComponent a z.val) :=
      (continuous_tangentComponent a).comp continuous_subtype_val
    exact ((hc.norm.inv₀ (fun z => norm_ne_zero_iff.mpr z.2)).smul hc).subtype_mk _

theorem tangentComponent_curve (a : Sphere n) (y : Direction a) (t : ℝ) :
    tangentComponent a (SphereGreatCircle.curve a.val y.val Real.pi t) =
      Real.sin (Real.pi * t) • y.val := by
  have hinner : inner ℝ a.val (SphereGreatCircle.curve a.val y.val Real.pi t) =
      Real.cos (Real.pi * t) := by
    simp [SphereGreatCircle.curve, inner_add_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, ClosedHemisphere.unit_norm, y.2.2]
  rw [tangentComponent, hinner, SphereGreatCircle.curve]
  module

theorem sin_pi_mul_pos {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < Real.sin (Real.pi * t) :=
  Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ht.1)
    (by simpa only [mul_one] using mul_lt_mul_of_pos_left ht.2 Real.pi_pos)

theorem curve_mem_directionDomain (a : Sphere n) (y : Direction a)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    SphereGreatCircle.curve a.val y.val Real.pi t ∈ directionDomain a := by
  change tangentComponent a _ ≠ 0
  rw [tangentComponent_curve]
  exact smul_ne_zero (ne_of_gt (sin_pi_mul_pos ht))
    (by intro he; have h := y.2.1; rw [he, norm_zero] at h; norm_num at h)

theorem directionRetraction_curve (a : Sphere n) (y : Direction a)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    directionRetraction a ⟨SphereGreatCircle.curve a.val y.val Real.pi t,
      curve_mem_directionDomain a y ht⟩ = y := by
  apply Subtype.ext
  change NormedSpace.normalize (tangentComponent a _) = y.val
  rw [tangentComponent_curve, NormedSpace.normalize_smul_of_pos (sin_pi_mul_pos ht)]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one y.2.1

end Wikipedia.HopfProblem.OrbitPair.SphereSemicircle
