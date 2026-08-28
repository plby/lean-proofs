import Wikipedia.NoExoticSixSphere.SphereCylinderCoordinates

/-!
# Smooth cylinder coordinates and the actual latitude parameters

The cylinder coordinate `s` has latitude height `s / sqrt (s² + 1)`.
Its angular parameter has positive derivative `π / 2` at the equator.
These are equalities of the original normalized vectors, so they can be
used with maps defined by descent through latitude quotients.
-/

noncomputable section

open scoped unitInterval ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.CylinderLatitude

open Wikipedia.HopfProblem.SphereHomology
open NoExoticSixSphere

def height (s : ℝ) : ℝ := s / Real.sqrt (s ^ 2 + 1)

theorem sqrt_pos (s : ℝ) : 0 < Real.sqrt (s ^ 2 + 1) :=
  Real.sqrt_pos.mpr (by positivity)

theorem abs_height_lt_one (s : ℝ) : |height s| < 1 := by
  have hs := Real.sq_sqrt (show 0 ≤ s ^ 2 + 1 by positivity)
  have ha : |s| < Real.sqrt (s ^ 2 + 1) := by
    nlinarith [sq_abs s, abs_nonneg s, sqrt_pos s]
  rw [height, abs_div, abs_of_pos (sqrt_pos s)]
  exact (div_lt_one (sqrt_pos s)).mpr ha

def time (s : ℝ) : I :=
  ⟨(1 + height s) / 2, by
    have h := abs_lt.mp (abs_height_lt_one s)
    constructor <;> linarith⟩

theorem time_interior (s : ℝ) : 0 < (time s : ℝ) ∧ (time s : ℝ) < 1 := by
  have h := abs_lt.mp (abs_height_lt_one s)
  change 0 < (1 + height s) / 2 ∧ (1 + height s) / 2 < 1
  constructor <;> linarith

@[simp] theorem latitude_height_time (s : ℝ) : Latitude.height (time s) = height s := by
  dsimp [Latitude.height, time]
  ring

theorem latitude_radius_time (s : ℝ) :
    Latitude.radius (time s) = (Real.sqrt (s ^ 2 + 1))⁻¹ := by
  have hs := Real.sq_sqrt (show 0 ≤ s ^ 2 + 1 by positivity)
  have hn := ne_of_gt (sqrt_pos s)
  have he : Latitude.radius (time s) ^ 2 = ((Real.sqrt (s ^ 2 + 1))⁻¹) ^ 2 := by
    rw [Latitude.radius_sq, latitude_height_time, height]
    field_simp
    nlinarith
  nlinarith [Latitude.radius_nonneg (time s), inv_pos.mpr (sqrt_pos s)]

theorem vector_norm (n : ℕ) (s : ℝ) (x : UnitSphere n) :
    ‖SphereCylinder.vector n (s, x)‖ = Real.sqrt (s ^ 2 + 1) := by
  have hs := SphereCylinder.norm_join_sq n s x.val
  rw [unitSphere_norm, one_pow] at hs
  change ‖SphereCylinder.vector n (s, x)‖ ^ 2 = s ^ 2 + 1 at hs
  nlinarith [norm_nonneg (SphereCylinder.vector n (s, x)), sqrt_pos s,
    Real.sq_sqrt (show 0 ≤ s ^ 2 + 1 by positivity)]

theorem point_eq_latitude (n : ℕ) (s : ℝ) (x : UnitSphere n) :
    SphereCylinder.point n (s, x) = Latitude.point n (time s) x := by
  apply Subtype.ext
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rw [SphereCylinder.point_head]
    change ‖SphereCylinder.vector n (s, x)‖⁻¹ * s = Latitude.height (time s)
    rw [vector_norm, latitude_height_time, height, div_eq_mul_inv, mul_comm]
  · change ‖SphereCylinder.vector n (s, x)‖⁻¹ * x.val j =
      Latitude.radius (time s) * x.val j
    rw [vector_norm, latitude_radius_time]

@[simp] theorem height_zero : height 0 = 0 := by norm_num [height]

@[simp] theorem time_zero : (time 0 : ℝ) = 1 / 2 := by simp [time]

theorem contDiff_height {n : ℕ∞ω} : ContDiff ℝ n height :=
  contDiff_id.div (((contDiff_id.pow 2).add contDiff_const).sqrt
    (fun s ↦ by positivity)) (fun s ↦ ne_of_gt (sqrt_pos s))

theorem hasDerivAt_height_zero : HasDerivAt height 1 0 := by
  have hd := (((hasDerivAt_id (0 : ℝ)).pow 2).add_const 1).sqrt (by norm_num)
  have h := (hasDerivAt_id (0 : ℝ)).div hd (by norm_num)
  convert h using 1 <;> try rfl
  norm_num

def angleOffset (s : ℝ) : ℝ := (Real.pi / 2) * height s

theorem time_angle (s : ℝ) : (time s : ℝ) * Real.pi = Real.pi / 2 + angleOffset s := by
  dsimp [time, angleOffset]
  ring

@[simp] theorem angleOffset_zero : angleOffset 0 = 0 := by simp [angleOffset]

theorem contDiff_angleOffset {n : ℕ∞ω} : ContDiff ℝ n angleOffset :=
  contDiff_const.mul contDiff_height

theorem hasDerivAt_angleOffset_zero : HasDerivAt angleOffset (Real.pi / 2) 0 := by
  convert hasDerivAt_height_zero.const_mul (Real.pi / 2) using 1 <;> try rfl
  simp

theorem angleOffset_derivative_pos : 0 < Real.pi / 2 := by positivity

end Wikipedia.HomotopyGroupsOfSpheres.CylinderLatitude
