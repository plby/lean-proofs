import Wikipedia.HopfProblem.SphereHomologySuspensionCoordinates

/-!
# Every point of the next Euclidean sphere is a latitude point

The first coordinate determines the actual suspension parameter. The
remaining coordinates have norm equal to its latitude radius; when that
radius is nonzero they determine a genuine point of the preceding sphere.
At either pole the remaining vector is zero.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HopfProblem.SphereHomology.Latitude

def tail (n : ℕ) (y : UnitSphere (n + 1)) : EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun i => y.val i.succ)

@[simp] theorem tail_apply (n : ℕ) (y : UnitSphere (n + 1)) (i : Fin (n + 1)) :
    tail n y i = y.val i.succ := rfl

theorem head_tail_norm_sq (n : ℕ) (y : UnitSphere (n + 1)) :
    y.val 0 ^ 2 + ‖tail n y‖ ^ 2 = 1 := by
  have h : ‖y.val‖ ^ 2 = 1 := by rw [unitSphere_norm, one_pow]
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ] at h
  rw [EuclideanSpace.real_norm_sq_eq]
  simpa only [tail_apply] using h

theorem head_bounds (n : ℕ) (y : UnitSphere (n + 1)) :
    -1 ≤ y.val 0 ∧ y.val 0 ≤ 1 := by
  have h := head_tail_norm_sq n y
  constructor
  · nlinarith [sq_nonneg ‖tail n y‖, sq_nonneg (y.val 0 + 1)]
  · nlinarith [sq_nonneg ‖tail n y‖, sq_nonneg (y.val 0 - 1)]

/-- The inverse height parameter comes from the original first real coordinate. -/
def parameter (n : ℕ) (y : UnitSphere (n + 1)) : unitInterval :=
  ⟨(y.val 0 + 1) / 2, by
    have h := head_bounds n y
    constructor <;> linarith [h.1, h.2]⟩

@[simp] theorem height_parameter (n : ℕ) (y : UnitSphere (n + 1)) :
    height (parameter n y) = y.val 0 := by
  change 2 * ((y.val 0 + 1) / 2) - 1 = y.val 0
  ring

theorem radius_parameter_eq_norm_tail (n : ℕ) (y : UnitSphere (n + 1)) :
    radius (parameter n y) = ‖tail n y‖ := by
  apply (sq_eq_sq₀ (radius_nonneg _) (norm_nonneg _)).mp
  rw [radius_sq, height_parameter]
  linarith [head_tail_norm_sq n y]

/-- The latitude map covers the original Euclidean sphere, including both poles. -/
theorem point_surjective (n : ℕ) :
    Function.Surjective (fun p : unitInterval × UnitSphere n => point n p.1 p.2) := by
  intro y
  let t := parameter n y
  have hr := radius_parameter_eq_norm_tail n y
  by_cases hzero : radius t = 0
  · have ht : tail n y = 0 := norm_eq_zero.mp (hr.symm.trans hzero)
    refine ⟨(t, basePoint n), ?_⟩
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact height_parameter n y
    · change radius t * (basePoint n).val j = y.val j.succ
      rw [hzero, zero_mul]
      have hj := congrArg (fun v : EuclideanSpace ℝ (Fin (n + 1)) => v j) ht
      change y.val j.succ = 0 at hj
      exact hj.symm
  · let v : EuclideanSpace ℝ (Fin (n + 1)) := (radius t)⁻¹ • tail n y
    have hv : ‖v‖ = 1 := by
      calc
        ‖v‖ = |(radius t)⁻¹| * ‖tail n y‖ := norm_smul _ _
        _ = (radius t)⁻¹ * radius t := by
          rw [abs_inv, abs_of_nonneg (radius_nonneg t), ← hr]
        _ = 1 := inv_mul_cancel₀ hzero
    let x : UnitSphere n := ⟨v, by
      simpa only [Metric.mem_sphere, dist_zero_right] using hv⟩
    refine ⟨(t, x), ?_⟩
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact height_parameter n y
    · change radius t * ((radius t)⁻¹ * tail n y j) = y.val j.succ
      rw [← mul_assoc, mul_inv_cancel₀ hzero, one_mul, tail_apply]

end Wikipedia.HopfProblem.SphereHomology.Latitude
