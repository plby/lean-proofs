import Wikipedia.SmoothSixDPoincare.Hemisphere

/-!
# The two disk parametrizations cover the sphere
-/

noncomputable section

open Set Metric

namespace Wikipedia.SmoothSixDPoincare.Hemisphere

variable {n : ℕ}

/-- Drop the first coordinate of a point on the standard sphere. -/
def tail (y : Sphere n) : Ambient n :=
  WithLp.toLp 2 (fun i => (y : Ambient (n + 1)) i.succ)

@[simp] theorem tail_apply (y : Sphere n) (i : Fin n) :
    tail y i = (y : Ambient (n + 1)) i.succ := rfl

theorem head_sq_add_tail_norm_sq (y : Sphere n) :
    (y : Ambient (n + 1)) 0 ^ 2 + ‖tail y‖ ^ 2 = 1 := by
  have hy : ‖(y : Ambient (n + 1))‖ ^ 2 = 1 := by
    rw [mem_sphere_zero_iff_norm.mp y.property]
    exact one_pow 2
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ] at hy
  rw [EuclideanSpace.real_norm_sq_eq]
  exact hy

theorem tail_mem_ball (y : Sphere n) : tail y ∈ closedBall (0 : Ambient n) 1 := by
  rw [mem_closedBall_zero_iff]
  have hy := head_sq_add_tail_norm_sq y
  nlinarith [sq_nonneg ((y : Ambient (n + 1)) 0), norm_nonneg (tail y)]

def disk (y : Sphere n) : Ball n := ⟨tail y, tail_mem_ball y⟩

theorem radius_disk (y : Sphere n) : radius (disk y) = |(y : Ambient (n + 1)) 0| := by
  have hy := head_sq_add_tail_norm_sq y
  have hs : 1 - ‖tail y‖ ^ 2 = (y : Ambient (n + 1)) 0 ^ 2 := by linarith
  change Real.sqrt (1 - ‖tail y‖ ^ 2) = _
  rw [hs, Real.sqrt_sq_eq_abs]

theorem point_disk_of_nonneg (y : Sphere n) (hy : 0 ≤ (y : Ambient (n + 1)) 0) :
    point true (disk y) = y := by
  apply Subtype.ext
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [radius_disk, abs_of_nonneg hy]
  · rfl

theorem point_disk_of_nonpos (y : Sphere n) (hy : (y : Ambient (n + 1)) 0 ≤ 0) :
    point false (disk y) = y := by
  apply Subtype.ext
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [radius_disk, abs_of_nonpos hy]
  · rfl

/-- The two hemispheres jointly cover the genuine standard sphere. -/
theorem point_jointly_surjective (y : Sphere n) : ∃ b x, point b x = y := by
  rcases le_total 0 ((y : Ambient (n + 1)) 0) with hy | hy
  · exact ⟨true, disk y, point_disk_of_nonneg y hy⟩
  · exact ⟨false, disk y, point_disk_of_nonpos y hy⟩

end Wikipedia.SmoothSixDPoincare.Hemisphere
