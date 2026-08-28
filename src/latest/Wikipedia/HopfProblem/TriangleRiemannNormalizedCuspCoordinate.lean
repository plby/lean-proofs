import Wikipedia.HopfProblem.TriangleRiemannIdealLimits
import Wikipedia.HopfProblem.SpecialPeriodsTriangleCusp

/-!
# Matching the triangle's cusp parameters

The exponential parameter used by the analytic ideal germ differs from
the original periodic cusp coordinate by a fixed unit complex factor.
The identities below apply to the actual coordinates, with no choice of
representative or limiting path.
-/

noncomputable section

open Complex Function Metric Set

namespace Wikipedia.HopfProblem.RiemannMapping

open SpecialPeriods.Triangle RiemannBoundary

/-- The fixed rotation from the original periodic cusp coordinate to the
half-strip coordinate used by the ideal boundary germ. -/
def triangleCuspPhase : ℂ :=
  Complex.exp (-Complex.I * (stripLeft : ℂ) / (triangleCuspScale : ℂ))

theorem triangleCuspPhase_ne_zero : triangleCuspPhase ≠ 0 :=
  Complex.exp_ne_zero _

@[simp] theorem norm_triangleCuspPhase : ‖triangleCuspPhase‖ = 1 := by
  simp [triangleCuspPhase, Complex.norm_exp]

/-- The logarithmic ideal germ and the original periodic parameter use
the same cusp coordinate, up to the explicit fixed unit factor. -/
theorem triangleCuspExp_eq_phase_mul_qParam (z : ℂ) :
    triangleCuspExp z = triangleCuspPhase * Periodic.qParam width z := by
  unfold triangleCuspExp halfStripExp triangleCuspPhase Periodic.qParam
  rw [← Complex.exp_add]
  congr 1
  have hc : (triangleCuspScale : ℂ) = (width : ℂ) / (2 * Real.pi) := by
    simp [triangleCuspScale]
  rw [hc]
  field_simp [Complex.ofReal_ne_zero.mpr width_ne_zero,
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring

/-- The same exact relation expressed with the original upper-half-plane
cusp coordinate. -/
theorem triangleCuspExp_eq_phase_mul_cuspQ (z : UpperHalfPlane) :
    triangleCuspExp (z : ℂ) = triangleCuspPhase * cuspQ z :=
  triangleCuspExp_eq_phase_mul_qParam z

theorem norm_triangleCuspExp_eq_norm_qParam (z : ℂ) :
    ‖triangleCuspExp z‖ = ‖Periodic.qParam width z‖ := by
  rw [triangleCuspExp_eq_phase_mul_qParam, norm_mul, norm_triangleCuspPhase, one_mul]

theorem norm_triangleCuspExp_eq_norm_cuspQ (z : UpperHalfPlane) :
    ‖triangleCuspExp (z : ℂ)‖ = ‖cuspQ z‖ :=
  norm_triangleCuspExp_eq_norm_qParam z

/-- A positive cusp disk contains the parameter of every sufficiently
high point. This estimate is uniform in the real coordinate. -/
theorem exists_triangleCuspExp_mem_ball_of_height {r : ℝ} (hr : 0 < r) :
    ∃ Y : ℝ, ∀ z : ℂ, Y < z.im → triangleCuspExp z ∈ ball (0 : ℂ) r := by
  refine ⟨-triangleCuspScale * Real.log r, fun z hz => ?_⟩
  rw [mem_ball, dist_zero_right, norm_triangleCuspExp, ← Real.exp_log hr,
    Real.exp_lt_exp]
  apply (div_lt_iff₀ triangleCuspScale_pos).mpr
  nlinarith

end Wikipedia.HopfProblem.RiemannMapping
