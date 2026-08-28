import Wikipedia.NoExoticSixSphere.RegularSlabAnnulusCollars

/-!
# The actual annulus clock detects the missing radial direction

Differentiate the original polynomial clock, rather than replacing it
with a linear height. At each of the two original boundary radii, its
derivative is a nonzero multiple of the sphere defining-function
derivative. Their kernels therefore agree exactly.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereAnnulus

open GLOrthonormalization
open Wikipedia.SmoothSixDPoincare.SphereBoundary

def squaredRadiusClock (u : ℝ) : ℝ := (4 / 9) * (u - 1) * (4 - u)

theorem ambientClock_eq_squaredRadiusClock {p : ℕ} (x : Vector (p + 1)) :
    ambientClock x = squaredRadiusClock (‖x‖ ^ 2) := by
  unfold ambientClock ambientTime squaredRadiusClock
  ring

theorem hasDerivAt_squaredRadiusClock (u : ℝ) :
    HasDerivAt squaredRadiusClock ((20 - 8 * u) / 9) u := by
  have h : HasDerivAt squaredRadiusClock
      ((4 / 9) * 1 * (4 - u) + (4 / 9) * (u - 1) * (0 - 1)) u :=
    (((hasDerivAt_id u).sub_const (1 : ℝ)).const_mul (4 / 9 : ℝ)).mul
      ((hasDerivAt_const u (4 : ℝ)).sub (hasDerivAt_id u))
  have he : (4 / 9 : ℝ) * 1 * (4 - u) + (4 / 9) * (u - 1) * (0 - 1) =
      (20 - 8 * u) / 9 := by ring
  rwa [he] at h

theorem fderiv_ambientClock {p : ℕ} (x : Vector (p + 1)) :
    fderiv ℝ ambientClock x = ((20 - 8 * ‖x‖ ^ 2) / 9) •
      fderiv ℝ (definingFunction (E := Vector (p + 1))) x := by
  have hn : HasFDerivAt (fun y : Vector (p + 1) ↦ ‖y‖ ^ 2)
      (fderiv ℝ (definingFunction (E := Vector (p + 1))) x) x := by
    rw [fderiv_definingFunction]
    exact (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hc := (hasDerivAt_squaredRadiusClock (‖x‖ ^ 2)).comp_hasFDerivAt x hn
  have he : (ambientClock : Vector (p + 1) → ℝ) =
      squaredRadiusClock ∘ (fun y ↦ ‖y‖ ^ 2) := funext ambientClock_eq_squaredRadiusClock
  rw [he]
  exact hc.fderiv

theorem fderiv_ambientClock_zero_iff {p : ℕ} (x v : Vector (p + 1))
    (hx : ‖x‖ = 1 ∨ ‖x‖ = 2) :
    fderiv ℝ ambientClock x v = 0 ↔
      fderiv ℝ (definingFunction (E := Vector (p + 1))) x v = 0 := by
  rw [fderiv_ambientClock]
  change ((20 - 8 * ‖x‖ ^ 2) / 9) *
    fderiv ℝ (definingFunction (E := Vector (p + 1))) x v = 0 ↔ _
  have hn : (20 - 8 * ‖x‖ ^ 2) / 9 ≠ 0 := by
    rcases hx with hx | hx <;> rw [hx] <;> norm_num
  rw [mul_eq_zero]
  exact or_iff_right hn

end NoExoticSixSphere.SphereAnnulus
