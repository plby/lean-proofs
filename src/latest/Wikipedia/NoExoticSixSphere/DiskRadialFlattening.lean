import Wikipedia.NoExoticSixSphere.SmoothSphereAmbientExtension
import Wikipedia.NoExoticSixSphere.GLOrthonormalization
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# A smooth positive radial flattening into the closed unit disk

The map is the identity near zero and radial normalization near the unit
sphere. Its positive scalar factor is smooth everywhere, and its image stays
in the closed ball. Adding the normal height will recover the radial
direction lost near the boundary.
-/

noncomputable section

open Filter Metric Topology
open scoped ContDiff

namespace NoExoticSixSphere.DiskRadialFlattening

open GLOrthonormalization SmoothSphereAmbient

def scalar (n : ℕ) (x : Vector (n + 1)) : ℝ :=
  cutoff n x + (1 - cutoff n x) * ‖x‖⁻¹

def map (n : ℕ) (x : Vector (n + 1)) : Vector (n + 1) := scalar n x • x

theorem scalar_zero (n : ℕ) : scalar n 0 = 1 := by
  have hχ : cutoff n 0 = 1 := (cutoff n).one_of_mem_closedBall (by simp [cutoff])
  simp only [scalar, hχ, sub_self, zero_mul, add_zero]

theorem contDiff_scalar (n : ℕ) : ContDiff ℝ ∞ (scalar n) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have he : scalar n =ᶠ[𝓝 0] (fun _ ↦ (1 : ℝ)) := by
      filter_upwards [(cutoff n).eventuallyEq_one] with y hy
      simp only [scalar, hy, Pi.one_apply, sub_self, zero_mul, add_zero]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact (cutoff n).contDiff.contDiffAt.add
      ((contDiffAt_const.sub (cutoff n).contDiff.contDiffAt).mul
        ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)))

theorem scalar_pos (n : ℕ) (x : Vector (n + 1)) : 0 < scalar n x := by
  by_cases hx : x = 0
  · subst x
    rw [scalar_zero]
    exact zero_lt_one
  · by_cases hχ : cutoff n x = 0
    · simpa only [scalar, hχ, sub_zero, one_mul, zero_add] using
        inv_pos.mpr (norm_pos_iff.mpr hx)
    · have hp : 0 < cutoff n x := lt_of_le_of_ne (cutoff n).nonneg (Ne.symm hχ)
      exact add_pos_of_pos_of_nonneg hp
        (mul_nonneg (sub_nonneg.mpr (cutoff n).le_one) (inv_nonneg.mpr (norm_nonneg x)))

theorem contDiff_map (n : ℕ) : ContDiff ℝ ∞ (map n) :=
  (contDiff_scalar n).smul contDiff_id

theorem norm_map (n : ℕ) (x : Vector (n + 1)) : ‖map n x‖ = scalar n x * ‖x‖ := by
  rw [map, norm_smul, Real.norm_eq_abs, abs_of_pos (scalar_pos n x)]

theorem map_eq_normalize (n : ℕ) {x : Vector (n + 1)} (hx : 1 / 2 ≤ ‖x‖) :
    map n x = NormedSpace.normalize x := by
  have hχ : cutoff n x = 0 := (cutoff n).zero_of_le_dist
    (by simpa only [cutoff, dist_zero_right] using hx)
  simp only [map, scalar, hχ, sub_zero, one_mul, zero_add, NormedSpace.normalize]

theorem norm_map_le_one (n : ℕ) (x : Vector (n + 1)) : ‖map n x‖ ≤ 1 := by
  by_cases hx : x = 0
  · subst x
    simp only [map, smul_zero, norm_zero, zero_le_one]
  · by_cases hn : ‖x‖ ≤ 1
    · have he : scalar n x * ‖x‖ = cutoff n x * ‖x‖ + (1 - cutoff n x) := by
        rw [scalar, add_mul, mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx), mul_one]
      rw [norm_map, he]
      have hχ : 0 ≤ cutoff n x := (cutoff n).nonneg
      nlinarith
    · rw [map_eq_normalize n (by linarith), NormedSpace.norm_normalize hx]

theorem map_mem_closedBall (n : ℕ) (x : Vector (n + 1)) : map n x ∈ closedBall 0 1 := by
  simpa only [mem_closedBall, dist_zero_right] using norm_map_le_one n x

theorem map_coe (n : ℕ) (s : Sphere n) : map n s.val = s.val := by
  rw [map_eq_normalize n (by rw [ClosedHemisphere.unit_norm]; norm_num)]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm s)

end NoExoticSixSphere.DiskRadialFlattening
