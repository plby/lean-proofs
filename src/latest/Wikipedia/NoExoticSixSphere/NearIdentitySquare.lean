import Wikipedia.NoExoticSixSphere.LocalInverse
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith

/-!
# Uniqueness and commutation of square roots near the identity

These are norm estimates in the original real Banach algebra. They do not
require a continuous choice of eigenvectors or a spectral decomposition.
-/

namespace NoExoticSixSphere.NearIdentitySquare

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

theorem eq_zero_of_sylvester_eq_zero (a b x : A)
    (hsmall : ‖a - 1‖ + ‖b - 1‖ < 2) (h : a * x + x * b = 0) : x = 0 := by
  have he : (a - 1) * x + x * (b - 1) = -(x + x) := by
    calc
      _ = (a * x + x * b) - (x + x) := by noncomm_ring
      _ = -(x + x) := by rw [h, zero_sub]
  have hn : 2 * ‖x‖ ≤ (‖a - 1‖ + ‖b - 1‖) * ‖x‖ := by
    calc
      2 * ‖x‖ = ‖x + x‖ := by rw [← two_smul ℝ x, norm_smul]; norm_num
      _ = ‖(a - 1) * x + x * (b - 1)‖ := by rw [he, norm_neg]
      _ ≤ ‖(a - 1) * x‖ + ‖x * (b - 1)‖ := norm_add_le _ _
      _ ≤ ‖a - 1‖ * ‖x‖ + ‖x‖ * ‖b - 1‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = (‖a - 1‖ + ‖b - 1‖) * ‖x‖ := by ring
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg x]

theorem square_injective_near_one {a b : A} (ha : ‖a - 1‖ < 1) (hb : ‖b - 1‖ < 1)
    (h : a * a = b * b) : a = b := by
  apply sub_eq_zero.mp
  apply eq_zero_of_sylvester_eq_zero a b (a - b) (by linarith)
  calc
    _ = a * a - b * b := by noncomm_ring
    _ = 0 := sub_eq_zero.mpr h

theorem commute_of_square_commute {s a : A} (hs : ‖s - 1‖ < 1)
    (h : Commute (s * s) a) : Commute s a := by
  change s * a = a * s
  apply sub_eq_zero.mp
  apply eq_zero_of_sylvester_eq_zero s s (s * a - a * s) (by linarith)
  calc
    _ = (s * s) * a - a * (s * s) := by noncomm_ring
    _ = 0 := sub_eq_zero.mpr h.eq

theorem selfAdjoint_of_square [StarRing A] [NormedStarGroup A] {s : A}
    (hs : ‖s - 1‖ < 1) (h : IsSelfAdjoint (s * s)) : IsSelfAdjoint s := by
  have hstar : ‖star s - 1‖ < 1 := by
    have he : star (s - 1) = star s - 1 := by simp
    rw [← he, norm_star]
    exact hs
  exact square_injective_near_one hstar hs (by rw [← star_mul, h.star_eq])

end NoExoticSixSphere.NearIdentitySquare
