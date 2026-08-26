import ErdosProblems.Erdos1164.SpatialPotential
import ErdosProblems.Erdos1164.Definitions

/-! # A polynomial-sized family of well-separated targets -/

namespace Erdos1164

open Erdos1165 Erdos1165.PotentialConvergence Erdos1165.PotentialEuclideanGeometry
open Erdos1165.Annulus Erdos1165.RadialHarnackSpecialization

/-- `m` targets in the positive horizontal axis, between radii `m²` and `2m²`. -/
def separatedTarget (m : ℕ) (i : Fin m) : Point :=
  ((m ^ 2 + m * (i : ℕ) : ℕ), 0)

theorem euclideanRadius_axis (a : ℤ) : euclideanRadius (a, 0) = |(a : ℝ)| := by
  simp [euclideanRadius, euclideanRadiusSq, Real.sqrt_sq_eq_abs]

theorem separatedTarget_radius (m : ℕ) (i : Fin m) :
    euclideanRadius (separatedTarget m i) = (m : ℝ) ^ 2 + m * (i : ℕ) := by
  rw [separatedTarget, euclideanRadius_axis, abs_of_nonneg (by positivity)]
  push_cast
  rfl

theorem separatedTarget_radius_bounds (m : ℕ) (i : Fin m) :
    (m : ℝ) ^ 2 ≤ euclideanRadius (separatedTarget m i) ∧
      euclideanRadius (separatedTarget m i) ≤ 2 * (m : ℝ) ^ 2 := by
  rw [separatedTarget_radius]
  have hi : ((i : ℕ) : ℝ) ≤ m := by exact_mod_cast i.isLt.le
  constructor
  · exact le_add_of_nonneg_right (by positivity)
  · nlinarith

theorem separatedTarget_ne_zero {m : ℕ} (hm : 1 ≤ m) (i : Fin m) :
    separatedTarget m i ≠ 0 := by
  apply (euclideanRadius_pos_iff _).mp
  have h := (separatedTarget_radius_bounds m i).1
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  exact (sq_pos_of_pos hmpos).trans_le h

theorem separatedTarget_injective {m : ℕ} (hm : 1 ≤ m) :
    Function.Injective (separatedTarget m) := by
  intro i j hij
  have h := congrArg Prod.fst hij
  simp only [separatedTarget, Nat.cast_add, Nat.cast_pow, Nat.cast_mul] at h
  have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  apply Fin.ext
  exact_mod_cast mul_left_cancel₀ hmz (add_left_cancel h)

theorem separatedTarget_mem_disc (m : ℕ) (i : Fin m) :
    separatedTarget m i ∈ latticeDisc (2 * m ^ 2) := by
  have hr := (separatedTarget_radius_bounds m i).2
  have hc : separatedTarget m i ∈ closedDisc (2 * m ^ 2) :=
    mem_closedDisc_of_euclideanRadius_le (by exact_mod_cast hr)
  simpa only [mem_closedDisc_iff_radiusSqInt_le, radiusSqInt, latticeDisc, Set.mem_ofPred_eq] using hc

theorem separatedTarget_distance_lower {m : ℕ} (hm : 1 ≤ m)
    {i j : Fin m} (hij : i ≠ j) :
    (m : ℝ) ≤ euclideanRadius (separatedTarget m i - separatedTarget m j) := by
  have heq : separatedTarget m i - separatedTarget m j =
      ((m : ℤ) * ((i : ℕ) - (j : ℕ)), 0) := by
    ext <;> simp [separatedTarget] <;> ring
  rw [heq, euclideanRadius_axis, Int.cast_mul, Int.cast_sub, Int.cast_natCast,
    Int.cast_natCast, Int.cast_natCast, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ m)]
  have hidx : (1 : ℝ) ≤ |((i : ℕ) : ℝ) - (j : ℕ)| := by
    rcases lt_or_gt_of_ne hij with h | h
    · have hn : (i : ℕ) + 1 ≤ (j : ℕ) := by exact h
      have hr : ((i : ℕ) : ℝ) + 1 ≤ (j : ℕ) := by exact_mod_cast hn
      have habs := neg_le_abs (((i : ℕ) : ℝ) - (j : ℕ))
      linarith
    · have hn : (j : ℕ) + 1 ≤ (i : ℕ) := by exact h
      have hr : ((j : ℕ) : ℝ) + 1 ≤ (i : ℕ) := by exact_mod_cast hn
      have habs := le_abs_self (((i : ℕ) : ℝ) - (j : ℕ))
      linarith
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hidx (Nat.cast_nonneg m : (0 : ℝ) ≤ m)

theorem separatedTarget_inner_quarter {m : ℕ} (hm : 4 ≤ m) (i : Fin m) :
    euclideanRadius (separatedTarget m i) ≤ ((m ^ 8 : ℕ) : ℝ) / 4 := by
  have hm6 : 8 ≤ m ^ 6 := (by norm_num : 8 ≤ 4 ^ 6).trans (Nat.pow_le_pow_left hm 6)
  have hpow : 8 * m ^ 2 ≤ m ^ 8 := by
    calc
      8 * m ^ 2 ≤ m ^ 6 * m ^ 2 := Nat.mul_le_mul_right _ hm6
      _ = _ := by ring
  have hcast : (8 : ℝ) * (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 8 := by exact_mod_cast hpow
  have hrad := (separatedTarget_radius_bounds m i).2
  push_cast
  linarith

/-- All target potentials are within a constant of twice the logarithmic scale. -/
theorem separatedTarget_potential {m : ℕ} (hm : 4 ≤ m) (i : Fin m) :
    2 * (potentialSlope * Real.log (m : ℝ)) - potentialError ≤
        planarPotentialKernel (separatedTarget m i) ∧
      planarPotentialKernel (separatedTarget m i) ≤
        2 * (potentialSlope * Real.log (m : ℝ)) + potentialError := by
  have hmreal : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hr := separatedTarget_radius_bounds m i
  have hrad : 4 ≤ euclideanRadius (separatedTarget m i) := by nlinarith
  have he := abs_le.mp (potential_log_error hrad)
  have hlo := Real.log_le_log (pow_pos hmpos 2) hr.1
  have hup := Real.log_le_log (by linarith : 0 < euclideanRadius (separatedTarget m i)) hr.2
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero 2 hmpos.ne'), Real.log_pow] at hup
  rw [Real.log_pow] at hlo
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hs := potentialSlope_pos.le
  have hlog2nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hsmall := (mul_le_mul_of_nonneg_right potentialSlope_le_one hlog2nonneg).trans
    (by simpa using hlog2 : 1 * Real.log 2 ≤ 1)
  have hlom := mul_le_mul_of_nonneg_left hlo hs
  have hupm := mul_le_mul_of_nonneg_left hup hs
  norm_num only [Nat.cast_ofNat] at hlom hupm
  constructor <;> nlinarith

/-- The potential between any two distinct selected points grows at least
linearly in `log m`. -/
theorem separatedTarget_difference_potential {m : ℕ} (hm : 4 ≤ m)
    {i j : Fin m} (hij : i ≠ j) :
    potentialSlope * Real.log (m : ℝ) - potentialError ≤
      planarPotentialKernel (separatedTarget m i - separatedTarget m j) := by
  have hmreal : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hd := separatedTarget_distance_lower (by omega : 1 ≤ m) hij
  have he := (abs_le.mp (potential_log_error (hmreal.trans hd))).1
  have hlog := Real.log_le_log (by linarith : (0 : ℝ) < m) hd
  have hmul := mul_le_mul_of_nonneg_left hlog potentialSlope_pos.le
  linarith

end Erdos1164
