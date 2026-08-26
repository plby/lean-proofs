import ErdosProblems.Erdos421.WeightedBoundedCounts
import ErdosProblems.Erdos421.GapWeights

/-! # A sublinear rejected mass with a cutoff above the one-tenth power -/

namespace Erdos421

theorem scale_log_le_pow {u : ℕ} (hu : 12 ≤ u) : 180 * u ≤ 2 ^ u := by
  induction u, hu using Nat.le_induction with
  | base => norm_num
  | succ u hu ih =>
    calc
      180 * (u + 1) ≤ 2 * (180 * u) := by omega
      _ ≤ 2 * 2 ^ u := Nat.mul_le_mul_left _ ih
      _ = 2 ^ (u + 1) := by rw [pow_succ]; ring

theorem scale_parent_factor_le_pow {u : ℕ} (hu : 12 ≤ u) :
    5 + 720 * u ≤ 2 ^ (2 * u) := by
  induction u, hu using Nat.le_induction with
  | base => norm_num
  | succ u hu ih =>
    calc
      5 + 720 * (u + 1) ≤ 4 * (5 + 720 * u) := by omega
      _ ≤ 4 * 2 ^ (2 * u) := Nat.mul_le_mul_left _ ih
      _ = 2 ^ (2 * (u + 1)) := by
        rw [Nat.mul_add, Nat.mul_one, pow_add]
        ring

theorem boundedUnequalParents_card_scale {u : ℕ} (hu : 12 ≤ u) :
    (boundedUnequalParents (2 ^ (180 * u)) (2 ^ (19 * u))).card ≤ 2 ^ (92 * u) := by
  have hH : 2 * 2 ^ (19 * u) ≤ 2 ^ (90 * u) := by
    calc
      _ = 2 ^ (19 * u + 1) := by rw [pow_succ]; ring
      _ ≤ 2 ^ (90 * u) := Nat.pow_le_pow_right (by decide) (by omega)
  have heq : 2 * (90 * u) = 180 * u := by omega
  have h := unequal_parent_card_bound_square_scale
    (boundedUnequalParents (2 ^ (180 * u)) (2 ^ (19 * u))) (90 * u) (2 ^ (19 * u)) hH
    (fun i hi ↦ by simpa only [heq] using (mem_boundedUnequalParents.mp hi).1)
    (fun i hi ↦ by simpa only [heq] using (mem_boundedUnequalParents.mp hi).2)
  have hfactor : 5 + 8 * (90 * u) ≤ 2 ^ (2 * u) := by
    convert scale_parent_factor_le_pow hu using 1
    omega
  calc
    _ ≤ (5 + 8 * (90 * u)) * 2 ^ (90 * u) := h
    _ ≤ 2 ^ (2 * u) * 2 ^ (90 * u) := Nat.mul_le_mul_right _ hfactor
    _ = 2 ^ (92 * u) := by rw [← pow_add]; congr 1; omega

theorem bounded_solution_factor_scale {u : ℕ} (hu : 12 ≤ u) :
    3 * (2 ^ (60 * u)) ^ 2 + 1 + 2 * ((180 * u) * 2 ^ (19 * u)) ^ 2 ≤
      6 * 2 ^ (120 * u) := by
  have hL : (180 * u) * 2 ^ (19 * u) ≤ 2 ^ (20 * u) := by
    calc
      _ ≤ 2 ^ u * 2 ^ (19 * u) := Nat.mul_le_mul_right _ (scale_log_le_pow hu)
      _ = 2 ^ (20 * u) := by rw [← pow_add]; congr 1; omega
  have hL2 : ((180 * u) * 2 ^ (19 * u)) ^ 2 ≤ 2 ^ (120 * u) := by
    calc
      _ ≤ (2 ^ (20 * u)) ^ 2 := Nat.pow_le_pow_left hL 2
      _ = 2 ^ (40 * u) := by rw [← pow_mul]; congr 1; omega
      _ ≤ 2 ^ (120 * u) := Nat.pow_le_pow_right (by decide) (by omega)
  have hT2 : (2 ^ (60 * u)) ^ 2 = 2 ^ (120 * u) := by
    rw [← pow_mul]; congr 1; omega
  have hpos : 0 < 2 ^ (120 * u) := by positivity
  rw [hT2]
  omega

/-- With `X = 2^(180u)`, all rejected gaps of length at most `X^(19/180)`
have total length at most `7 X^(179/180)`, for `u ≥ 12`. -/
theorem boundedRejections_mass_scale {u : ℕ} (hu : 12 ≤ u) :
    (∑ k ∈ boundedRejections (2 ^ (180 * u)) (2 ^ (19 * u)), gapLength k) ≤
      7 * 2 ^ (179 * u) := by
  have hcube : 2 ^ (180 * u) ≤ (2 ^ (60 * u)) ^ 3 := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have h := boundedRejections_mass_bound_nat (180 * u) (2 ^ (19 * u))
    (2 ^ (60 * u)) (by positivity) hcube
  have hK2 : (180 * u) ^ 2 ≤ 2 ^ (2 * u) := by
    calc
      _ ≤ (2 ^ u) ^ 2 := Nat.pow_le_pow_left (scale_log_le_pow hu) 2
      _ = 2 ^ (2 * u) := by rw [← pow_mul, Nat.mul_comm u 2]
  have hH3 : (2 ^ (19 * u)) ^ 3 = 2 ^ (57 * u) := by
    rw [← pow_mul]; congr 1; omega
  have hH4 : (2 ^ (19 * u)) ^ 4 = 2 ^ (76 * u) := by
    rw [← pow_mul]; congr 1; omega
  have hraw : (180 * u) ^ 2 * (2 ^ (19 * u)) ^ 3 *
      (3 * (2 ^ (60 * u)) ^ 2 + 1 + 2 * ((180 * u) * 2 ^ (19 * u)) ^ 2) ≤
      6 * 2 ^ (179 * u) := by
    calc
      _ ≤ 2 ^ (2 * u) * 2 ^ (57 * u) * (6 * 2 ^ (120 * u)) :=
        Nat.mul_le_mul (Nat.mul_le_mul hK2 hH3.le) (bounded_solution_factor_scale hu)
      _ = 6 * (2 ^ (2 * u) * 2 ^ (57 * u) * 2 ^ (120 * u)) := by ring
      _ = 6 * 2 ^ (179 * u) := by
        rw [← pow_add, ← pow_add, show 2 * u + 57 * u + 120 * u = 179 * u by omega]
  have hparents : (boundedUnequalParents (2 ^ (180 * u)) (2 ^ (19 * u))).card *
      (180 * u) ^ 2 * (2 ^ (19 * u)) ^ 4 ≤ 2 ^ (179 * u) := by
    calc
      _ ≤ 2 ^ (92 * u) * 2 ^ (2 * u) * 2 ^ (76 * u) :=
        Nat.mul_le_mul (Nat.mul_le_mul (boundedUnequalParents_card_scale hu) hK2) hH4.le
      _ = 2 ^ (170 * u) := by rw [← pow_add, ← pow_add]; congr 1; omega
      _ ≤ 2 ^ (179 * u) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

end Erdos421
