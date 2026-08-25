import Util.Linnik.PowerSum

/-!
# Finite exponential moments from cumulative density bounds

The finite form of the zero-density summation argument separates the
elementary geometric series from the analytic family of zeros.
-/

namespace Linnik

open scoped BigOperators Classical

theorem sum_half_pow_le_two (N : ℕ) :
    (∑ j ∈ Finset.range N, (1 / 2 : ℝ) ^ j) ≤ 2 := by
  have h := sum_half_pow_succ N
  have heq : (∑ j ∈ Finset.range N, (1 / 2 : ℝ) ^ j) =
      2 * ∑ j ∈ Finset.range N, (1 / 2 : ℝ) ^ (j + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_succ]
    ring
  rw [heq, h]
  have hp : 0 ≤ (1 / 2 : ℝ) ^ N := by positivity
  linarith

theorem exp_neg_two_le_half : Real.exp (-2) ≤ (1 / 2 : ℝ) := by
  rw [Real.exp_neg]
  apply (inv_le_iff_one_le_mul₀ (Real.exp_pos 2)).mpr
  have h := Real.add_one_le_exp (2 : ℝ)
  linarith

theorem exp_moment_le_of_cumulative_bound
    {ι : Type*} (S : Finset ι) (u a : ι → ℝ) (N : ℕ)
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (ha : ∀ i ∈ S, 0 ≤ a i)
    (hu₀ : ∀ i ∈ S, 0 ≤ u i) (huN : ∀ i ∈ S, u i < N + 1)
    (hdensity : ∀ j ∈ Finset.range (N + 1),
      (∑ i ∈ S.filter (fun i ↦ u i < j + 1), a i) ≤ C * Real.exp (c * (j + 1))) :
    (∑ i ∈ S, a i * Real.exp (-(c + 2) * u i)) ≤ 2 * C * Real.exp c := by
  have hpoint (i : ι) (hi : i ∈ S) :
      Real.exp (-(c + 2) * u i) ≤
        ∑ j ∈ Finset.range (N + 1),
          if u i < j + 1 then Real.exp (-(c + 2) * j) else 0 := by
    let j : ℕ := ⌊u i⌋₊
    have hjle : (j : ℝ) ≤ u i := Nat.floor_le (hu₀ i hi)
    have hij : u i < (j : ℝ) + 1 := Nat.lt_floor_add_one _
    have hjN : j < N + 1 := by
      have hreal : (j : ℝ) < (N : ℝ) + 1 := hjle.trans_lt (huN i hi)
      exact_mod_cast hreal
    have hexp : Real.exp (-(c + 2) * u i) ≤ Real.exp (-(c + 2) * j) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    apply hexp.trans
    have hsingle := Finset.single_le_sum
      (s := Finset.range (N + 1))
      (f := fun k : ℕ ↦ if u i < k + 1 then Real.exp (-(c + 2) * k) else 0)
      (fun k _ ↦ by split_ifs <;> positivity) (Finset.mem_range.mpr hjN)
    simpa only [if_pos hij] using hsingle
  have hfirst : (∑ i ∈ S, a i * Real.exp (-(c + 2) * u i)) ≤
      ∑ j ∈ Finset.range (N + 1), Real.exp (-(c + 2) * j) *
        ∑ i ∈ S.filter (fun i ↦ u i < j + 1), a i := by
    calc
      (∑ i ∈ S, a i * Real.exp (-(c + 2) * u i)) ≤
          ∑ i ∈ S, a i * ∑ j ∈ Finset.range (N + 1),
            if u i < j + 1 then Real.exp (-(c + 2) * j) else 0 :=
        Finset.sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left (hpoint i hi) (ha i hi)
      _ = _ := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> ring
  apply hfirst.trans
  calc
    (∑ j ∈ Finset.range (N + 1), Real.exp (-(c + 2) * j) *
        ∑ i ∈ S.filter (fun i ↦ u i < j + 1), a i) ≤
        ∑ j ∈ Finset.range (N + 1),
          Real.exp (-(c + 2) * j) * (C * Real.exp (c * (j + 1))) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hdensity j hj) (Real.exp_pos _).le
    _ ≤ ∑ j ∈ Finset.range (N + 1), C * Real.exp c * (1 / 2 : ℝ) ^ j := by
      apply Finset.sum_le_sum
      intro j _
      have hid : Real.exp (-(c + 2) * j) * (C * Real.exp (c * (j + 1))) =
          C * Real.exp c * Real.exp (-2) ^ j := by
        rw [← Real.exp_nat_mul]
        have hexp : -(c + 2) * (j : ℝ) + c * (j + 1) = c + (j : ℝ) * (-2) := by ring
        calc
          _ = C * Real.exp (-(c + 2) * j + c * (j + 1)) := by rw [Real.exp_add]; ring
          _ = _ := by rw [hexp, Real.exp_add]; ring
      rw [hid]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_two_le_half j) (by positivity)
    _ = C * Real.exp c * ∑ j ∈ Finset.range (N + 1), (1 / 2 : ℝ) ^ j :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ C * Real.exp c * 2 :=
      mul_le_mul_of_nonneg_left (sum_half_pow_le_two _) (by positivity)
    _ = 2 * C * Real.exp c := by ring

/-- Repulsion amplifies a bounded exponential moment by a power of the
exceptional gap. -/
theorem exp_moment_amplification
    {ι : Type*} (S : Finset ι) (delta a : ι → ℝ)
    {H R C lambda : ℝ}
    (ha : ∀ i ∈ S, 0 ≤ a i)
    (hrepulsion : ∀ i ∈ S, Real.exp (-R * delta i) ≤ lambda)
    (hmoment : (∑ i ∈ S, a i * Real.exp (-H * delta i)) ≤ C) :
    (∑ i ∈ S, a i * Real.exp (-(H + 2 * R) * delta i)) ≤ C * lambda ^ 2 := by
  calc
    (∑ i ∈ S, a i * Real.exp (-(H + 2 * R) * delta i)) ≤
        ∑ i ∈ S, (a i * Real.exp (-H * delta i)) * lambda ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hexp : Real.exp (-(H + 2 * R) * delta i) =
          Real.exp (-H * delta i) * Real.exp (-R * delta i) ^ 2 := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
      rw [hexp, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Real.exp_pos _).le (hrepulsion i hi) 2)
        (mul_nonneg (ha i hi) (Real.exp_pos _).le)
    _ = (∑ i ∈ S, a i * Real.exp (-H * delta i)) * lambda ^ 2 :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ C * lambda ^ 2 := mul_le_mul_of_nonneg_right hmoment (sq_nonneg lambda)

end Linnik
