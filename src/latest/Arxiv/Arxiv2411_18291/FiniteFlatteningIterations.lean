import Arxiv.Arxiv2411_18291.FlatteningIterationCost
import Mathlib.Algebra.Order.Floor.Semiring

/-! # Explicit finite criteria for the cost of repeated flattening -/

noncomputable section

namespace Arxiv2411_18291

theorem add_three_le_mul_two_pow (K d : ℕ) : K + d + 3 ≤ (K + 3) * 2 ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hp : 1 ≤ (K + 3) * 2 ^ d := Nat.succ_le_of_lt (by positivity)
    rw [pow_succ]
    nlinarith only [ih, hp]

theorem flattening_cost_le_capacity_of_log_bound {C ε : ℝ} {K k : ℕ}
    (hC : 1 ≤ C) (hε : 0 ≤ ε)
    (hstart : ((K : ℝ) + 3) * Real.log C ≤ ε * (2 : ℝ) ^ K * Real.log 4)
    (hKk : K ≤ k) : C ^ (k + 3) ≤ (flatteningCapacity k : ℝ) ^ ε := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hKk
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hgrowth : (K + d + 3 : ℕ) ≤ (K + 3) * 2 ^ d := add_three_le_mul_two_pow K d
  have hgrowth' : ((K + d : ℕ) : ℝ) + 3 ≤ ((K : ℝ) + 3) * (2 : ℝ) ^ d := by
    exact_mod_cast hgrowth
  have hnum : (((K + d : ℕ) : ℝ) + 3) * Real.log C ≤
      ε * (2 : ℝ) ^ (K + d) * Real.log 4 := by
    calc
      _ ≤ (((K : ℝ) + 3) * (2 : ℝ) ^ d) * Real.log C :=
        mul_le_mul_of_nonneg_right hgrowth' hlogC
      _ = (((K : ℝ) + 3) * Real.log C) * (2 : ℝ) ^ d := by ring
      _ ≤ (ε * (2 : ℝ) ^ K * Real.log 4) * (2 : ℝ) ^ d :=
        mul_le_mul_of_nonneg_right hstart (by positivity)
      _ = _ := by rw [pow_add]; ring
  have hcap : 0 < (flatteningCapacity (K + d) : ℝ) := by
    unfold flatteningCapacity
    positivity
  have hlog : Real.log (flatteningCapacity (K + d) : ℝ) =
      Real.log 16 + (2 : ℝ) ^ (K + d) * Real.log 4 := by
    simp only [flatteningCapacity, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    rfl
  apply (Real.log_le_log_iff (pow_pos (lt_of_lt_of_le zero_lt_one hC) _)
    (Real.rpow_pos_of_pos hcap _)).mp
  rw [Real.log_pow, Real.log_rpow hcap, hlog]
  push_cast
  have hnonneg : 0 ≤ ε * Real.log 16 :=
    mul_nonneg hε (Real.log_nonneg (by norm_num))
  push_cast at hnum
  nlinarith only [hnum, hnonneg]

/-- A single logarithmic inequality supplies a finite iteration threshold. -/
theorem exists_flattening_iterations_of_log_bound {C ε : ℝ} {K n : ℕ}
    (hC : 1 ≤ C) (hε : 0 < ε)
    (hstart : ((K : ℝ) + 3) * Real.log C ≤ ε * (2 : ℝ) ^ K * Real.log 4)
    (hn : flatteningCapacity K < n) :
    ∃ k : ℕ, (flatteningStep^[k]) n ≤ 16 ∧ C ^ k ≤ (n : ℝ) ^ ε := by
  let j := Nat.find (exists_flatteningCapacity_ge n)
  have hj : n ≤ flatteningCapacity j := Nat.find_spec (exists_flatteningCapacity_ge n)
  have hKj : K < j := by
    by_contra h
    have hh := flatteningCapacity_mono (show j ≤ K by omega)
    omega
  obtain ⟨k, hjk⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
  rw [hjk] at hj hKj
  have hk : K ≤ k := by omega
  have hprev : flatteningCapacity k < n := by
    have h := Nat.find_min (exists_flatteningCapacity_ge n) (show k < j by omega)
    omega
  refine ⟨k + 1 + 2, iterate_flatteningStep_le_sixteen (k + 1) n hj, ?_⟩
  calc
    _ = C ^ (k + 3) := rfl
    _ ≤ (flatteningCapacity k : ℝ) ^ ε :=
      flattening_cost_le_capacity_of_log_bound hC hε.le hstart hk
    _ ≤ _ := Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hprev.le) hε.le

theorem sq_le_two_pow_of_four_le {k : ℕ} (hk : 4 ≤ k) : k ^ 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hp : 4 * k ≤ k ^ 2 := by simpa only [pow_two] using Nat.mul_le_mul_right k hk
    rw [pow_succ (2 : ℕ) k]
    nlinarith only [hk, ih, hp]

/-- A conservative explicit threshold. The logarithmic criterion above can
be used directly when a substantially smaller threshold is desired. -/
def flatteningCostThreshold (C ε : ℝ) : ℕ :=
  flatteningCapacity (max 4 ⌈2 * Real.log C / (ε * Real.log 4)⌉₊) + 1

theorem exists_flattening_iterations_explicit {C ε : ℝ} {n : ℕ}
    (hC : 1 ≤ C) (hε : 0 < ε) (hn : flatteningCostThreshold C ε ≤ n) :
    ∃ k : ℕ, (flatteningStep^[k]) n ≤ 16 ∧ C ^ k ≤ (n : ℝ) ^ ε := by
  let K := max 4 ⌈2 * Real.log C / (ε * Real.log 4)⌉₊
  have hK : 4 ≤ K := le_max_left _ _
  have hKreal : (4 : ℝ) ≤ K := by exact_mod_cast hK
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hden : 0 < ε * Real.log 4 := mul_pos hε hlog4
  have hceil : 2 * Real.log C / (ε * Real.log 4) ≤ (K : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 4
      ⌈2 * Real.log C / (ε * Real.log 4)⌉₊))
  have hCK := (div_le_iff₀ hden).mp hceil
  have hsq : (K : ℝ) ^ 2 ≤ (2 : ℝ) ^ K := by
    exact_mod_cast sq_le_two_pow_of_four_le hK
  have hstart : ((K : ℝ) + 3) * Real.log C ≤ ε * (2 : ℝ) ^ K * Real.log 4 := by
    calc
      _ ≤ (2 * (K : ℝ)) * Real.log C :=
        mul_le_mul_of_nonneg_right (by linarith only [hKreal]) (Real.log_nonneg hC)
      _ = (K : ℝ) * (2 * Real.log C) := by ring
      _ ≤ (K : ℝ) * ((K : ℝ) * (ε * Real.log 4)) :=
        mul_le_mul_of_nonneg_left hCK (Nat.cast_nonneg _)
      _ = ε * (K : ℝ) ^ 2 * Real.log 4 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hε.le) hlog4.le
  exact exists_flattening_iterations_of_log_bound hC hε hstart
    (by change flatteningCapacity K + 1 ≤ n at hn; omega)

end Arxiv2411_18291
