import Arxiv.Arxiv2411_18291.FlatteningRecurrence
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The total degree cost of repeated multiplicity reduction

The number of rounds grows doubly logarithmically with the initial bound.
For every fixed per-round cost and every positive exponent, its total cost
is eventually smaller than that power of the ambient size.
-/

open Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem flatteningStep_le_of_sixteen_le {n x : ℕ} (hn : 16 ≤ n) (hx : x ≤ n) :
    flatteningStep x ≤ n := by
  by_cases h : x ≤ 16
  · simpa only [flatteningStep_of_le_sixteen h] using hn
  · exact (flatteningStep_lt (show 16 < x by omega)).le.trans hx

theorem iterate_flatteningStep_le_initial {n : ℕ} (hn : 16 ≤ n) (k : ℕ) :
    (flatteningStep^[k]) n ≤ n := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact flatteningStep_le_of_sixteen_le hn ih

theorem flatteningCapacity_mono : Monotone flatteningCapacity := by
  intro k l hkl
  exact Nat.mul_le_mul_left 16 (pow_le_pow_right' (by decide : 1 ≤ (4 : ℕ))
    (pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) hkl))

theorem exists_flatteningCapacity_ge (n : ℕ) : ∃ k, n ≤ flatteningCapacity k := by
  have hpow : ∀ k : ℕ, k ≤ 2 ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hpos : 0 < 2 ^ k := by positivity
      rw [pow_succ]
      omega
  refine ⟨n, (hpow n).trans ?_⟩
  have hbase : 2 ^ (2 ^ n) ≤ 4 ^ (2 ^ n) := pow_le_pow_left' (by decide) _
  have hp : 2 ^ n ≤ 4 ^ (2 ^ n) := (hpow (2 ^ n)).trans hbase
  unfold flatteningCapacity
  omega

theorem eventually_flattening_cost_le_capacity {C ε : ℝ} (hC : 1 ≤ C) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, C ^ (k + 3) ≤ (flatteningCapacity k : ℝ) ^ ε := by
  have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2)
  have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1 : ℝ) < 2)
  have hlim : Tendsto (fun k : ℕ => ((k : ℝ) + 3) * Real.log C / (2 : ℝ) ^ k)
      atTop (𝓝 0) := by
    have h := (h1.add (h0.const_mul 3)).mul_const (Real.log C)
    simp only [pow_one, pow_zero, mul_zero, zero_add, zero_mul] at h
    convert h using 1
    funext k
    ring
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  filter_upwards [hlim.eventually (gt_mem_nhds (mul_pos hε hlog4))] with k hk
  have hpow : (0 : ℝ) < 2 ^ k := by positivity
  have hnum := ((div_lt_iff₀ hpow).mp hk).le
  have hcap : 0 < (flatteningCapacity k : ℝ) := by unfold flatteningCapacity; positivity
  have hlog : Real.log (flatteningCapacity k : ℝ) =
      Real.log 16 + (2 : ℝ) ^ k * Real.log 4 := by
    simp only [flatteningCapacity, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    rfl
  apply (Real.log_le_log_iff (pow_pos (by linarith only [hC]) _)
    (Real.rpow_pos_of_pos hcap _)).mp
  rw [Real.log_pow, Real.log_rpow hcap, hlog]
  push_cast
  have hnonneg : 0 ≤ ε * Real.log 16 :=
    mul_nonneg hε.le (Real.log_nonneg (by norm_num))
  nlinarith only [hnum, hnonneg]

theorem eventually_exists_flattening_iterations {C ε : ℝ} (hC : 1 ≤ C) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ k : ℕ, (flatteningStep^[k]) n ≤ 16 ∧ C ^ k ≤ (n : ℝ) ^ ε := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp (eventually_flattening_cost_le_capacity hC hε)
  filter_upwards [eventually_ge_atTop (flatteningCapacity K + 1)] with n hn
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
    _ ≤ (flatteningCapacity k : ℝ) ^ ε := hK k hk
    _ ≤ (n : ℝ) ^ ε := Real.rpow_le_rpow (Nat.cast_nonneg _)
      (by exact_mod_cast hprev.le) hε.le

end Arxiv2411_18291
