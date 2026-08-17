/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos95.RpowBookkeeping

/-!
# Fixed parameters for Guth's partitioning recurrence

For every positive loss `η ≤ 1/4` we choose a finite sequence of box
degrees.  Its number of sign cells dominates both the bad-cell loss and the
`(3/2+η)` moment of the good cell line counts.
-/

open scoped BigOperators

namespace Erdos95.GuthParameters

/-- The sum of the degree budgets for the successive cuts. -/
def wallDegree {J : ℕ} (k : Fin J → ℕ) : ℕ :=
  ∑ j, 3 * k j

/-- One more than the wall degree, the line--cell crossing budget. -/
def crossingBudget {J : ℕ} (k : Fin J → ℕ) : ℕ :=
  wallDegree k + 1

/-- Numerical data needed by one fixed-degree partitioning step. -/
structure Parameters (η : ℝ) where
  J : ℕ
  k : Fin J → ℕ
  c : ℕ
  c_pos : 0 < c
  fit : ∀ j : Fin J, 2 ^ (j : ℕ) < (k j + 1) ^ 3
  bad_half : 2 * (c * crossingBudget k) ≤ 2 ^ J
  contraction :
    16 * (((1 : ℝ) / (c : ℝ)) ^ ((1 : ℝ) / 2 + η)) *
        (crossingBudget k : ℝ) ≤ 1

theorem wallDegree_const (J K : ℕ) :
    wallDegree (fun _ : Fin J ↦ K) = J * (3 * K) := by
  simp [wallDegree]

/-- Exponential growth supplies admissible fixed parameters for every
positive `η`.  The explicit construction uses `J=3ts`, cut box degree
`2^(ts)`, and bad-cell threshold `2^((2t-1)s)`. -/
theorem exists_parameters {η : ℝ} (hη : 0 < η)
    (hηle : η ≤ (1 : ℝ) / 4) : Nonempty (Parameters η) := by
  obtain ⟨t, ht⟩ := exists_nat_gt ((1 : ℝ) / η)
  have htpos : 0 < t := by
    by_contra ht0
    have : t = 0 := Nat.eq_zero_of_not_pos ht0
    subst t
    simp only [Nat.cast_zero] at ht
    have : 0 < (1 : ℝ) / η := one_div_pos.mpr hη
    linarith
  have hηt : 1 < η * (t : ℝ) := by
    have := (div_lt_iff₀ hη).mp ht
    simpa [mul_comm] using this
  let C : ℕ := 288 * t
  let s : ℕ := 2 * C
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hspos : 0 < s := by dsimp [s]; positivity
  have hCs : C * s ≤ 2 ^ s := by
    have hpow := Nat.two_mul_sq_add_one_le_two_pow_two_mul C
    dsimp [s]
    nlinarith
  let J : ℕ := 3 * t * s
  let K : ℕ := 2 ^ (t * s)
  let k : Fin J → ℕ := fun _ ↦ K
  let c : ℕ := 2 ^ ((2 * t - 1) * s)
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hJpos : 0 < J := by dsimp [J]; positivity
  have hwall : wallDegree k = 9 * t * s * 2 ^ (t * s) := by
    rw [show wallDegree k = J * (3 * K) by
      simpa [k] using wallDegree_const J K]
    simp only [J, K]
    ring
  have hwallpos : 0 < wallDegree k := by rw [hwall]; positivity
  have hcross_le : crossingBudget k ≤ 2 * wallDegree k := by
    simp only [crossingBudget]
    omega
  refine ⟨⟨J, k, c, hcpos, ?_, ?_, ?_⟩⟩
  · intro j
    have hjJ : (j : ℕ) < J := j.isLt
    have hpowj : 2 ^ (j : ℕ) < 2 ^ J :=
      Nat.pow_lt_pow_right (by omega) hjJ
    have hJK : 2 ^ J = K ^ 3 := by
      dsimp [J, K]
      rw [← pow_mul]
      congr 1
      ring
    calc
      2 ^ (j : ℕ) < 2 ^ J := hpowj
      _ = K ^ 3 := hJK
      _ < (K + 1) ^ 3 := by
        exact Nat.pow_lt_pow_left (Nat.lt_succ_self K) (by omega)
      _ = (k j + 1) ^ 3 := by rfl
  · have h36 : 36 * t * s ≤ 2 ^ s := by
      calc
        36 * t * s ≤ (288 * t) * s := by gcongr <;> omega
        _ = C * s := by rfl
        _ ≤ 2 ^ s := hCs
    have hbadCore :
        4 * c * wallDegree k ≤ 2 ^ J := by
      rw [hwall]
      dsimp only [c, J]
      have hexp : (2 * t - 1) * s + t * s = 3 * t * s - s := by
        have hsle' : s ≤ 2 * t * s := by
          nlinarith
        calc
          (2 * t - 1) * s + t * s =
              (2 * t * s - s) + t * s := by rw [Nat.sub_mul]; simp
          _ = 2 * t * s + t * s - s :=
            (Nat.sub_add_comm hsle').symm
          _ = 3 * t * s - s := by congr 1 <;> ring
      have hsle : s ≤ 3 * t * s := by
        nlinarith
      calc
        4 * 2 ^ ((2 * t - 1) * s) *
            (9 * t * s * 2 ^ (t * s)) =
            (36 * t * s) *
              2 ^ ((2 * t - 1) * s + t * s) := by
          rw [pow_add]
          ring
        _ ≤ 2 ^ s * 2 ^ (3 * t * s - s) :=
          by
            rw [hexp]
            exact Nat.mul_le_mul_right _ h36
        _ = 2 ^ (3 * t * s) := by
          rw [← pow_add, Nat.add_sub_of_le hsle]
    calc
      2 * (c * crossingBudget k) ≤ 2 * (c * (2 * wallDegree k)) := by
        gcongr
      _ = 4 * c * wallDegree k := by ring
      _ ≤ 2 ^ J := hbadCore
  · have h288 : 288 * t * s ≤ 2 ^ s := by
      simpa [C] using hCs
    have hleft :
        16 * (crossingBudget k : ℝ) ≤
          ((2 : ℝ) ^ (((t + 1) * s : ℕ) : ℝ)) := by
      have hnat : 16 * crossingBudget k ≤ 2 ^ ((t + 1) * s) := by
        calc
          16 * crossingBudget k ≤ 32 * wallDegree k := by
            omega
          _ = (288 * t * s) * 2 ^ (t * s) := by
            rw [hwall]
            ring
          _ ≤ 2 ^ s * 2 ^ (t * s) := by gcongr
          _ = 2 ^ ((t + 1) * s) := by
            rw [← pow_add]
            congr 1
            ring
      exact_mod_cast hnat
    have hexponent :
        (((t + 1) * s : ℕ) : ℝ) ≤
          (((2 * t - 1) * s : ℕ) : ℝ) *
            ((1 : ℝ) / 2 + η) := by
      have hbase : (t : ℝ) + 1 ≤
          (2 * (t : ℝ) - 1) * ((1 : ℝ) / 2 + η) := by
        nlinarith [hηt, hηle]
      have hcastE : (((2 * t - 1) * s : ℕ) : ℝ) =
          (2 * (t : ℝ) - 1) * (s : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ 2 * t)]
        push_cast
        ring
      calc
        (((t + 1) * s : ℕ) : ℝ) =
            ((t : ℝ) + 1) * (s : ℝ) := by push_cast; ring
        _ ≤ ((2 * (t : ℝ) - 1) * ((1 : ℝ) / 2 + η)) *
            (s : ℝ) :=
          mul_le_mul_of_nonneg_right hbase (by positivity)
        _ = (((2 * t - 1) * s : ℕ) : ℝ) *
            ((1 : ℝ) / 2 + η) := by
          rw [hcastE]
          ring
    have hright :
        ((2 : ℝ) ^ (((t + 1) * s : ℕ) : ℝ)) ≤
          (c : ℝ) ^ ((1 : ℝ) / 2 + η) := by
      have hpowexp := Real.rpow_le_rpow_of_exponent_le
        (show (1 : ℝ) ≤ 2 by norm_num) hexponent
      calc
        ((2 : ℝ) ^ (((t + 1) * s : ℕ) : ℝ)) ≤
            (2 : ℝ) ^
              ((((2 * t - 1) * s : ℕ) : ℝ) *
                ((1 : ℝ) / 2 + η)) := hpowexp
        _ = ((2 : ℝ) ^ (((2 * t - 1) * s : ℕ) : ℝ)) ^
              ((1 : ℝ) / 2 + η) :=
          Real.rpow_mul (by positivity) _ _
        _ = (c : ℝ) ^ ((1 : ℝ) / 2 + η) := by
          rw [Real.rpow_natCast]
          norm_cast
    have hden :
        16 * (crossingBudget k : ℝ) ≤
          (c : ℝ) ^ ((1 : ℝ) / 2 + η) := hleft.trans hright
    have hcpow : 0 < (c : ℝ) ^ ((1 : ℝ) / 2 + η) := by
      exact Real.rpow_pos_of_pos (by positivity) _
    rw [Real.div_rpow (by positivity) (by positivity)]
    rw [Real.one_rpow]
    calc
      16 * (1 / ((c : ℝ) ^ ((1 : ℝ) / 2 + η))) *
          (crossingBudget k : ℝ) =
          (16 * (crossingBudget k : ℝ)) /
            ((c : ℝ) ^ ((1 : ℝ) / 2 + η)) := by
        field_simp
      _ ≤ 1 := (div_le_one hcpow).mpr hden

end Erdos95.GuthParameters
