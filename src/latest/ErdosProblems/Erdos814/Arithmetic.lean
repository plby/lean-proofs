import Mathlib

/-!
# Arithmetic for Erdős Problem 814

This file isolates the natural-, integer-, and real-valued identities used at the
boundary of the graph-theoretic argument.  In particular, all subtraction in the
edge shortage is performed in `ℤ`; this is important for the endpoint `k = 2`,
where the shortage is `-1`.
-/

namespace Erdos814

/-- The number of edges in the statement of Erdős Problem 814. -/
def edgeThreshold (k n : ℕ) : ℕ :=
  (k - 1) * (n + 2 - k) + (k - 2).choose 2 + 1

/-- The largest signed shortage allowed by the uniform form of Sauermann's argument. -/
def Tmax (k : ℕ) : ℤ :=
  (((k - 1) * (k - 2) : ℕ) : ℤ) - ((k - 2).choose 2 : ℤ)

/-- The signed shortage corresponding to the edge threshold of Problem 814. -/
def problemT (k : ℕ) : ℤ :=
  Tmax k - 1

/-- A uniform denominator which gives the convenient constant `1 / (10000 k³)`. -/
def uniformDen (k : ℕ) : ℕ :=
  10000 * k ^ 3

theorem edgeThreshold_cast_eq (k n : ℕ) (hk : 2 ≤ k) (hn : k - 1 ≤ n) :
    (edgeThreshold k n : ℤ) = (((k - 1) * n : ℕ) : ℤ) - problemT k := by
  have hkn : k ≤ n + 2 := by omega
  have hk1 : 1 ≤ k := by omega
  have hk2 : 2 ≤ k := hk
  simp only [edgeThreshold, problemT, Tmax]
  push_cast [Nat.cast_sub hkn, Nat.cast_sub hk1, Nat.cast_sub hk2]
  ring

@[simp] theorem problemT_two : problemT 2 = -1 := by
  norm_num [problemT, Tmax]

theorem problemT_add_one_le_Tmax (k : ℕ) : problemT k + 1 ≤ Tmax k := by
  simp [problemT]

theorem Tmax_le_sq (k : ℕ) : Tmax k ≤ (k ^ 2 : ℕ) := by
  have hmul : (k - 1) * (k - 2) ≤ k * k :=
    Nat.mul_le_mul (Nat.sub_le k 1) (Nat.sub_le k 2)
  calc
    Tmax k ≤ (((k - 1) * (k - 2) : ℕ) : ℤ) := by
      simp [Tmax]
    _ ≤ ((k * k : ℕ) : ℤ) := by exact_mod_cast hmul
    _ = (k ^ 2 : ℕ) := by simp [pow_two]

theorem uniformDen_pos (k : ℕ) (hk : 2 ≤ k) : 0 < uniformDen k := by
  simp only [uniformDen]
  positivity

theorem uniformDen_one_le (k : ℕ) (hk : 2 ≤ k) : 1 ≤ uniformDen k := by
  exact uniformDen_pos k hk

theorem uniformDen_cast (k : ℕ) :
    (uniformDen k : ℝ) = 10000 * (k : ℝ) ^ 3 := by
  norm_num [uniformDen]

/-- Convert the integral small-core estimate to the real inequality in the problem. -/
theorem card_le_one_sub_inv_mul
    (k card n : ℕ) (hk : 2 ≤ k)
    (hsmall : uniformDen k * card ≤ (uniformDen k - 1) * n) :
    (card : ℝ) ≤ (1 - 1 / (10000 * (k : ℝ) ^ 3)) * (n : ℝ) := by
  have hDposNat : 0 < uniformDen k := uniformDen_pos k hk
  have hDpos : (0 : ℝ) < uniformDen k := by exact_mod_cast hDposNat
  have hsmall' :
      (uniformDen k : ℝ) * (card : ℝ) ≤
        ((uniformDen k - 1 : ℕ) : ℝ) * (n : ℝ) := by
    exact_mod_cast hsmall
  have hsubcast :
      ((uniformDen k - 1 : ℕ) : ℝ) = (uniformDen k : ℝ) - 1 := by
    rw [Nat.cast_sub (uniformDen_one_le k hk)]
    norm_num
  rw [hsubcast] at hsmall'
  have hcoef :
      1 - 1 / (10000 * (k : ℝ) ^ 3) =
        ((uniformDen k : ℝ) - 1) / (uniformDen k : ℝ) := by
    rw [← uniformDen_cast]
    field_simp
    <;> ring
  rw [hcoef, div_mul_eq_mul_div]
  apply (le_div_iff₀ hDpos).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using hsmall'

end Erdos814
