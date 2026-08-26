import ErdosProblems.Erdos394.Defs

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open Nat Finset

namespace Erdos394

/-- If the block is nonempty, its starting value divides its product. -/
theorem start_dvd_consecutiveProduct {k m : ℕ} (hk : 0 < k) :
    m ∣ consecutiveProduct k m := by
  unfold consecutiveProduct
  simpa using
    (Finset.dvd_prod_of_mem (fun i : ℕ ↦ m + i)
      (show 0 ∈ Finset.range k by simp [hk]))

/-- For positive parameters, the set whose infimum defines `t` is nonempty. -/
theorem admissibleSet_nonempty {k n : ℕ} (hk : 0 < k) (hn : 0 < n) :
    {m : ℕ | 0 < m ∧ n ∣ consecutiveProduct k m}.Nonempty := by
  exact ⟨n, hn, start_dvd_consecutiveProduct hk⟩

/-- The minimum `t k n` itself is an admissible starting value. -/
theorem t_mem {k n : ℕ} (hk : 0 < k) (hn : 0 < n) :
    0 < t k n ∧ n ∣ consecutiveProduct k (t k n) := by
  exact Nat.sInf_mem (admissibleSet_nonempty hk hn)

/-- `t k n` is positive for positive parameters. -/
theorem t_pos {k n : ℕ} (hk : 0 < k) (hn : 0 < n) : 0 < t k n :=
  (t_mem hk hn).1

/-- The defining divisibility condition holds at `t k n`. -/
theorem t_dvd {k n : ℕ} (hk : 0 < k) (hn : 0 < n) :
    n ∣ consecutiveProduct k (t k n) :=
  (t_mem hk hn).2

/-- Every admissible start is at least `t k n`. -/
theorem t_min {k n m : ℕ} (hm : 0 < m)
    (hdiv : n ∣ consecutiveProduct k m) : t k n ≤ m := by
  exact Nat.sInf_le ⟨hm, hdiv⟩

/-- The elementary universal upper bound `t k n ≤ n`. -/
theorem t_le_self {k n : ℕ} (hk : 0 < k) (hn : 0 < n) : t k n ≤ n := by
  exact t_min (m := n) hn (start_dvd_consecutiveProduct hk)

/-- Appending one term multiplies the consecutive product by that term. -/
theorem consecutiveProduct_succ (k m : ℕ) :
    consecutiveProduct (k + 1) m = consecutiveProduct k m * (m + k) := by
  simp [consecutiveProduct, Finset.prod_range_succ]

/-- Increasing the block length by one cannot increase the least start. -/
theorem t_succ_le {k n : ℕ} (hk : 0 < k) (hn : 0 < n) :
    t (k + 1) n ≤ t k n := by
  apply t_min (t_pos hk hn)
  rw [consecutiveProduct_succ]
  exact dvd_mul_of_dvd_left (t_dvd hk hn) _

/-- Starting at one works exactly for the divisors of `k!`. -/
theorem t_eq_one_iff {k n : ℕ} (hk : 0 < k) (hn : 0 < n) :
    t k n = 1 ↔ n ∣ k ! := by
  have hprod : consecutiveProduct k 1 = k ! := by
    simpa [consecutiveProduct, add_comm] using
      (Finset.prod_range_add_one_eq_factorial k)
  constructor
  · intro ht
    simpa [ht, hprod] using t_dvd hk hn
  · intro hdiv
    apply Nat.le_antisymm
    · apply t_min (by simp)
      simpa [hprod] using hdiv
    · exact t_pos hk hn

end Erdos394
