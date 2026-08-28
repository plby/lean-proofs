import Wikipedia.HopfProblem.FourthHurewiczFourSimplexQuotientMinimum
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Prefix minima after inserting a cube coordinate

Before the inserted position a prefix is unchanged.  Once the inserted
position is included, its value is the minimum of the inserted coordinate
and the corresponding original prefix.  In particular, inserting one only
shifts the later prefix indices.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.SimplexGeometry

private theorem succAbove_lt_prefix_iff {n : ℕ} (i : Fin (n + 1))
    (j : Fin n) (k : ℕ) (h : k ≤ i.val) :
    (i.succAbove j).val < k ↔ j.val < k := by
  by_cases hji : j.castSucc < i
  · rw [Fin.succAbove_of_castSucc_lt i j hji]
    rfl
  · rw [Fin.succAbove_of_le_castSucc i j (le_of_not_gt hji)]
    simp only [Fin.lt_def, Fin.val_castSucc] at hji
    simp only [Fin.val_succ]
    omega

private theorem succAbove_lt_prefix_succ_iff {n : ℕ} (i : Fin (n + 1))
    (j : Fin n) (k : ℕ) (h : i.val ≤ k) :
    (i.succAbove j).val < k + 1 ↔ j.val < k := by
  by_cases hji : j.castSucc < i
  · rw [Fin.succAbove_of_castSucc_lt i j hji]
    simp only [Fin.lt_def, Fin.val_castSucc] at hji
    simp only [Fin.val_castSucc]
    omega
  · rw [Fin.succAbove_of_le_castSucc i j (le_of_not_gt hji)]
    simp only [Fin.val_succ, Nat.add_lt_add_iff_right]

/-- A prefix ending before an inserted coordinate does not depend on that coordinate. -/
theorem prefixMinimum_insertNth_le {n : ℕ} (i : Fin (n + 1)) (ε : I)
    (u : Fin n → I) (k : ℕ) (h : k ≤ i.val) :
    prefixMinimum (Fin.insertNth i ε u) k = prefixMinimum u k := by
  apply eq_of_forall_le_iff
  intro a
  simp only [prefixMinimum, Finset.le_inf_iff, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [Fin.forall_iff_succAbove i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
    succAbove_lt_prefix_iff i _ k h, not_lt_of_ge h, false_implies, true_and]

/-- A prefix containing the inserted coordinate includes exactly one extra minimum. -/
theorem prefixMinimum_insertNth_succ {n : ℕ} (i : Fin (n + 1)) (ε : I)
    (u : Fin n → I) (k : ℕ) (h : i.val ≤ k) :
    prefixMinimum (Fin.insertNth i ε u) (k + 1) = min ε (prefixMinimum u k) := by
  apply eq_of_forall_le_iff
  intro a
  simp only [prefixMinimum, Finset.le_inf_iff, Finset.mem_filter,
    Finset.mem_univ, true_and, le_min_iff]
  rw [Fin.forall_iff_succAbove i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
    succAbove_lt_prefix_succ_iff i _ k h, Nat.lt_succ_of_le h, true_implies]

/-- Inserting one leaves every earlier prefix unchanged. -/
theorem prefixMinimum_insertNth_one_le {n : ℕ} (i : Fin (n + 1))
    (u : Fin n → I) (k : ℕ) (h : k ≤ i.val) :
    prefixMinimum (Fin.insertNth i 1 u) k = prefixMinimum u k :=
  prefixMinimum_insertNth_le i 1 u k h

/-- Inserting one shifts each later prefix by one without changing its value. -/
theorem prefixMinimum_insertNth_one_succ {n : ℕ} (i : Fin (n + 1))
    (u : Fin n → I) (k : ℕ) (h : i.val ≤ k) :
    prefixMinimum (Fin.insertNth i 1 u) (k + 1) = prefixMinimum u k := by
  rw [prefixMinimum_insertNth_succ i 1 u k h]
  exact min_eq_right (show prefixMinimum u k ≤ (⊤ : I) from le_top)

/-- Appending a coordinate leaves all prefixes of the original tuple unchanged. -/
theorem prefixMinimum_insertNth_last_le {n : ℕ} (u : Fin n → I) (ε : I)
    (k : ℕ) (hk : k ≤ n) :
    prefixMinimum (Fin.insertNth (Fin.last n) ε u) k = prefixMinimum u k :=
  prefixMinimum_insertNth_le (Fin.last n) ε u k hk

end Wikipedia.HopfProblem.HigherHurewicz.SimplexGeometry
