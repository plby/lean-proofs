/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.Base

/-!
# Exact disjoint interval allocation by finite prefix sums

All lengths and endpoints are natural numbers, so rounding is handled
before the capacity condition is applied.
-/

namespace Erdos4b

open scoped BigOperators

def sourceAllocatedStart (E : Finset ℕ) (length : ℕ → ℕ) (base m : ℕ) : ℕ :=
  base + ∑ j ∈ E.filter (· < m), length j

def sourceAllocatedEnd (E : Finset ℕ) (length : ℕ → ℕ) (base m : ℕ) : ℕ :=
  sourceAllocatedStart E length base m + length m

theorem sourceAllocatedStart_le_end (E : Finset ℕ) (length : ℕ → ℕ) (base m : ℕ) :
    sourceAllocatedStart E length base m ≤ sourceAllocatedEnd E length base m :=
  Nat.le_add_right _ _

theorem base_le_sourceAllocatedStart (E : Finset ℕ) (length : ℕ → ℕ) (base m : ℕ) :
    base ≤ sourceAllocatedStart E length base m := Nat.le_add_right _ _

theorem sourceAllocatedEnd_le_total {E : Finset ℕ} (length : ℕ → ℕ)
    (base : ℕ) {m : ℕ} (hm : m ∈ E) :
    sourceAllocatedEnd E length base m ≤ base + ∑ j ∈ E, length j := by
  have hnot : m ∉ E.filter (· < m) := by simp
  have hsub : insert m (E.filter (· < m)) ⊆ E :=
    Finset.insert_subset hm (Finset.filter_subset _ _)
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ ↦ Nat.zero_le (length j))
  rw [Finset.sum_insert hnot] at hsum
  unfold sourceAllocatedEnd sourceAllocatedStart
  omega

theorem sourceAllocatedEnd_le_nextStart {E : Finset ℕ} (length : ℕ → ℕ)
    (base : ℕ) {m n : ℕ} (hm : m ∈ E) (hmn : m < n) :
    sourceAllocatedEnd E length base m ≤ sourceAllocatedStart E length base n := by
  have hnot : m ∉ E.filter (· < m) := by simp
  have hsub : insert m (E.filter (· < m)) ⊆ E.filter (· < n) := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact Finset.mem_filter.mpr ⟨hm, hmn⟩
    · have hd := Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨hd.1, hd.2.trans hmn⟩
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ ↦ Nat.zero_le (length j))
  rw [Finset.sum_insert hnot] at hsum
  unfold sourceAllocatedEnd sourceAllocatedStart
  omega

theorem sourceAllocated_primeIntervals_disjoint {E : Finset ℕ} (length : ℕ → ℕ)
    (base : ℕ) {m n : ℕ} (hm : m ∈ E) (hn : n ∈ E) (hmn : m ≠ n) :
    Disjoint
      (auxiliaryPrimeInterval (sourceAllocatedStart E length base m)
        (sourceAllocatedEnd E length base m))
      (auxiliaryPrimeInterval (sourceAllocatedStart E length base n)
        (sourceAllocatedEnd E length base n)) := by
  rw [Finset.disjoint_left]
  intro q hqm hqn
  have hqm' := mem_auxiliaryPrimeInterval.mp hqm
  have hqn' := mem_auxiliaryPrimeInterval.mp hqn
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · have := sourceAllocatedEnd_le_nextStart length base hm hlt
    omega
  · have := sourceAllocatedEnd_le_nextStart length base hn hgt
    omega

theorem sourceAllocated_upperHalf_range {E : Finset ℕ} (length : ℕ → ℕ)
    {base X : ℕ} (hhalf : X ≤ 2 * base) (hcapacity : base + ∑ j ∈ E, length j ≤ X)
    {m : ℕ} (hm : m ∈ E) :
    X ≤ 2 * sourceAllocatedStart E length base m ∧
      sourceAllocatedStart E length base m ≤ sourceAllocatedEnd E length base m ∧
      sourceAllocatedEnd E length base m ≤ X :=
  ⟨hhalf.trans (Nat.mul_le_mul_left 2 (base_le_sourceAllocatedStart E length base m)),
    sourceAllocatedStart_le_end E length base m,
    (sourceAllocatedEnd_le_total length base hm).trans hcapacity⟩

theorem sourceAllocated_real_length (E : Finset ℕ) (length : ℕ → ℕ) (base m : ℕ) :
    (sourceAllocatedEnd E length base m : ℝ) - sourceAllocatedStart E length base m = length m := by
  simp only [sourceAllocatedEnd, Nat.cast_add, add_sub_cancel_left]

end Erdos4b
