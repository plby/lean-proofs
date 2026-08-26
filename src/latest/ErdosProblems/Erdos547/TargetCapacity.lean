import ErdosProblems.Erdos547.AllowedWeight

/-!
# A target bin with enough capacity for the next shrub
-/

namespace Erdos547

open Finset
open scoped BigOperators

variable {I : Type*} [Fintype I]

theorem exists_target_outside_small_set (capacity used : I → ℝ)
    (hused : ∀ i, 0 ≤ used i) (s : ℝ) (hs : 0 < s) (hsone : s ≤ 1)
    (hpositive : 0 < ∑ i, capacity i)
    (htotal : (∑ i, used i) ≤ (1 - s) * ∑ i, capacity i)
    (E : Finset I) (hE : (∑ i ∈ E, capacity i) ≤ s / 4 * ∑ i, capacity i) :
    ∃ i, i ∉ E ∧ used i < (1 - s / 2) * capacity i := by
  classical
  by_contra hn
  have hlarge (i : I) (hi : i ∈ (Finset.univ : Finset I) \ E) :
      (1 - s / 2) * capacity i ≤ used i := by
    exact le_of_not_gt fun hh ↦ hn ⟨i, (Finset.mem_sdiff.mp hi).2, hh⟩
  have hsum : (1 - s / 2) * (∑ i ∈ (Finset.univ : Finset I) \ E, capacity i) ≤ ∑ i, used i := by
    rw [Finset.mul_sum]
    exact (Finset.sum_le_sum hlarge).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ ↦ hused i))
  have hsplit := Finset.sum_sdiff (f := capacity) (Finset.subset_univ E)
  have hsplit' := congrArg (fun x : ℝ ↦ (1 - s / 2) * x) hsplit
  have hloss := mul_le_mul_of_nonneg_left hE (show 0 ≤ 1 - s / 2 by linarith only [hsone])
  have hlower : (1 - s / 2) * (1 - s / 4) * (∑ i, capacity i) ≤ ∑ i, used i := by
    nlinarith only [hsum, hsplit', hloss]
  have hstrict : 1 - s < (1 - s / 2) * (1 - s / 4) := by
    nlinarith only [hs, sq_nonneg s]
  have hh := mul_lt_mul_of_pos_right hstrict hpositive
  linarith only [hh, hlower, htotal]

theorem exists_target_capacity (capacity used : I → ℝ)
    (hused : ∀ i, 0 ≤ used i) (s L : ℝ) (hs : 0 < s) (hsone : s ≤ 1) (hL : 0 ≤ L)
    (hpositive : 0 < ∑ i, capacity i)
    (htotal : (∑ i, used i) ≤ (1 - s) * ∑ i, capacity i)
    (hsmall : L * Fintype.card I ≤ s / 4 * ∑ i, capacity i) :
    ∃ i, L ≤ capacity i ∧ used i < (1 - s / 2) * capacity i := by
  classical
  let E := (Finset.univ : Finset I).filter (fun i ↦ capacity i < L)
  have hE : (∑ i ∈ E, capacity i) ≤ s / 4 * ∑ i, capacity i := by
    apply le_trans _ hsmall
    calc
      _ ≤ ∑ _i ∈ E, L := Finset.sum_le_sum fun i hi ↦ (Finset.mem_filter.mp hi).2.le
      _ = L * E.card := by simp [mul_comm]
      _ ≤ L * Fintype.card I := mul_le_mul_of_nonneg_left
        (by exact_mod_cast Finset.card_le_univ E) hL
  obtain ⟨i, hi, hroom⟩ := exists_target_outside_small_set capacity used hused s hs hsone
    hpositive htotal E hE
  refine ⟨i, ?_, hroom⟩
  exact le_of_not_gt fun hh ↦ hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)

theorem target_capacity_after_extension (capacity used added s : ℝ)
    (hcapacity : 0 < capacity) (hs : 0 < s)
    (htarget : used < (1 - s / 2) * capacity) (hadded : added ≤ s / 4 * capacity) :
    used + added < capacity := by
  have hh := mul_pos hs hcapacity
  nlinarith only [hh, htarget, hadded]

end Erdos547

#print axioms Erdos547.exists_target_capacity
