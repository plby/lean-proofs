import StackExchange.Puzzling139335.N4MiddleInvolutions.FaceBounds.Intervals
import StackExchange.Puzzling139335.N4MiddleInvolutions.FaceBounds.Sums.Partition

/-! Span bounds for interval families grouped by the sign of a label. -/

open Set

namespace Puzzling139335.N4MiddleInvolutions.FaceBounds

/-- Disjoint open intervals in a fixed closed interval have total span at
most its length, regardless of the order in which endpoints are named. -/
theorem sum_abs_sub_le_of_disjoint_intervals {ι : Type*}
    (s : Finset ι) (a b : ι → ℝ) {l r : ℝ} (hlr : l ≤ r)
    (ha : ∀ i ∈ s, l ≤ a i ∧ a i ≤ r)
    (hb : ∀ i ∈ s, l ≤ b i ∧ b i ≤ r)
    (hdis : (↑s : Set ι).Pairwise fun i j =>
      Disjoint (Ioo (min (a i) (b i)) (max (a i) (b i)))
        (Ioo (min (a j) (b j)) (max (a j) (b j)))) :
    (∑ i ∈ s, |a i - b i|) ≤ r - l := by
  classical
  have h := sum_interval_lengths_le s (fun i => min (a i) (b i))
    (fun i => max (a i) (b i)) hlr
    (fun i hi => le_min (ha i hi).1 (hb i hi).1)
    (fun i hi => max_le (ha i hi).2 (hb i hi).2)
    (fun i _ => min_le_max) hdis
  simpa only [max_sub_min_eq_abs, abs_sub_comm] using h

/-- When intervals with labels of the same strict sign are pairwise
disjoint, and zero labels have zero span, their total span is at most twice
the length of a common containing interval. -/
theorem sum_abs_sub_le_two_mul_of_signed_intervals {ι : Type*}
    (s : Finset ι) (label a b : ι → ℝ) {l r : ℝ} (hlr : l ≤ r)
    (ha : ∀ i ∈ s, l ≤ a i ∧ a i ≤ r)
    (hb : ∀ i ∈ s, l ≤ b i ∧ b i ≤ r)
    (hzero : ∀ i ∈ s, label i = 0 → |a i - b i| = 0)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 0 < label i * label j →
      Disjoint (Ioo (min (a i) (b i)) (max (a i) (b i)))
        (Ioo (min (a j) (b j)) (max (a j) (b j)))) :
    (∑ i ∈ s, |a i - b i|) ≤ 2 * (r - l) := by
  classical
  apply sum_le_two_mul_of_signed_parts s label (fun i => |a i - b i|) hzero
  · apply sum_abs_sub_le_of_disjoint_intervals _ a b hlr
    · intro i hi
      exact ha i (Finset.mem_filter.mp hi).1
    · intro i hi
      exact hb i (Finset.mem_filter.mp hi).1
    · intro i hi j hj hij
      obtain ⟨his, hip⟩ := Finset.mem_filter.mp hi
      obtain ⟨hjs, hjp⟩ := Finset.mem_filter.mp hj
      exact hdis i his j hjs hij (mul_pos hip hjp)
  · apply sum_abs_sub_le_of_disjoint_intervals _ a b hlr
    · intro i hi
      exact ha i (Finset.mem_filter.mp hi).1
    · intro i hi
      exact hb i (Finset.mem_filter.mp hi).1
    · intro i hi j hj hij
      obtain ⟨his, hin⟩ := Finset.mem_filter.mp hi
      obtain ⟨hjs, hjn⟩ := Finset.mem_filter.mp hj
      exact hdis i his j hjs hij (mul_pos_of_neg_of_neg hin hjn)

end Puzzling139335.N4MiddleInvolutions.FaceBounds
