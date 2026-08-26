import ErdosProblems.Erdos421.ArithmeticReciprocalSquares

/-! # Summing the positive and negative nonzero Fourier modes -/

namespace Erdos421

theorem sum_integer_arithmetic_inverse_squares_le (S : Finset ℤ)
    (hS : ∀ n ∈ S, n ≠ 0) {d Y : ℝ} (hd : 0 < d) (hY : 0 < Y) :
    (∑ n ∈ S, 1 / (d + Y * |(n : ℝ)|) ^ 2) ≤ 2 / (Y * d) := by
  classical
  let P := S.filter (fun n ↦ 0 < n)
  let N := S.filter (fun n ↦ n < 0)
  have hP : Set.InjOn Int.natAbs P := by
    intro a ha b hb heq
    exact (Int.natAbs_inj_of_nonneg_of_nonneg
      (Finset.mem_filter.mp ha).2.le (Finset.mem_filter.mp hb).2.le).mp heq
  have hN : Set.InjOn Int.natAbs N := by
    intro a ha b hb heq
    exact (Int.natAbs_inj_of_nonpos_of_nonpos
      (Finset.mem_filter.mp ha).2.le (Finset.mem_filter.mp hb).2.le).mp heq
  have hbound (T : Finset ℤ) (hT : T ⊆ S) (hinj : Set.InjOn Int.natAbs T) :
      (∑ n ∈ T, 1 / (d + Y * |(n : ℝ)|) ^ 2) ≤ 1 / (Y * d) := by
    have hpos : ∀ n ∈ T.image Int.natAbs, 0 < n := by
      intro n hn
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
      exact Int.natAbs_pos.mpr (hS m (hT hm))
    have hb := sum_positive_arithmetic_inverse_squares_le (T.image Int.natAbs) hpos hd hY
    rw [Finset.sum_image hinj] at hb
    have hcast (n : ℤ) : (n.natAbs : ℝ) = |(n : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    simpa only [hcast] using hb
  have hsplit : S = P ∪ N := by
    ext n
    simp only [P, N, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hn
      rcases lt_or_gt_of_ne (hS n hn) with h | h
      · exact Or.inr ⟨hn, h⟩
      · exact Or.inl ⟨hn, h⟩
    · rintro (h | h) <;> exact h.1
  have hdisj : Disjoint P N := by
    apply Finset.disjoint_left.mpr
    intro n hnP hnN
    exact (Finset.mem_filter.mp hnN).2.not_gt (Finset.mem_filter.mp hnP).2
  have hbP := hbound P (Finset.filter_subset _ _) hP
  have hbN := hbound N (Finset.filter_subset _ _) hN
  rw [hsplit, Finset.sum_union hdisj]
  exact (add_le_add hbP hbN).trans_eq (by ring)

end Erdos421
