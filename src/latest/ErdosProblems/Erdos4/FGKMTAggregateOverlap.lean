import ErdosProblems.Erdos4.FGKMTUnionError

/-! Pair-codegree control of the aggregate raw-hit overcount. -/

open scoped BigOperators

namespace Erdos4.FGKMT

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]

theorem aggregate_distinct_pair_le (μ : I → FiniteLaw (Finset V)) (p : V → ℝ)
    {κ δ : ℝ} {r : ℕ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ)
    (hp : ∀ v, κ ≤ p v) (hsize : ∀ i e, 0 < (μ i).weight e → e.card ≤ r)
    (hpair : ∀ v w, v ≠ w → pairDegree μ v w ≤ δ) (W : Finset V) (v w : V) :
    (∑ i, eventNumerator (μ i) p W (fun e => v ≠ w ∧ v ∈ e ∧ w ∈ e)) ≤ δ / κ ^ r := by
  classical
  calc
    _ ≤ (∑ i, (μ i).prob (fun e => v ≠ w ∧ v ∈ e ∧ w ∈ e)) / κ ^ r := by
      rw [Finset.sum_div]
      exact Finset.sum_le_sum (fun i _hi => eventNumerator_le (μ i) p hκ0 hκ1 hp (hsize i) W _)
    _ ≤ δ / κ ^ r := by
      apply div_le_div_of_nonneg_right _ (pow_pos hκ0 r).le
      by_cases hvw : v = w
      · simp only [hvw, ne_eq, not_true_eq_false, false_and, FiniteLaw.prob, if_false,
          Finset.sum_const_zero]
        exact hδ
      · have heq : (∑ i, (μ i).prob (fun e => v ≠ w ∧ v ∈ e ∧ w ∈ e)) = pairDegree μ v w := by
          unfold pairDegree
          apply Finset.sum_congr rfl
          intro i _hi
          apply le_antisymm
          · exact (μ i).prob_mono (fun e he => he.2)
          · exact (μ i).prob_mono (fun e he => ⟨hvw, he⟩)
        rw [heq]
        exact hpair v w hvw

theorem aggregate_raw_union_error (μ : I → FiniteLaw (Finset V)) (p : V → ℝ)
    {κ δ : ℝ} {r : ℕ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ)
    (hp : ∀ v, κ ≤ p v) (hsize : ∀ i e, 0 < (μ i).weight e → e.card ≤ r)
    (hpair : ∀ v w, v ≠ w → pairDegree μ v w ≤ δ) (W T : Finset V) :
    |(∑ v ∈ T, rawDegree μ p W v) -
      ∑ i, eventNumerator (μ i) p W (fun e => ¬Disjoint T e)| ≤
        (T.card : ℝ) ^ 2 * δ / κ ^ r := by
  classical
  have hp0 : ∀ v, 0 < p v := fun v => hκ0.trans_le (hp v)
  have heq : (∑ v ∈ T, rawDegree μ p W v) -
      ∑ i, eventNumerator (μ i) p W (fun e => ¬Disjoint T e) =
      ∑ i, ((∑ v ∈ T, eventNumerator (μ i) p W (fun e => v ∈ e)) -
        eventNumerator (μ i) p W (fun e => ¬Disjoint T e)) := by
    unfold rawDegree
    rw [Finset.sum_sub_distrib, Finset.sum_comm]
  have hn : 0 ≤ ∑ i, ((∑ v ∈ T, eventNumerator (μ i) p W (fun e => v ∈ e)) -
      eventNumerator (μ i) p W (fun e => ¬Disjoint T e)) :=
    Finset.sum_nonneg (fun i _hi => (eventNumerator_union_error (μ i) p hp0 W T).1)
  rw [heq, abs_of_nonneg hn]
  calc
    _ ≤ ∑ i, ∑ v ∈ T, ∑ w ∈ T,
        eventNumerator (μ i) p W (fun e => v ≠ w ∧ v ∈ e ∧ w ∈ e) :=
      Finset.sum_le_sum (fun i _hi => (eventNumerator_union_error (μ i) p hp0 W T).2)
    _ = ∑ v ∈ T, ∑ w ∈ T, ∑ i,
        eventNumerator (μ i) p W (fun e => v ≠ w ∧ v ∈ e ∧ w ∈ e) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _hv
      exact Finset.sum_comm
    _ ≤ ∑ _v ∈ T, ∑ _w ∈ T, δ / κ ^ r := by
      apply Finset.sum_le_sum
      intro v _hv
      apply Finset.sum_le_sum
      intro w _hw
      exact aggregate_distinct_pair_le μ p hκ0 hκ1 hδ hp hsize hpair W v w
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

end Erdos4.FGKMT
