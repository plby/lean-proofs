import ErdosProblems.Erdos4.FGKMTRawDegree

/-! The error in replacing a union of hits by their sum is charged to pairs. -/

open scoped BigOperators

namespace Erdos4.FGKMT

theorem indicator_union_error {J : Type*} [DecidableEq J]
    (s : Finset J) (E : J → Prop) [DecidablePred E] :
    0 ≤ (∑ j ∈ s, if E j then (1 : ℝ) else 0) - (if ∃ j ∈ s, E j then 1 else 0) ∧
    (∑ j ∈ s, if E j then (1 : ℝ) else 0) - (if ∃ j ∈ s, E j then 1 else 0) ≤
      ∑ j ∈ s, ∑ k ∈ s, if j ≠ k ∧ E j ∧ E k then 1 else 0 := by
  classical
  by_cases hE : ∃ j ∈ s, E j
  · rw [if_pos hE]
    obtain ⟨j₀, hj₀, hEj₀⟩ := hE
    have hlow : (1 : ℝ) ≤ ∑ j ∈ s, if E j then 1 else 0 := by
      have hh := Finset.single_le_sum (s := s) (f := fun j => if E j then (1 : ℝ) else 0)
        (fun j _hj => by split_ifs <;> norm_num) hj₀
      simpa only [if_pos hEj₀] using hh
    have hpoint (j : J) : (if E j then (1 : ℝ) else 0) ≤
        (if j = j₀ then 1 else 0) + ∑ k ∈ s, if j ≠ k ∧ E j ∧ E k then 1 else 0 := by
      have hn : (0 : ℝ) ≤ ∑ k ∈ s, if j ≠ k ∧ E j ∧ E k then 1 else 0 :=
        Finset.sum_nonneg (fun k _hk => by split_ifs <;> norm_num)
      by_cases heq : j = j₀
      · subst j
        rw [if_pos hEj₀, if_pos (rfl : j₀ = j₀)]
        exact le_add_of_nonneg_right hn
      · rw [if_neg heq, zero_add]
        by_cases hej : E j
        · rw [if_pos hej]
          have hh := Finset.single_le_sum (s := s)
            (f := fun k => if j ≠ k ∧ E j ∧ E k then (1 : ℝ) else 0)
            (fun k _hk => by split_ifs <;> norm_num) hj₀
          have hpair : j ≠ j₀ ∧ E j ∧ E j₀ := ⟨heq, hej, hEj₀⟩
          rw [if_pos hpair] at hh
          exact hh
        · rw [if_neg hej]
          exact hn
    have hupper := Finset.sum_le_sum (s := s) (fun j _hj => hpoint j)
    rw [Finset.sum_add_distrib] at hupper
    have hone : (∑ j ∈ s, if j = j₀ then (1 : ℝ) else 0) = 1 := by simp [hj₀]
    rw [hone] at hupper
    exact ⟨by linarith, by linarith⟩
  · have hnone : ∀ j ∈ s, ¬E j := fun j hj hej => hE ⟨j, hj, hej⟩
    have hsum : (∑ j ∈ s, if E j then (1 : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      exact if_neg (hnone j hj)
    rw [if_neg hE, hsum, sub_self]
    exact ⟨le_rfl, Finset.sum_nonneg (fun j _hj =>
      Finset.sum_nonneg (fun k _hk => by split_ifs <;> norm_num))⟩

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem eventNumerator_indicator (μ : FiniteLaw (Finset V)) (p : V → ℝ)
    (W : Finset V) (E : Finset V → Prop) [DecidablePred E] :
    eventNumerator μ p W E =
      ∑ e, reweighted μ p W e * (if E e then (1 : ℝ) else 0) := by
  unfold eventNumerator
  apply Finset.sum_congr rfl
  intro e _he
  by_cases he : E e <;> simp [he]

theorem eventNumerator_sum {J : Type*} (s : Finset J) (μ : FiniteLaw (Finset V))
    (p : V → ℝ) (W : Finset V) (E : J → Finset V → Prop)
    [∀ j, DecidablePred (E j)] :
    (∑ j ∈ s, eventNumerator μ p W (E j)) =
      ∑ e, reweighted μ p W e * ∑ j ∈ s, if E j e then (1 : ℝ) else 0 := by
  simp only [eventNumerator_indicator, Finset.mul_sum]
  exact Finset.sum_comm

theorem eventNumerator_union_error (μ : FiniteLaw (Finset V)) (p : V → ℝ)
    (hp : ∀ v, 0 < p v) (W T : Finset V) :
    0 ≤ (∑ v ∈ T, eventNumerator μ p W (fun e => v ∈ e)) -
        eventNumerator μ p W (fun e => ¬Disjoint T e) ∧
    (∑ v ∈ T, eventNumerator μ p W (fun e => v ∈ e)) -
        eventNumerator μ p W (fun e => ¬Disjoint T e) ≤
      ∑ v ∈ T, ∑ w ∈ T, eventNumerator μ p W (fun e => v ≠ w ∧ v ∈ e ∧ w ∈ e) := by
  classical
  have hdiff : (∑ v ∈ T, eventNumerator μ p W (fun e => v ∈ e)) -
      eventNumerator μ p W (fun e => ¬Disjoint T e) =
      ∑ e, reweighted μ p W e *
        ((∑ v ∈ T, if v ∈ e then (1 : ℝ) else 0) - if ∃ v ∈ T, v ∈ e then 1 else 0) := by
    rw [eventNumerator_sum, eventNumerator_indicator, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _he
    by_cases hex : ∃ v ∈ T, v ∈ e
    · rw [if_pos hex, if_pos (Finset.not_disjoint_iff.mpr hex)]
      ring
    · have hd : ¬¬Disjoint T e := fun h => hex (Finset.not_disjoint_iff.mp h)
      rw [if_neg hex, if_neg hd]
      ring
  have hpairs : (∑ v ∈ T, ∑ w ∈ T,
      eventNumerator μ p W (fun e => v ≠ w ∧ v ∈ e ∧ w ∈ e)) =
      ∑ e, reweighted μ p W e *
        ∑ v ∈ T, ∑ w ∈ T, if v ≠ w ∧ v ∈ e ∧ w ∈ e then (1 : ℝ) else 0 := by
    simp only [eventNumerator_indicator, Finset.mul_sum]
    calc
      _ = ∑ v ∈ T, ∑ e : Finset V, ∑ w ∈ T,
          reweighted μ p W e * (if v ≠ w ∧ v ∈ e ∧ w ∈ e then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro v _hv
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hdiff, hpairs]
  exact ⟨Finset.sum_nonneg (fun e _he => mul_nonneg (reweighted_nonneg μ p hp W e)
      (indicator_union_error T (fun v => v ∈ e)).1),
    Finset.sum_le_sum (fun e _he => mul_le_mul_of_nonneg_left
      (indicator_union_error T (fun v => v ∈ e)).2 (reweighted_nonneg μ p hp W e))⟩

end Erdos4.FGKMT
