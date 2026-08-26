import ErdosProblems.Erdos1148.OrderedNatRuns
import ErdosProblems.Erdos1148.CuspRunGeometry

/-! # Ordered long runs retain all visit time except one unit per run -/

namespace Erdos1148.DukeArithmetic

theorem sum_real_long_nat_run_duration (V : Finset ℕ) :
    (∑ p ∈ (maximalNatRuns V).filter (fun p => p.1 < p.2), ((p.2 : ℝ) - p.1)) =
      (V.card : ℝ) - (maximalNatRuns V).card := by
  have hcast : (∑ p ∈ (maximalNatRuns V).filter (fun p => p.1 < p.2),
      ((p.2 - p.1 : ℕ) : ℝ)) + ((maximalNatRuns V).card : ℝ) = (V.card : ℝ) := by
    exact_mod_cast sum_long_maximalNatRuns_duration V
  have heq : (∑ p ∈ (maximalNatRuns V).filter (fun p => p.1 < p.2), ((p.2 : ℝ) - p.1)) =
      ∑ p ∈ (maximalNatRuns V).filter (fun p => p.1 < p.2), ((p.2 - p.1 : ℕ) : ℝ) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [Nat.cast_sub (Finset.mem_filter.mp hp).2.le]
  rw [heq]
  linarith

theorem exists_ordered_long_nat_runs (V : Finset ℕ) :
    ∃ l : List (ℕ × ℕ),
      l.toFinset = (maximalNatRuns V).filter (fun p => p.1 < p.2) ∧ l.Nodup ∧
      l.Pairwise (fun p q => p.2 < q.1) ∧ l.length ≤ (maximalNatRuns V).card ∧
      (l.map (fun p => (p.2 : ℝ) - p.1)).sum = (V.card : ℝ) - (maximalNatRuns V).card := by
  classical
  obtain ⟨l, hfin, hnodup, hpair⟩ := exists_ordered_maximalNatRuns V
  let l' := l.filter (fun p => p.1 < p.2)
  have hfin' : l'.toFinset = (maximalNatRuns V).filter (fun p => p.1 < p.2) := by
    rw [← hfin, List.filter_toFinset]
  have hnodup' : l'.Nodup := hnodup.filter _
  refine ⟨l', hfin', hnodup', hpair.filter _, ?_, ?_⟩
  · have hlen : l.length = (maximalNatRuns V).card := by
      rw [← hfin, List.toFinset_card_of_nodup hnodup]
    exact (List.length_filter_le _ l).trans hlen.le
  · rw [← List.sum_toFinset _ hnodup', hfin']
    exact sum_real_long_nat_run_duration V

end Erdos1148.DukeArithmetic
