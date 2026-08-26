/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceSaturatedPacking
import ErdosProblems.Erdos547b.SourceParameterSchedule

/-!
# Absolute bad-edge cost for several simultaneously served source families

A global bad-edge count need not be proportional to a smaller family's
unused size. Charge an explicit absolute loss in each family instead.
The source hierarchy pays for that global loss without changing parameters.
-/

open scoped BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceAbsoluteBadBudget

open Finset Erdos547b.ZhaoSourceSaturatedPacking Erdos547b.ZhaoSourceParameterSchedule

theorem source_aggregation_margin {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    4 * rootTypicality α + 4 * epsilon α < gamma α := by
  have hg := (parameter_pos hα).2.2.2.2.2.2.1
  have hupper := parameter_upper_bounds hα hα1
  have hd1 := (reservoir_cleanup_bounds hα hα1).2.2.2.2.2
  have hg1 : gamma α ≤ 1 := by linarith only [hupper.2.2.2.2.2.1, hd1]
  have hδg : rootTypicality α ≤ gamma α / 1000 :=
    div_le_div_of_nonneg_right (pow_succ_le_self hg.le hg1 5) (by norm_num)
  linarith only [hδg, hupper.2.2.2.2.2.2, hg]

variable {Bin Item : Type*} [DecidableEq Bin]

/-- The reserved-mass ledger and an absolute bad-set cost suffice for
each family's residual demand, with no incorrect local fraction estimate. -/
theorem residual_capacity_of_absolute_bad_cost
    (all used bad : Finset Bin) (capacity : Bin → ℝ) (slack loss demand consumed : ℝ)
    (hused : used ⊆ all) (hbad : bad ⊆ all \ used)
    (hbadCost : (∑ e ∈ bad, (capacity e - slack)) ≤ loss)
    (hledger : (∑ e ∈ used, (capacity e - slack)) ≤ consumed)
    (hbudget : demand + consumed ≤ (∑ e ∈ all, (capacity e - slack)) - loss) :
    demand ≤ ∑ e ∈ (all \ used) \ bad, (capacity e - slack) := by
  have hsplit := Finset.sum_sdiff hused (f := fun e => capacity e - slack)
  have hsplitBad := Finset.sum_sdiff hbad (f := fun e => capacity e - slack)
  linarith only [hbadCost, hledger, hbudget, hsplit, hsplitBad]

omit [DecidableEq Bin] in
theorem bad_effective_cost_le_absolute
    (bad : Finset Bin) (capacity : Bin → ℝ) (slack δ N : ℝ) (globalCount : ℕ)
    (hslack : 0 ≤ slack) (hN : 0 ≤ N)
    (hcount : (bad.card : ℝ) ≤ 2 * δ * globalCount)
    (hcap : ∀ e ∈ bad, capacity e ≤ 2 * N) :
    (∑ e ∈ bad, (capacity e - slack)) ≤ 4 * δ * N * globalCount := by
  have hsum : (∑ e ∈ bad, (capacity e - slack)) ≤ (bad.card : ℝ) * (2 * N) := by
    calc
      _ ≤ ∑ _e ∈ bad, 2 * N := by
        apply Finset.sum_le_sum
        intro e he
        linarith only [hcap e he, hslack]
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hm := mul_le_mul_of_nonneg_right hcount (by positivity : 0 ≤ 2 * N)
  nlinarith only [hsum, hm]

/-- Actual ordered saturation after charging the global bad-edge allowance
to this family's sufficient budget. This is purely finite allocation. -/
theorem exists_residualPacking_absolute
    (all used bad : Finset Bin) (items : List Item)
    (weight : Item → ℝ) (capacity : Bin → ℝ) (slack δ N consumed : ℝ) (globalCount : ℕ)
    (hused : used ⊆ all) (hbad : bad ⊆ all \ used)
    (hcount : (bad.card : ℝ) ≤ 2 * δ * globalCount)
    (hslack : 0 ≤ slack) (hN : 0 ≤ N)
    (hcap : ∀ e ∈ all \ used, capacity e ≤ 2 * N)
    (hledger : (∑ e ∈ used, (capacity e - slack)) ≤ consumed)
    (hsmall : ∀ i ∈ items, 0 < weight i ∧ weight i ≤ slack)
    (hbudget : mass weight items + consumed ≤
      (∑ e ∈ all, capacity e) - slack * all.card - 4 * δ * N * globalCount) :
    Nonempty (SaturatedPacking (((all \ used) \ bad).filter (fun e => slack < capacity e)).toList
      items weight capacity slack) := by
  have hcost := bad_effective_cost_le_absolute bad capacity slack δ N globalCount hslack hN hcount
    (fun e he => hcap e (hbad he))
  have hbudget' : mass weight items + consumed ≤
      (∑ e ∈ all, (capacity e - slack)) - 4 * δ * N * globalCount := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_comm (all.card : ℝ)]
    exact hbudget
  have hremaining := residual_capacity_of_absolute_bad_cost all used bad capacity slack
    (4 * δ * N * globalCount) (mass weight items) consumed hused hbad hcost hledger hbudget'
  have hgood := hremaining.trans (sum_le_positive_capacity_bins ((all \ used) \ bad) capacity slack)
  apply exists_saturatedPacking _ items weight capacity slack (Finset.nodup_toList _) hslack
  · intro e he
    exact (Finset.mem_filter.mp (Finset.mem_toList.mp he)).2
  · exact hsmall
  · rw [← List.sum_toFinset (fun e => capacity e - slack) (Finset.nodup_toList _)]
    simpa using hgood

end Erdos547b.ZhaoSourceAbsoluteBadBudget

#print axioms Erdos547b.ZhaoSourceAbsoluteBadBudget.source_aggregation_margin
#print axioms Erdos547b.ZhaoSourceAbsoluteBadBudget.residual_capacity_of_absolute_bad_cost
#print axioms Erdos547b.ZhaoSourceAbsoluteBadBudget.bad_effective_cost_le_absolute
#print axioms Erdos547b.ZhaoSourceAbsoluteBadBudget.exists_residualPacking_absolute
