import ErdosProblems.Erdos4.TiltedSieve
import ErdosProblems.Erdos4.FGKMTExpectationExtraction

/-! Independent finite choices admit a legal deterministic cover with the exponential miss bound. -/

open scoped BigOperators

namespace Erdos4.Tilted

open FGKMT

noncomputable def dependentLaw {I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} [∀ i, Fintype (A i)] (μ : ∀ i, FiniteLaw (A i)) : FiniteLaw (∀ i, A i) where
  weight choice := ∏ i, (μ i).weight (choice i)
  nonneg choice := Finset.prod_nonneg (fun i _ => (μ i).nonneg (choice i))
  total := Erdos4.assignmentWeight_sum _ (fun i => (μ i).total)

theorem dependentLaw_prob_all {I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} [∀ i, Fintype (A i)] (μ : ∀ i, FiniteLaw (A i))
    (E : ∀ i, A i → Prop) :
    (dependentLaw μ).prob (fun choice => ∀ i, E i (choice i)) = ∏ i, (μ i).prob (E i) := by
  classical
  have hh := Erdos4.independent_assignment_miss_mass
    (fun i a => (μ i).weight a) (fun i a => E i a)
  convert hh using 1
  · unfold FiniteLaw.prob dependentLaw
    apply Finset.sum_congr rfl
    intro choice _
    by_cases h : ∀ i, E i (choice i) <;> simp [h]
  · rfl

theorem dependentLaw_support {I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} [∀ i, Fintype (A i)] (μ : ∀ i, FiniteLaw (A i))
    (choice : ∀ i, A i) (hchoice : 0 < (dependentLaw μ).weight choice) :
    ∀ i, 0 < (μ i).weight (choice i) := by
  intro i
  by_contra hnot
  have hz : (μ i).weight (choice i) = 0 := le_antisymm (le_of_not_gt hnot) ((μ i).nonneg _)
  have hh : (dependentLaw μ).weight choice = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hz
  linarith

theorem exists_independent_cover {I V : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]
    {A : I → Type*} [∀ i, Fintype (A i)] (μ : ∀ i, FiniteLaw (A i))
    (edge : ∀ i, A i → Finset V) (vertices : Finset V) :
    ∃ choice : ∀ i, A i,
      (∀ i, 0 < (μ i).weight (choice i)) ∧
      (((vertices.filter (fun v => ∀ i, v ∉ edge i (choice i))).card : ℝ)) ≤
        ∑ v ∈ vertices, Real.exp (-(∑ i, (μ i).prob (fun a => v ∈ edge i a))) := by
  classical
  let law := dependentLaw μ
  let cost := fun (choice : ∀ i, A i) => ((vertices.filter (fun v => ∀ i, v ∉ edge i (choice i))).card : ℝ)
  have hmean : law.mean cost ≤
      ∑ v ∈ vertices, Real.exp (-(∑ i, (μ i).prob (fun a => v ∈ edge i a))) := by
    have hcost : cost = (fun choice => ∑ v ∈ vertices, if (∀ i, v ∉ edge i (choice i)) then (1 : ℝ) else 0) := by
      funext choice
      simp only [cost, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [hcost, FiniteLaw.mean_finset_sum]
    apply Finset.sum_le_sum
    intro v hv
    rw [← FiniteLaw.prob_eq_mean]
    change (dependentLaw μ).prob (fun choice => ∀ i, v ∉ edge i (choice i)) ≤ _
    rw [dependentLaw_prob_all μ (fun i a => v ∉ edge i a)]
    simp only [FiniteLaw.prob_compl]
    exact Erdos4.prod_one_sub_le_exp_neg_sum Finset.univ
      (fun i => (μ i).prob (fun a => v ∈ edge i a))
      (fun i _ => (μ i).prob_le_one _)
  obtain ⟨choice, hpos, hcost⟩ := law.exists_support_le_mean cost
  exact ⟨choice, dependentLaw_support μ choice hpos, hcost.trans hmean⟩

end Erdos4.Tilted
