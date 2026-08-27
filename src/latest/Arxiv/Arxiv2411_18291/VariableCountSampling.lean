import Arxiv.Arxiv2411_18291.FiniteCountSampling

/-! # Simultaneous concentration with different test means -/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291.IndependentBernoulliChoice

theorem exists_subset_with_variable_concentrated_counts {I T : Type*} [DecidableEq I]
    (D : Finset I) (tests : Finset T) (s : T → Finset I)
    (hsub : ∀ t ∈ tests, s t ⊆ D) (p : I → unitInterval) (μ : T → ℝ)
    {c μ₀ : ℝ} (hc : 0 ≤ c)
    (hmean : ∀ t ∈ tests, (∑ i ∈ s t, (p i : ℝ)) = μ t)
    (hlower : ∀ t ∈ tests, μ₀ ≤ μ t)
    (hsmall : tests.card * (2 * Real.exp (-(μ₀ * c ^ 2 / (2 * (1 + 2 * c))))) < 1) :
    ∃ H : Finset I, H ⊆ D ∧ ∀ t ∈ tests,
      |((H ∩ s t).card : ℝ) - μ t| ≤ c * μ t := by
  classical
  let bad (t : T) := {ω : Sample I | c * μ t < |(∑ i ∈ s t, present i ω) - μ t|}
  have hsingle (t : T) (ht : t ∈ tests) : (probability p).real (bad t) ≤
      2 * Real.exp (-(μ₀ * c ^ 2 / (2 * (1 + 2 * c)))) := by
    have htail : (probability p).real (bad t) ≤
        2 * Real.exp (-(μ t * c ^ 2 / (2 * (1 + 2 * c)))) := by
      simpa only [mul_one] using pseudobin_part_one_nonneg (s t)
        (by norm_num : (0 : ℝ) < 1) hc present_measurable (present_independent p)
        (fun i _ => ae_of_all _ fun ω => present_bounds i ω)
        ((count_mean p (s t)).trans (hmean t ht))
    apply htail.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hlower t ht) (sq_nonneg c)) (by positivity)
  have hprob : (probability p).real (⋃ t ∈ tests, bad t) ≤
      tests.card * (2 * Real.exp (-(μ₀ * c ^ 2 / (2 * (1 + 2 * c))))) := by
    calc
      _ ≤ ∑ t ∈ tests, (probability p).real (bad t) := measureReal_biUnion_finset_le tests _
      _ ≤ ∑ _t ∈ tests, 2 * Real.exp (-(μ₀ * c ^ 2 / (2 * (1 + 2 * c)))) :=
        sum_le_sum hsingle
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  have hex : ∃ ω : Sample I, ∀ t ∈ tests,
      |(∑ i ∈ s t, present i ω) - μ t| ≤ c * μ t := by
    by_contra h
    push Not at h
    have hall : (⋃ t ∈ tests, bad t) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro ω
      obtain ⟨t, ht, hω⟩ := h ω
      exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨ht, hω⟩⟩
    rw [hall, probReal_univ] at hprob
    linarith only [hprob, hsmall]
  obtain ⟨ω, hω⟩ := hex
  refine ⟨D.filter (fun i => ω i), filter_subset _ _, ?_⟩
  intro t ht
  have heq : D.filter (fun i => ω i) ∩ s t = (s t).filter fun i => ω i := by
    ext i
    simp only [mem_inter, mem_filter]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hsub t ht h.1, h.2⟩, h.1⟩⟩
  rw [heq, ← count_eq_card_filter]
  exact hω t ht

end Arxiv2411_18291.IndependentBernoulliChoice
