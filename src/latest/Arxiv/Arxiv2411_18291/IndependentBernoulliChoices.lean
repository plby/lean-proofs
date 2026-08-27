import Arxiv.Arxiv2411_18291.BernoulliSubset

/-!
# Independent Bernoulli choices with different probabilities

Each coordinate has its own prescribed probability. The product measure
gives independent indicators, their exact means, and concentration of every
finite count. The indicators satisfy the corrected nonnegativity hypothesis.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

namespace Arxiv2411_18291.IndependentBernoulliChoice

variable {I : Type*}

abbrev Sample (I : Type*) := I → Prop

def probability (p : I → unitInterval) : Measure (Sample I) :=
  Measure.infinitePi fun i => BernoulliSubset.coin (p i)

instance (p : I → unitInterval) : IsProbabilityMeasure (probability p) := by
  unfold probability
  infer_instance

def present (i : I) : Sample I → ℝ := {ω : Sample I | ω i}.indicator fun _ => 1

theorem coordinate_event_measurable (i : I) : MeasurableSet {ω : Sample I | ω i} := by
  have h : {ω : Sample I | ω i} = (fun ω => ω i) ⁻¹' {True} := by ext ω; simp
  rw [h]
  exact (measurable_pi_apply i) (.singleton True)

theorem present_measurable (i : I) : Measurable (present i) :=
  measurable_const.indicator (coordinate_event_measurable i)

theorem present_bounds (i : I) (ω : Sample I) : 0 ≤ present i ω ∧ present i ω ≤ 1 := by
  classical
  simp only [present, Set.indicator]
  split_ifs <;> norm_num

theorem present_integrable (p : I → unitInterval) (i : I) :
    Integrable (present i) (probability p) :=
  (integrable_const 1).indicator (coordinate_event_measurable i)

theorem present_mean (p : I → unitInterval) (i : I) :
    (∫ ω, present i ω ∂probability p) = p i := by
  have hmap : (probability p).map (fun ω => ω i) = BernoulliSubset.coin (p i) :=
    Measure.infinitePi_map_eval (fun j => BernoulliSubset.coin (p j)) i
  have hset : {ω : Sample I | ω i} = (fun ω => ω i) ⁻¹' {True} := by ext ω; simp
  rw [present, integral_indicator_const _ (coordinate_event_measurable i), hset,
    smul_eq_mul, mul_one]
  change (probability p ((fun ω : Sample I => ω i) ⁻¹' {True})).toReal = (p i : ℝ)
  rw [← Measure.map_apply (measurable_pi_apply i) (.singleton True), hmap]
  simp [BernoulliSubset.coin]

theorem present_independent (p : I → unitInterval) : iIndepFun present (probability p) := by
  classical
  have h : iIndepFun (fun i (ω : Sample I) => if ω i then (1 : ℝ) else 0) (probability p) :=
    iIndepFun_infinitePi (X := fun _ (b : Prop) => if b then (1 : ℝ) else 0)
      (fun _ => measurable_of_countable _)
  have heq : (fun i (ω : Sample I) => if ω i then (1 : ℝ) else 0) = present := by
    funext i ω
    simp only [present, Set.indicator, Set.mem_ofPred_eq]
  rwa [heq] at h

open Classical in
theorem count_eq_card_filter (s : Finset I) (ω : Sample I) :
    (∑ i ∈ s, present i ω) = ((s.filter fun i => ω i).card : ℝ) := by
  classical
  simp only [present, Set.indicator, Set.mem_ofPred_eq, card_eq_sum_ones, sum_filter,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem count_mean (p : I → unitInterval) (s : Finset I) :
    (∫ ω, ∑ i ∈ s, present i ω ∂probability p) = ∑ i ∈ s, (p i : ℝ) := by
  rw [integral_finsetSum s (fun i _ => present_integrable p i)]
  simp only [present_mean]

end Arxiv2411_18291.IndependentBernoulliChoice
