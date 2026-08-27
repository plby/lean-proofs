import Mathlib.Probability.Distributions.SetBernoulli
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Checking the signed version of `lem:pseudobin`

Part (i) of the printed lemma assumes only `|Xᵢ| ≤ C`, not nonnegativity.
This module checks a finite counterexample to that signed formulation.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291.SignedConcentration

def half : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

abbrev Sample := Fin 400 → Prop

def coin : Measure Prop := bernoulliMeasure True False half

instance : IsProbabilityMeasure coin := by unfold coin; infer_instance

def probability : Measure Sample := Measure.infinitePi (fun _ => coin)

instance : IsProbabilityMeasure probability := by unfold probability; infer_instance

open Classical in
def value (b : Prop) : ℝ := if b then 28 / 25 else -(22 / 25)

def summand (i : Fin 400) (ω : Sample) : ℝ := value (ω i)

theorem variable_measurable (i : Fin 400) : Measurable (summand i) := by
  exact (Measurable.of_discrete : Measurable value).comp (measurable_pi_apply i)

theorem variables_independent : iIndepFun summand probability :=
  iIndepFun_infinitePi (X := fun _ => value) (fun _ => Measurable.of_discrete)

theorem variable_bound (i : Fin 400) (ω : Sample) : |summand i ω| ≤ 28 / 25 := by
  unfold summand value
  split_ifs <;> norm_num

theorem variable_integrable (i : Fin 400) : Integrable (summand i) probability := by
  have h := integrable_bernoulliMeasure True False half value
  have hm : MeasurePreserving (fun ω : Sample => ω i) probability coin :=
    ⟨measurable_pi_apply i, Measure.infinitePi_map_eval (fun _ => coin) i⟩
  change Integrable value coin at h
  rw [← hm.map_eq] at h
  exact (integrable_map_measure (Measurable.of_discrete.aestronglyMeasurable)
    (measurable_pi_apply i).aemeasurable).mp h

theorem variable_mean (i : Fin 400) : (∫ ω, summand i ω ∂probability) = 3 / 25 := by
  have hm : MeasurePreserving (fun ω : Sample => ω i) probability coin :=
    ⟨measurable_pi_apply i, Measure.infinitePi_map_eval (fun _ => coin) i⟩
  rw [show (∫ ω, summand i ω ∂probability) = ∫ b, value b ∂coin from by
    rw [← hm.map_eq, integral_map (measurable_pi_apply i).aemeasurable
      (Measurable.of_discrete.aestronglyMeasurable)]
    rfl]
  rw [coin, integral_bernoulliMeasure]
  norm_num [half, value]

theorem sum_mean : (∫ ω, ∑ i, summand i ω ∂probability) = 48 := by
  rw [integral_finsetSum _ (fun i _ => variable_integrable i)]
  simp [variable_mean]
  norm_num

private theorem sum_value_general {α : Type*} [Fintype α] (ω : α → Prop) :
    (∑ i, value (ω i)) =
      2 * ({i | ω i}.ncard : ℝ) - Fintype.card α * (22 / 25) := by
  classical
  have hi (i : α) :
      value (ω i) = 2 * (if ω i then (1 : ℝ) else 0) - 22 / 25 := by
    unfold value
    split_ifs <;> norm_num
  have hc : {i | ω i}.ncard = (Finset.univ.filter ω).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext i
    simp
  simp_rw [hi]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hs : (∑ i, if ω i then (1 : ℝ) else 0) =
      ((Finset.univ.filter ω).card : ℝ) := by
    simp
  rw [hs, hc]
  simp

theorem sum_value (ω : Sample) :
    (∑ i, summand i ω) = 2 * ({i | ω i}.ncard : ℝ) - 352 := by
  change (∑ i, value (ω i)) = _
  simpa only [Fintype.card_fin, Nat.cast_ofNat,
    show (400 : ℝ) * (22 / 25) = 352 by norm_num] using sum_value_general ω

theorem map_positive_set :
    probability.map (fun ω : Sample => {i | ω i}) =
      setBernoulli (Set.univ : Set (Fin 400)) half := by
  rw [setBernoulli_eq_map]
  simp only [Set.mem_univ, probability, coin, bernoulliMeasure_def]

theorem count_probability (k : ℕ) :
    probability.real {ω : Sample | {i | ω i}.ncard = k} =
      ((400 : ℕ).choose k : ℝ) * (1 / 2) ^ k * (1 / 2) ^ (400 - k) := by
  have hm : Measurable (fun ω : Sample => {i | ω i}) :=
    MeasurableEquiv.setOfPred.measurable
  have hc : Measurable (Set.ncard : Set (Fin 400) → ℕ) := by fun_prop
  have hmap : probability.map (fun ω : Sample => {i | ω i}.ncard) =
      (setBernoulli (Set.univ : Set (Fin 400)) half).map Set.ncard := by
    rw [← map_positive_set, Measure.map_map hc hm]
    rfl
  calc
    _ = (probability.map (fun ω : Sample => {i | ω i}.ncard)).real {k} := by
      have hm' : Measurable (fun ω : Sample => {i | ω i}.ncard) := hc.comp hm
      rw [map_measureReal_apply hm' (.singleton k)]
      rfl
    _ = _ := by
      rw [hmap, map_ncard_setBernoulli_real_singleton (Set.toFinite _) half k]
      norm_num [half, Set.ncard_univ, Nat.card_eq_fintype_card]

theorem count_probability_lower :
    (1 : ℝ) / 600 < probability.real {ω : Sample | {i | ω i}.ncard = 225} := by
  rw [count_probability]
  rw [← Nat.choose_symm (by omega : 225 ≤ 400)]
  norm_num only [Nat.reduceSub]
  rw [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial_eq_descFactorialBinary,
    Nat.factorial_eq_factorialBinarySplitting]
  norm_num [Nat.descFactorialBinary, Nat.factorialBinarySplitting, Nat.ascFactorialBinary]

theorem claimed_bound_lt : 2 * Real.exp (-(50 / 7)) < (1 : ℝ) / 600 := by
  have he : (271 / 100 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have hp : (271 / 100 : ℝ) ^ 7 < Real.exp 7 := by
    have h := pow_lt_pow_left₀ he (by norm_num : (0 : ℝ) ≤ 271 / 100) (by decide : 7 ≠ 0)
    simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one] using h
  have hr := Real.add_one_le_exp ((1 : ℝ) / 7)
  have hprod : (1200 : ℝ) < Real.exp (50 / 7) := by
    rw [show (50 / 7 : ℝ) = 7 + 1 / 7 by norm_num, Real.exp_add]
    have h := mul_le_mul_of_nonneg_left hr (Real.exp_pos 7).le
    nlinarith
  rw [Real.exp_neg]
  have hi : (Real.exp (50 / 7))⁻¹ < (1 : ℝ) / 1200 := by
    exact (inv_lt_comm₀ (Real.exp_pos _) (by norm_num)).mpr (by simpa using hprod)
  linarith

/-- The printed upper bound is strictly smaller than the probability of just
one outcome count within the deviation event. Here `μ=48`, `c=1`, `C=28/25`. -/
theorem signed_pseudobin_fails :
    2 * Real.exp (-(48 * 1 ^ 2 / (2 * (1 + 2 * 1) * (28 / 25)))) <
      probability.real {ω | |(∑ i, summand i ω) - 48| > 1 * 48} := by
  have hsub : {ω : Sample | {i | ω i}.ncard = 225} ⊆
      {ω | |(∑ i, summand i ω) - 48| > 1 * 48} := by
    intro ω hω
    change {i | ω i}.ncard = 225 at hω
    simp only [Set.mem_ofPred_eq, sum_value, hω]
    norm_num
  have h := claimed_bound_lt.trans (count_probability_lower.trans_le (measureReal_mono hsub))
  rw [show -(48 * 1 ^ 2 / (2 * (1 + 2 * 1) * (28 / 25))) = -(50 / 7 : ℝ) by norm_num]
  exact h

/-- A finite, measurable, integrable, independent family satisfying all of
the signed lemma's hypotheses, with positive parameters and `0 < c ≤ 1`,
but strictly violating its conclusion. -/
theorem signed_pseudobin_counterexample :
    ∃ (X : Fin 400 → Sample → ℝ) (C μ c : ℝ),
      0 < C ∧ 0 < μ ∧ 0 < c ∧ c ≤ 1 ∧
      (∀ i, Measurable (X i)) ∧ (∀ i, Integrable (X i) probability) ∧
      iIndepFun X probability ∧ (∀ i ω, |X i ω| ≤ C) ∧
      (∫ ω, ∑ i, X i ω ∂probability) = μ ∧
      2 * Real.exp (-(μ * c ^ 2 / (2 * (1 + 2 * c) * C))) <
        probability.real {ω | |(∑ i, X i ω) - μ| > c * μ} := by
  exact ⟨summand, 28 / 25, 48, 1, by norm_num, by norm_num, by norm_num, by norm_num,
    variable_measurable, variable_integrable, variables_independent, variable_bound,
    sum_mean, signed_pseudobin_fails⟩

end Arxiv2411_18291.SignedConcentration
