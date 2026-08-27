import ErdosProblems.Erdos4.FGKMTConditionalLaw

/-!
# Exact importance-weight moments

The inverse survival weights, their conditional moments, and the cap-tail
identity are finite-sum identities. They apply to the actual tilted law
without substituting an independent law on target vertices.
-/

open scoped BigOperators

namespace Erdos4.Tilted

open FGKMT

variable {Ω : Type*} [Fintype Ω]

theorem mean_indicator_const (ν : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E] (c : ℝ) :
    ν.mean (fun o => if E o then c else 0) = c * ν.prob E := by
  calc
    _ = ν.mean (fun o => c * (if E o then 1 else 0)) := by
      apply ν.mean_congr
      intro o
      by_cases h : E o <;> simp [h]
    _ = _ := by rw [FiniteLaw.mean_const_mul, ← FiniteLaw.prob_eq_mean]

noncomputable def eventWeight (ν : FiniteLaw Ω) (E : Ω → Prop) (o : Ω) : ℝ := by
  classical
  exact if E o then 1 / ν.prob E else 0

theorem eventWeight_nonneg (ν : FiniteLaw Ω) (E : Ω → Prop) (o : Ω) :
    0 ≤ eventWeight ν E o := by
  unfold eventWeight
  split_ifs
  · exact div_nonneg zero_le_one (ν.prob_nonneg E)
  · rfl

theorem mean_eventWeight (ν : FiniteLaw Ω) (E : Ω → Prop) (hE : ν.prob E ≠ 0) :
    ν.mean (eventWeight ν E) = 1 := by
  classical
  unfold eventWeight
  rw [mean_indicator_const, one_div_mul_cancel hE]

theorem mean_eventWeight_sq (ν : FiniteLaw Ω) (E : Ω → Prop) (hE : ν.prob E ≠ 0) :
    ν.mean (fun o => eventWeight ν E o ^ 2) = 1 / ν.prob E := by
  classical
  calc
    _ = ν.mean (fun o => if E o then (1 / ν.prob E) ^ 2 else 0) := by
      apply ν.mean_congr
      intro o
      by_cases h : E o <;> simp [eventWeight, h]
    _ = _ := by
      rw [mean_indicator_const]
      field_simp

theorem mean_eventWeight_mul (ν : FiniteLaw Ω) (E F : Ω → Prop) :
    ν.mean (fun o => eventWeight ν E o * eventWeight ν F o) =
      ν.prob (fun o => E o ∧ F o) / (ν.prob E * ν.prob F) := by
  classical
  calc
    _ = ν.mean (fun o => if E o ∧ F o then 1 / (ν.prob E * ν.prob F) else 0) := by
      apply ν.mean_congr
      intro o
      by_cases he : E o <;> by_cases hf : F o <;> simp [eventWeight, he, hf, mul_comm]
    _ = _ := by rw [mean_indicator_const ν (fun o => E o ∧ F o)]; ring

theorem condition_mean_eventWeight (ν : FiniteLaw Ω) (E R : Ω → Prop)
    [DecidablePred R] (o₀ : Ω) (hE : ν.prob E ≠ 0) (hR : ν.prob R ≠ 0)
    (hER : ∀ o, E o → R o) :
    (ν.condition R o₀).mean (eventWeight ν E) = 1 / ν.prob R := by
  classical
  rw [FiniteLaw.condition_mean _ _ _ hR]
  have heq : ν.mean (fun o => if R o then eventWeight ν E o else 0) =
      ν.mean (eventWeight ν E) := by
    apply ν.mean_congr
    intro o
    by_cases h : R o
    · simp [h]
    · have he : ¬E o := fun he => h (hER o he)
      simp [h, he, eventWeight]
  rw [heq, mean_eventWeight ν E hE]

theorem condition_mean_eventWeight_sq (ν : FiniteLaw Ω) (E R : Ω → Prop)
    [DecidablePred R] (o₀ : Ω) (hE : ν.prob E ≠ 0) (hR : ν.prob R ≠ 0)
    (hER : ∀ o, E o → R o) :
    (ν.prob R) ^ 2 * (ν.condition R o₀).mean (fun o => eventWeight ν E o ^ 2) =
      ν.prob R / ν.prob E := by
  classical
  rw [FiniteLaw.condition_mean _ _ _ hR]
  have heq : ν.mean (fun o => if R o then eventWeight ν E o ^ 2 else 0) =
      ν.mean (fun o => eventWeight ν E o ^ 2) := by
    apply ν.mean_congr
    intro o
    by_cases h : R o
    · simp [h]
    · have he : ¬E o := fun he => h (hER o he)
      simp [h, he, eventWeight]
  rw [heq, mean_eventWeight_sq ν E hE]
  field_simp

theorem condition_mean_eventWeight_mul (ν : FiniteLaw Ω) (E F R : Ω → Prop)
    [DecidablePred R] (o₀ : Ω) (hR : ν.prob R ≠ 0)
    (hER : ∀ o, E o → R o) :
    (ν.prob R) ^ 2 *
      (ν.condition R o₀).mean (fun o => eventWeight ν E o * eventWeight ν F o) =
      ν.prob R * ν.prob (fun o => E o ∧ F o) / (ν.prob E * ν.prob F) := by
  classical
  rw [FiniteLaw.condition_mean _ _ _ hR]
  have heq : ν.mean (fun o => if R o then eventWeight ν E o * eventWeight ν F o else 0) =
      ν.mean (fun o => eventWeight ν E o * eventWeight ν F o) := by
    apply ν.mean_congr
    intro o
    by_cases h : R o
    · simp [h]
    · have he : ¬E o := fun he => h (hER o he)
      simp [h, he, eventWeight]
  rw [heq, mean_eventWeight_mul]
  field_simp

open Classical in
theorem mean_eventWeight_on_event (ν : FiniteLaw Ω) (E F : Ω → Prop) :
    ν.mean (fun o => if F o then eventWeight ν E o else 0) =
      ν.prob (fun o => E o ∧ F o) / ν.prob E := by
  calc
    _ = ν.mean (fun o => if E o ∧ F o then 1 / ν.prob E else 0) := by
      apply ν.mean_congr
      intro o
      by_cases he : E o <;> by_cases hf : F o <;> simp [eventWeight, he, hf]
    _ = _ := by rw [mean_indicator_const ν (fun o => E o ∧ F o)]; ring

open Classical in
theorem cap_tail_pointwise (z : ℝ) :
    (if 2 < z then z else 0) ≤ 2 * (z - 1) ^ 2 := by
  split_ifs with h
  · nlinarith [mul_nonneg (show 0 ≤ 2 * z - 1 by linarith) (show 0 ≤ z - 2 by linarith)]
  · positivity

open Classical in
theorem cap_tail_mean_le (ν : FiniteLaw Ω) (Z : Ω → ℝ) :
    ν.mean (fun o => if 2 < Z o then Z o else 0) ≤
      2 * ν.mean (fun o => (Z o - 1) ^ 2) := by
  calc
    _ ≤ ν.mean (fun o => 2 * (Z o - 1) ^ 2) := ν.mean_mono (fun o => cap_tail_pointwise (Z o))
    _ = _ := ν.mean_const_mul _ _

variable {I : Type*} [Fintype I]

noncomputable def eventNormalizer (ν : FiniteLaw Ω) (μ : FiniteLaw I)
    (E : I → Ω → Prop) (o : Ω) : ℝ := μ.mean (fun i => eventWeight ν (E i) o)

theorem eventNormalizer_nonneg (ν : FiniteLaw Ω) (μ : FiniteLaw I)
    (E : I → Ω → Prop) (o : Ω) : 0 ≤ eventNormalizer ν μ E o :=
  μ.mean_nonneg (fun i => eventWeight_nonneg ν (E i) o)

theorem mean_eventNormalizer (ν : FiniteLaw Ω) (μ : FiniteLaw I)
    (E : I → Ω → Prop) (hE : ∀ i, ν.prob (E i) ≠ 0) :
    ν.mean (eventNormalizer ν μ E) = 1 := by
  unfold eventNormalizer FiniteLaw.mean
  simp only [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  calc
    _ = ∑ i : I, μ.weight i * ν.mean (eventWeight ν (E i)) := by
      apply Finset.sum_congr rfl
      intro i _
      unfold FiniteLaw.mean
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro o _
      ring
    _ = 1 := by simp only [mean_eventWeight ν _ (hE _), mul_one]; exact μ.total

open Classical in
/-- The exact cap-tail identity (5.30), allowing arbitrary deterministic label weights. -/
theorem eventNormalizer_cap_identity (ν : FiniteLaw Ω) (μ : FiniteLaw I)
    (E : I → Ω → Prop) (o₀ : Ω) (hE : ∀ i, ν.prob (E i) ≠ 0) :
    μ.mean (fun i => (ν.condition (E i) o₀).prob (fun o => 2 < eventNormalizer ν μ E o)) =
      ν.mean (fun o => if 2 < eventNormalizer ν μ E o then eventNormalizer ν μ E o else 0) := by
  let F := fun o => 2 < eventNormalizer ν μ E o
  have hcond (i : I) : (ν.condition (E i) o₀).prob F =
      ν.mean (fun o => if F o then eventWeight ν (E i) o else 0) := by
    rw [FiniteLaw.condition_prob _ _ _ _ (hE i), mean_eventWeight_on_event]
  change μ.mean (fun i => (ν.condition (E i) o₀).prob F) = _
  simp_rw [hcond]
  unfold FiniteLaw.mean
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  change (∑ i : I, μ.weight i * (ν.weight o * (if F o then eventWeight ν (E i) o else 0))) =
    ν.weight o * (if F o then eventNormalizer ν μ E o else 0)
  by_cases h : F o
  · simp only [if_pos h, eventNormalizer, FiniteLaw.mean, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · simp [h]

open Classical in
theorem eventNormalizer_cap_le (ν : FiniteLaw Ω) (μ : FiniteLaw I)
    (E : I → Ω → Prop) (o₀ : Ω) (hE : ∀ i, ν.prob (E i) ≠ 0) :
    μ.mean (fun i => (ν.condition (E i) o₀).prob (fun o => 2 < eventNormalizer ν μ E o)) ≤
      2 * ν.mean (fun o => (eventNormalizer ν μ E o - 1) ^ 2) := by
  rw [eventNormalizer_cap_identity ν μ E o₀ hE]
  exact cap_tail_mean_le ν _

end Erdos4.Tilted
