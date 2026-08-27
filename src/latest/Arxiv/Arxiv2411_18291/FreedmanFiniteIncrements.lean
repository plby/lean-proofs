import Arxiv.Arxiv2411_18291.FreedmanConditionalVariance

/-! # Freedman's bound for a finite list of adapted increments -/

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ}
variable {a b v : ℝ} {n : ℕ}

theorem freedman_finite_conditionalVariance_bound (ha : 0 < a) (hb : 0 < b) (hv : 0 ≤ v)
    (hX : ∀ i < n, StronglyMeasurable[ℱ (i + 1)] (X i))
    (hXb : ∀ i < n, ∀ᵐ ω ∂P, |X i ω| ≤ b)
    (hmean : ∀ i < n, P[X i | ℱ i] ≤ᵐ[P] 0) :
    P.real {ω | ∃ j ≤ n, a ≤ ∑ i ∈ range j, X i ω ∧
      (∑ i ∈ range j, Var[X i; P | ℱ i] ω) ≤ v} ≤
      Real.exp (-(a ^ 2 / (2 * (v + a * b)))) := by
  let Y := fun i => if i < n then X i else (0 : Ω → ℝ)
  have hYeq : ∀ i < n, Y i = X i := fun i hi => if_pos hi
  have hY : ∀ i, StronglyMeasurable[ℱ (i + 1)] (Y i) := by
    intro i
    by_cases hi : i < n
    · simpa only [Y, if_pos hi] using hX i hi
    · simpa only [Y, if_neg hi] using (stronglyMeasurable_zero :
        StronglyMeasurable[ℱ (i + 1)] (0 : Ω → ℝ))
  have hYb : ∀ i, ∀ᵐ ω ∂P, |Y i ω| ≤ b := by
    intro i
    by_cases hi : i < n
    · simpa only [Y, if_pos hi] using hXb i hi
    · exact ae_of_all _ fun _ => by simp [Y, hi, hb.le]
  have hYmean : ∀ i, P[Y i | ℱ i] ≤ᵐ[P] 0 := by
    intro i
    by_cases hi : i < n
    · simpa only [Y, if_pos hi] using hmean i hi
    · simp only [Y, if_neg hi, condExp_zero]
      exact Filter.EventuallyLE.rfl
  have heq : {ω | ∃ j ≤ n, a ≤ ∑ i ∈ range j, X i ω ∧
      (∑ i ∈ range j, Var[X i; P | ℱ i] ω) ≤ v} =
      {ω | ∃ j ≤ n, a ≤ ∑ i ∈ range j, Y i ω ∧
        (∑ i ∈ range j, Var[Y i; P | ℱ i] ω) ≤ v} := by
    ext ω
    apply exists_congr
    intro j
    apply and_congr_right
    intro hj
    have hs : (∑ i ∈ range j, Y i ω) = ∑ i ∈ range j, X i ω := by
      apply sum_congr rfl
      intro i hi
      rw [hYeq i ((mem_range.mp hi).trans_le hj)]
    have hv : (∑ i ∈ range j, Var[Y i; P | ℱ i] ω) =
        ∑ i ∈ range j, Var[X i; P | ℱ i] ω := by
      apply sum_congr rfl
      intro i hi
      rw [hYeq i ((mem_range.mp hi).trans_le hj)]
    rw [hs, hv]
  rw [heq]
  exact freedman_conditionalVariance_bound ha hb hv hY hYb hYmean n

end Arxiv2411_18291
