import ErdosProblems.Erdos1164.PermutationRecords

/-! # Averaging discounted covering costs over finite orderings

This is the measure-theoretic part of the permutation argument. Its input is
one discounted estimate for each deterministic ordering, which is separate
from the finite combinatorics and need not be conditioned on the future path.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1164

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_leftRecordCount {n : ℕ} (t : Fin n → Ω → ℝ)
    (ht : ∀ i, Measurable (t i)) :
    Measurable fun w ↦ leftRecordCount (fun i ↦ t i w) := by
  classical
  unfold leftRecordCount
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite _ measurable_const measurable_const
  simpa only [Set.ofPred_forall] using
    (MeasurableSet.iInter fun j : Fin n ↦ MeasurableSet.iInter fun _ : j < i ↦
      measurableSet_lt (ht j) (ht i))

/-- An exponential cost, set to zero off the successful-cover event. -/
noncomputable def discountedCost (A : Set Ω) (c : Ω → ℝ) : Ω → ℝ≥0∞ :=
  A.indicator (fun w ↦ ENNReal.ofReal (Real.exp (-c w)))

/-- The weight corresponding to one independently chosen ordering. -/
noncomputable def recordCostWeight {n : ℕ} (A : Set Ω) (c : Ω → ℝ)
    (t : Fin n → Ω → ℝ) (q : ℝ) (p : Equiv.Perm (Fin n)) : Ω → ℝ≥0∞ :=
  fun w ↦ discountedCost A c w *
    ENNReal.ofReal (q ^ leftRecordCount (fun i ↦ t (p i) w))

theorem measurable_discountedCost {A : Set Ω} (hA : MeasurableSet A)
    {c : Ω → ℝ} (hc : Measurable c) : Measurable (discountedCost A c) := by
  exact (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hc.neg)).indicator hA

theorem measurable_recordCostWeight {n : ℕ} {A : Set Ω} (hA : MeasurableSet A)
    {c : Ω → ℝ} (hc : Measurable c) (t : Fin n → Ω → ℝ)
    (ht : ∀ i, Measurable (t i)) (q : ℝ) (p : Equiv.Perm (Fin n)) :
    Measurable (recordCostWeight A c t q p) := by
  apply (measurable_discountedCost hA hc).mul
  apply ENNReal.measurable_ofReal.comp
  exact (measurable_of_countable (fun k : ℕ ↦ q ^ k)).comp
    (measurable_leftRecordCount (fun i ↦ t (p i)) (fun i ↦ ht (p i)))

private theorem sum_recordCostWeight {n : ℕ} {A : Set Ω} {c : Ω → ℝ}
    (t : Fin n → Ω → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hinj : ∀ w ∈ A, Function.Injective (fun i ↦ t i w)) (w : Ω) :
    (∑ p : Equiv.Perm (Fin n), recordCostWeight A c t q p w) =
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ≥0∞) *
        ENNReal.ofReal (recordGeneratingProduct q n) * discountedCost A c w := by
  classical
  by_cases hw : w ∈ A
  · simp only [recordCostWeight, ← Finset.mul_sum]
    have hsum : (∑ p : Equiv.Perm (Fin n),
        ENNReal.ofReal (q ^ leftRecordCount (fun i ↦ t (p i) w))) =
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ≥0∞) *
          ENNReal.ofReal (recordGeneratingProduct q n) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ ↦ pow_nonneg hq _)]
      have hcard : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := by positivity
      have heq := average_pow_leftRecordCount q n (fun i ↦ t i w) (hinj w hw)
      have heq' := (div_eq_iff hcard).mp heq
      change (∑ p : Equiv.Perm (Fin n), q ^ leftRecordCount (fun i ↦ t (p i) w)) =
        recordGeneratingProduct q n * (Fintype.card (Equiv.Perm (Fin n)) : ℝ) at heq'
      rw [mul_comm] at heq'
      rw [heq', ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    rw [hsum, mul_comm]
  · simp [recordCostWeight, discountedCost, hw]

/-- Independent ordering averages convert the discounted deterministic-order
bounds into a covering-cost Laplace estimate. Injectivity is only required
on the successful-cover event, so capped hitting times may tie off that event. -/
theorem record_cost_laplace_bound {n : ℕ} (μ : Measure Ω)
    {A : Set Ω} (hA : MeasurableSet A) {c : Ω → ℝ} (hc : Measurable c)
    (t : Fin n → Ω → ℝ) (ht : ∀ i, Measurable (t i))
    (q : ℝ) (hq : 1 ≤ q)
    (hinj : ∀ w ∈ A, Function.Injective (fun i ↦ t i w))
    (horder : ∀ p : Equiv.Perm (Fin n), ∫⁻ w, recordCostWeight A c t q p w ∂μ ≤ 1) :
    ENNReal.ofReal (recordGeneratingProduct q n) *
      (∫⁻ w, discountedCost A c w ∂μ) ≤ 1 := by
  have hq0 : 0 ≤ q := by linarith
  have hsum : (∫⁻ w, ∑ p : Equiv.Perm (Fin n), recordCostWeight A c t q p w ∂μ) ≤
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ≥0∞) := by
    rw [lintegral_finsetSum _ (fun p _ ↦ measurable_recordCostWeight hA hc t ht q p)]
    calc
      _ ≤ ∑ _p : Equiv.Perm (Fin n), (1 : ℝ≥0∞) := Finset.sum_le_sum (fun p _ ↦ horder p)
      _ = _ := by simp
  simp_rw [sum_recordCostWeight t q hq0 hinj] at hsum
  rw [lintegral_const_mul'' _ (measurable_discountedCost hA hc).aemeasurable] at hsum
  have hcard : (Fintype.card (Equiv.Perm (Fin n)) : ℝ≥0∞) ≠ 0 := by positivity
  have hfinite : (Fintype.card (Equiv.Perm (Fin n)) : ℝ≥0∞) ≠ ⊤ := by finiteness
  rw [mul_assoc] at hsum
  exact (ENNReal.mul_le_mul_iff_right hcard hfinite).mp (by simpa only [mul_one] using hsum)

/-- The lower tail obtained from the harmonic record estimate. The hypotheses
are the deterministic-order discounted inequalities, not a record-independence
assumption or the desired radius conclusion. -/
theorem record_cost_lower_tail {n : ℕ} (μ : Measure Ω)
    {A : Set Ω} (hA : MeasurableSet A) {c : Ω → ℝ} (hc : Measurable c)
    (t : Fin n → Ω → ℝ) (ht : ∀ i, Measurable (t i))
    (q : ℝ) (hq : 1 ≤ q)
    (hinj : ∀ w ∈ A, Function.Injective (fun i ↦ t i w))
    (horder : ∀ p : Equiv.Perm (Fin n), ∫⁻ w, recordCostWeight A c t q p w ∂μ ≤ 1)
    (u : ℝ) :
    μ (A ∩ {w | c w ≤ u}) ≤
      ENNReal.ofReal (Real.exp (u - (1 - 1 / q) * (harmonic n : ℝ))) := by
  let B := A ∩ {w | c w ≤ u}
  have hB : MeasurableSet B := hA.inter (measurableSet_le hc measurable_const)
  have hpoint : B.indicator (fun _ ↦ ENNReal.ofReal (Real.exp (-u))) ≤ discountedCost A c := by
    intro w
    by_cases hw : w ∈ B
    · rw [Set.indicator_of_mem hw, discountedCost, Set.indicator_of_mem hw.1]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg hw.2))
    · rw [Set.indicator_of_notMem hw]
      exact zero_le
  have hint := lintegral_mono (μ := μ) hpoint
  rw [lintegral_indicator_const hB] at hint
  have hmain := record_cost_laplace_bound μ hA hc t ht q hq hinj horder
  have hprod := ENNReal.ofReal_le_ofReal (recordGeneratingProduct_lower q hq n)
  have hbound : ENNReal.ofReal (Real.exp ((1 - 1 / q) * (harmonic n : ℝ))) *
      (ENNReal.ofReal (Real.exp (-u)) * μ B) ≤ 1 :=
    (mul_le_mul' hprod hint).trans hmain
  have hex : Real.exp ((1 - 1 / q) * (harmonic n : ℝ) - u) =
      Real.exp ((1 - 1 / q) * (harmonic n : ℝ)) * Real.exp (-u) := Real.exp_sub _ _ |>.trans (by rw [Real.exp_neg]; rfl)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← hex] at hbound
  have hzero : ENNReal.ofReal (Real.exp ((1 - 1 / q) * (harmonic n : ℝ) - u)) ≠ 0 := by positivity
  have hfin : ENNReal.ofReal (Real.exp ((1 - 1 / q) * (harmonic n : ℝ) - u)) ≠ ⊤ := by finiteness
  have hdiv : μ B ≤ 1 / ENNReal.ofReal (Real.exp ((1 - 1 / q) * (harmonic n : ℝ) - u)) :=
    (ENNReal.le_div_iff_mul_le (Or.inl hzero) (Or.inl hfin)).mpr
      (by simpa only [mul_comm] using hbound)
  convert hdiv using 1
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_div_of_pos (Real.exp_pos _)]
  congr 1
  simp only [one_div]
  rw [← Real.exp_neg]
  congr 1
  ring

end Erdos1164
