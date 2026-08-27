import Arxiv.Arxiv2411_18291.FreedmanFiniteIncrements
import Arxiv.Arxiv2411_18291.PredictableIndicatorVariance

/-!
# Concentration with predictable switching and local drift hypotheses

An increment is retained only on a past-measurable event. Its conditional
mean need be nonpositive only there. The variance budget may be measured
using the original increments, since predictable switching reduces variance.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ}
variable {s : ℕ → Set Ω} {a b v : ℝ} {n : ℕ}

theorem freedman_predictable_indicator_bound (ha : 0 < a) (hb : 0 < b) (hv : 0 ≤ v)
    (hX : ∀ i < n, StronglyMeasurable[ℱ (i + 1)] (X i))
    (hXb : ∀ i < n, ∀ᵐ ω ∂P, |X i ω| ≤ b)
    (hs : ∀ i < n, MeasurableSet[ℱ i] (s i))
    (hmean : ∀ i < n, ∀ᵐ ω ∂P, ω ∈ s i → P[X i | ℱ i] ω ≤ 0) :
    P.real {ω | ∃ j ≤ n, a ≤ ∑ i ∈ range j, (s i).indicator (X i) ω ∧
      (∑ i ∈ range j, Var[X i; P | ℱ i] ω) ≤ v} ≤
      Real.exp (-(a ^ 2 / (2 * (v + a * b)))) := by
  classical
  let Y := fun i => (s i).indicator (X i)
  have hY : ∀ i < n, StronglyMeasurable[ℱ (i + 1)] (Y i) := by
    intro i hi
    exact (hX i hi).indicator (ℱ.mono (Nat.le_succ i) _ (hs i hi))
  have hYb : ∀ i < n, ∀ᵐ ω ∂P, |Y i ω| ≤ b := by
    intro i hi
    filter_upwards [hXb i hi] with ω hω
    by_cases h : ω ∈ s i
    · simpa only [Y, Set.indicator_of_mem h] using hω
    · simpa only [Y, Set.indicator_of_notMem h, abs_zero] using hb.le
  have hYmean : ∀ i < n, P[Y i | ℱ i] ≤ᵐ[P] 0 := by
    intro i hi
    exact condExp_indicator_nonpos_of_on (hs i hi)
      (Integrable.of_bound ((hX i hi).mono (ℱ.le (i + 1))).aestronglyMeasurable
        b (hXb i hi)) (hmean i hi)
  have hVar : ∀ i, ∀ᵐ ω ∂P, i < n → Var[Y i; P | ℱ i] ω ≤ Var[X i; P | ℱ i] ω := by
    intro i
    by_cases hi : i < n
    · exact (condVar_indicator_le (ℱ.le i) (hs i hi)
        ((hX i hi).mono (ℱ.le (i + 1))) (hXb i hi)).mono fun _ h _ => h
    · exact ae_of_all _ fun _ h => (hi h).elim
  have hsub : {ω | ∃ j ≤ n, a ≤ ∑ i ∈ range j, Y i ω ∧
      (∑ i ∈ range j, Var[X i; P | ℱ i] ω) ≤ v} ≤ᵐ[P]
      {ω | ∃ j ≤ n, a ≤ ∑ i ∈ range j, Y i ω ∧
        (∑ i ∈ range j, Var[Y i; P | ℱ i] ω) ≤ v} := by
    filter_upwards [ae_all_iff.mpr hVar] with ω hω
    rintro ⟨j, hj, hs, hv⟩
    refine ⟨j, hj, hs, (sum_le_sum ?_).trans hv⟩
    intro i hi
    exact hω i ((mem_range.mp hi).trans_le hj)
  exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)).trans
    (freedman_finite_conditionalVariance_bound ha hb hv hY hYb hYmean)

end Arxiv2411_18291
