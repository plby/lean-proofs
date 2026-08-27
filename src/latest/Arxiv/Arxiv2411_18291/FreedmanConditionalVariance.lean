import Arxiv.Arxiv2411_18291.FreedmanSecondMoment
import Arxiv.Arxiv2411_18291.ConditionalCentering

/-!
# Freedman's inequality with conditional variance

Centering changes the increment bound from `b` to `2*b`. Applying the
stronger second-moment bound with this correct constant recovers exactly
the denominator `2*(v+a*b)` stated in the paper, also for supermartingales.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ}
variable {a b v : ℝ}

theorem freedman_conditionalVariance_bound (ha : 0 < a) (hb : 0 < b) (hv : 0 ≤ v)
    (hX : ∀ i, StronglyMeasurable[ℱ (i + 1)] (X i))
    (hXb : ∀ i, ∀ᵐ ω ∂P, |X i ω| ≤ b) (hmean : ∀ i, P[X i | ℱ i] ≤ᵐ[P] 0)
    (n : ℕ) :
    P.real {ω | ∃ j ≤ n, a ≤ ∑ i ∈ range j, X i ω ∧
      (∑ i ∈ range j, Var[X i; P | ℱ i] ω) ≤ v} ≤
      Real.exp (-(a ^ 2 / (2 * (v + a * b)))) := by
  let Y := fun i ω => X i ω - P[X i | ℱ i] ω
  have hY : ∀ i, StronglyMeasurable[ℱ (i + 1)] (Y i) := by
    intro i
    exact (hX i).sub (stronglyMeasurable_condExp.mono (ℱ.mono (Nat.le_succ i)))
  have hYb : ∀ i, ∀ᵐ ω ∂P, |Y i ω| ≤ 2 * b := fun i =>
    conditional_center_abs_bound (hXb i)
  have hYmean : ∀ i, P[Y i | ℱ i] =ᵐ[P] 0 := by
    intro i
    exact conditional_center_mean_zero (ℱ.le i)
      (Integrable.of_bound ((hX i).mono (ℱ.le (i + 1))).aestronglyMeasurable b (hXb i))
  have hsub : {ω | ∃ j ≤ n, a ≤ ∑ i ∈ range j, X i ω ∧
      (∑ i ∈ range j, Var[X i; P | ℱ i] ω) ≤ v} ≤ᵐ[P]
      {ω | ∃ j ≤ n, a ≤ ∑ i ∈ range j, Y i ω ∧
        (∑ i ∈ range j, P[fun ω => (Y i ω) ^ 2 | ℱ i] ω) ≤ v} := by
    filter_upwards [ae_all_iff.mpr hmean] with ω hω
    rintro ⟨j, hj, hs, hv⟩
    refine ⟨j, hj, hs.trans ?_, hv⟩
    apply sum_le_sum
    intro i _
    have hi := hω i
    change P[X i | ℱ i] ω ≤ 0 at hi
    change X i ω ≤ X i ω - P[X i | ℱ i] ω
    linarith only [hi]
  have htail := freedman_secondMoment_bound ha (show 0 < 2 * b by positivity) hv
    hY hYb (fun i => (hYmean i).le) n
  have hden : 2 * v + a * (2 * b) = 2 * (v + a * b) := by ring
  rw [hden] at htail
  exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)).trans htail

end Arxiv2411_18291
