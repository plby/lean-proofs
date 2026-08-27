import Arxiv.Arxiv2411_18291.ConditionalCentering
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-!
# Conditional variance after switching off an increment predictably

Multiplication by the indicator of a past-measurable event switches off
both the conditional mean and the conditional variance on its complement.
This will stop the tracked processes when their drift estimates cease to apply.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace Arxiv2411_18291

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {X : Ω → ℝ} {s : Set Ω} {b : ℝ}

theorem conditional_variance_nonneg : 0 ≤ᵐ[P] Var[X; P | m] :=
  condExp_nonneg (ae_of_all _ fun ω => sq_nonneg (X ω - P[X | m] ω))

variable [IsProbabilityMeasure P]

theorem condVar_indicator_of_abs_bound (hm : m ≤ mΩ) (hs : MeasurableSet[m] s)
    (hX : StronglyMeasurable X) (hXb : ∀ᵐ ω ∂P, |X ω| ≤ b) :
    Var[s.indicator X; P | m] =ᵐ[P] s.indicator Var[X; P | m] := by
  classical
  have hXi : Integrable X P := Integrable.of_bound hX.aestronglyMeasurable b hXb
  have hcenter : StronglyMeasurable (fun ω => X ω - P[X | m] ω) :=
    hX.sub (stronglyMeasurable_condExp.mono hm)
  have hsquare := integrable_sq_of_abs_bound hcenter (conditional_center_abs_bound hXb)
  have heq : ((s.indicator X - P[s.indicator X | m]) ^ 2) =ᵐ[P]
      s.indicator (fun ω => (X ω - P[X | m] ω) ^ 2) := by
    filter_upwards [condExp_indicator hXi hs] with ω hω
    change (s.indicator X ω - P[s.indicator X | m] ω) ^ 2 =
      s.indicator (fun ω => (X ω - P[X | m] ω) ^ 2) ω
    rw [hω]
    by_cases h : ω ∈ s <;> simp [h]
  exact (condExp_congr_ae heq).trans (condExp_indicator hsquare hs)

theorem condVar_indicator_le (hm : m ≤ mΩ) (hs : MeasurableSet[m] s)
    (hX : StronglyMeasurable X) (hXb : ∀ᵐ ω ∂P, |X ω| ≤ b) :
    Var[s.indicator X; P | m] ≤ᵐ[P] Var[X; P | m] := by
  classical
  filter_upwards [condVar_indicator_of_abs_bound hm hs hX hXb,
    conditional_variance_nonneg (X := X) (m := m)] with ω heq hnonneg
  rw [heq]
  by_cases h : ω ∈ s
  · simp [h]
  · simpa only [Set.indicator_of_notMem h, Pi.zero_apply] using hnonneg

omit [IsProbabilityMeasure P] in
theorem condExp_indicator_nonpos_of_on (hs : MeasurableSet[m] s) (hX : Integrable X P)
    (hmean : ∀ᵐ ω ∂P, ω ∈ s → P[X | m] ω ≤ 0) :
    P[s.indicator X | m] ≤ᵐ[P] 0 := by
  classical
  filter_upwards [condExp_indicator hX hs, hmean] with ω heq hmean
  change P[s.indicator X | m] ω ≤ 0
  rw [heq]
  by_cases h : ω ∈ s
  · simpa only [Set.indicator_of_mem h] using hmean h
  · simp [h]

end Arxiv2411_18291
