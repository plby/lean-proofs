import Arxiv.Arxiv2411_18291.ConditionalVarianceExponential
import Mathlib.Probability.CondVar

/-!
# Centering bounded increments and translating conditional variance

Centering an increment of absolute value at most `b` gives the correct
bound `2*b`. Subtracting a predictable integrable variable does not change
conditional variance.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace Arxiv2411_18291

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable [IsProbabilityMeasure P] {X Z : Ω → ℝ} {b : ℝ}

theorem conditional_center_mean_zero (hm : m ≤ mΩ) (hX : Integrable X P) :
    P[fun ω => X ω - P[X | m] ω | m] =ᵐ[P] 0 := by
  have h := condExp_sub hX (integrable_condExp (f := X) (m := m)) m
  rw [condExp_of_stronglyMeasurable hm stronglyMeasurable_condExp integrable_condExp] at h
  filter_upwards [h] with ω hω
  change P[fun ω => X ω - P[X | m] ω | m] ω = P[X | m] ω - P[X | m] ω at hω
  simpa only [sub_self, Pi.zero_apply] using hω

omit [IsProbabilityMeasure P] in
theorem conditional_center_abs_bound (hXb : ∀ᵐ ω ∂P, |X ω| ≤ b) :
    ∀ᵐ ω ∂P, |X ω - P[X | m] ω| ≤ 2 * b := by
  filter_upwards [hXb, ae_bdd_abs_condExp_of_ae_bdd_abs (m := m) hXb] with ω hx hμ
  calc
    _ ≤ |X ω| + |P[X | m] ω| := abs_sub _ _
    _ ≤ b + b := add_le_add hx hμ
    _ = _ := by ring

theorem condVar_sub_predictable (hm : m ≤ mΩ) (hX : Integrable X P)
    (hZ : Integrable Z P) (hZm : StronglyMeasurable[m] Z) :
    Var[fun ω => X ω - Z ω; P | m] =ᵐ[P] Var[X; P | m] := by
  unfold condVar
  apply condExp_congr_ae
  have h := condExp_sub hX hZ m
  rw [condExp_of_stronglyMeasurable hm hZm hZ] at h
  filter_upwards [h] with ω hω
  change P[fun ω => X ω - Z ω | m] ω = P[X | m] ω - Z ω at hω
  change (X ω - Z ω - P[fun ω => X ω - Z ω | m] ω) ^ 2 =
    (X ω - P[X | m] ω) ^ 2
  rw [hω]
  ring

omit [IsProbabilityMeasure P] in
theorem conditional_secondMoment_eq_condVar_of_mean_zero
    (hmean : P[X | m] =ᵐ[P] 0) :
    P[fun ω => (X ω) ^ 2 | m] =ᵐ[P] Var[X; P | m] := by
  apply condExp_congr_ae
  filter_upwards [hmean] with ω hω
  change (X ω) ^ 2 = (X ω - P[X | m] ω) ^ 2
  simp only [hω, Pi.zero_apply, sub_zero]

end Arxiv2411_18291
