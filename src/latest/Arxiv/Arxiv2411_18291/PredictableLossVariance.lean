import Arxiv.Arxiv2411_18291.ConditionalVarianceBounds
import Arxiv.Arxiv2411_18291.ConditionalCentering

/-!
# Variance of a bounded loss minus a predictable comparison increment

The predictable comparison does not contribute to conditional variance.
For a nonnegative bounded loss, the remaining variance is bounded by its
conditional mean times the loss bound.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace Arxiv2411_18291

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable [IsProbabilityMeasure P] {X Z : Ω → ℝ} {b : ℝ}

theorem condVar_neg_sub_predictable (hm : m ≤ mΩ) (hX : Integrable X P)
    (hZ : Integrable Z P) (hZm : StronglyMeasurable[m] Z) :
    Var[fun ω => -X ω - Z ω; P | m] =ᵐ[P] Var[X; P | m] :=
  (condVar_sub_predictable hm hX.neg hZ hZm).trans (condVar_neg X)

theorem conditional_variance_of_bounded_loss (hm : m ≤ mΩ) (hX : StronglyMeasurable X)
    (hXb : ∀ᵐ ω ∂P, 0 ≤ X ω ∧ X ω ≤ b) (hZ : Integrable Z P)
    (hZm : StronglyMeasurable[m] Z) :
    Var[fun ω => -X ω - Z ω; P | m] ≤ᵐ[P] fun ω => b * P[X | m] ω := by
  have habs : ∀ᵐ ω ∂P, |X ω| ≤ b := hXb.mono fun ω h => by
    rw [abs_of_nonneg h.1]
    exact h.2
  have hXi : Integrable X P := Integrable.of_bound hX.aestronglyMeasurable b habs
  have hcongr : P[fun ω => |X ω| | m] =ᵐ[P] P[X | m] :=
    condExp_congr_ae (hXb.mono fun _ h => abs_of_nonneg h.1)
  filter_upwards [condVar_neg_sub_predictable hm hXi hZ hZm,
    conditional_variance_le_mul_abs_mean hm hX habs, hcongr] with ω heq hvar hmean
  rw [heq, ← hmean]
  exact hvar

end Arxiv2411_18291
