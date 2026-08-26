import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.Filter.AtTopBot.Basic

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Set
open scoped ENNReal

namespace CofiniteDerivatives

variable {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
variable (μ : Measure Ω)

/-- Summable failure probabilities imply eventual success for each target, simultaneously for a
countable family of targets. No independence assumption is used. -/
theorem ae_forall_eventually_not_failure (failure : ι → ℕ → Set Ω)
    (hsum : ∀ i, (∑' n, μ (failure i n)) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ i, ∃ N, ∀ n ≥ N, ω ∉ failure i n := by
  rw [ae_all_iff]
  intro i
  have hbc : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ω ∉ failure i n :=
    ae_eventually_notMem (hsum i)
  filter_upwards [hbc] with ω hω
  exact eventually_atTop.mp hω

/-- A point satisfying every eventual-success condition exists whenever the ambient measure is
nonzero. This is the deterministic-sample extraction used at the end of the proof. -/
theorem exists_forall_eventually_not_failure [NeZero μ] (failure : ι → ℕ → Set Ω)
    (hsum : ∀ i, (∑' n, μ (failure i n)) ≠ ∞) :
    ∃ ω, ∀ i, ∃ N, ∀ n ≥ N, ω ∉ failure i n := by
  have h := ae_forall_eventually_not_failure μ failure hsum
  exact Filter.Eventually.exists h

end CofiniteDerivatives
