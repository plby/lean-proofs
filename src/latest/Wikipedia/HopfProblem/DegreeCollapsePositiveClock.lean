import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# A complete positive clock and its actual inverse

The primitive of a continuous speed bounded below by a positive constant
is an order isomorphism of the whole real line. Its inverse has the exact
reciprocal derivative. No completeness or inverse-time premise is assumed.
-/

noncomputable section

open Set Filter Function
open scoped Topology Interval

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange

/-- Integrating a uniformly positive speed constructs an actual complete clock. -/
theorem exists_positive_integral_clock {a : ℝ → ℝ} (ha : Continuous a)
    {δ : ℝ} (hδ : 0 < δ) (hlower : ∀ t, δ ≤ a t) :
    ∃ c : ℝ ≃o ℝ, c 0 = 0 ∧
      (∀ t, c t = ∫ s in (0 : ℝ)..t, a s) ∧
      (∀ t, HasDerivAt c (a t) t) ∧
      ∀ t, HasDerivAt c.symm (a (c.symm t))⁻¹ t := by
  let g : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, a s
  have hd (t : ℝ) : HasDerivAt g (a t) t :=
    intervalIntegral.integral_hasDerivAt_right (ha.intervalIntegrable _ _)
      ha.aestronglyMeasurable.stronglyMeasurableAtFilter ha.continuousAt
  have hg : Differentiable ℝ g := fun t => (hd t).differentiableAt
  have hzero : g 0 = 0 := by simp [g]
  have hmono : StrictMono g := strictMono_of_hasDerivAt_pos hd (fun t => hδ.trans_le (hlower t))
  have hbound {s t : ℝ} (hst : s ≤ t) : δ * (t - s) ≤ g t - g s :=
    mul_sub_le_image_sub_of_le_deriv hg (fun t => by rw [(hd t).deriv]; exact hlower t) hst
  have hsurj : Surjective g := by
    intro y
    apply mem_range_of_exists_le_of_exists_ge hg.continuous
    · refine ⟨min 0 (y / δ), ?_⟩
      have hh := hbound (min_le_left 0 (y / δ))
      have hm : δ * min 0 (y / δ) ≤ y := by
        calc
          δ * min 0 (y / δ) ≤ δ * (y / δ) := mul_le_mul_of_nonneg_left (min_le_right _ _) hδ.le
          _ = y := by field_simp
      rw [hzero] at hh
      linarith
    · refine ⟨max 0 (y / δ), ?_⟩
      have hh := hbound (le_max_left 0 (y / δ))
      have hm : y ≤ δ * max 0 (y / δ) := by
        calc
          y = δ * (y / δ) := by field_simp
          _ ≤ δ * max 0 (y / δ) := mul_le_mul_of_nonneg_left (le_max_right _ _) hδ.le
      rw [hzero] at hh
      linarith
  let c : ℝ ≃o ℝ := hmono.orderIsoOfSurjective g hsurj
  refine ⟨c, hzero, fun _ => rfl, hd, ?_⟩
  intro t
  exact HasDerivAt.of_local_left_inverse c.symm.continuous.continuousAt
    (hd (c.symm t)) (ne_of_gt (hδ.trans_le (hlower _)))
    (Filter.Eventually.of_forall c.apply_symm_apply)

end Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange
