import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Probability.ProbabilityMassFunction.Constructions

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Deleting moments on events of vanishing probability

This file records the precise Cauchy--Schwarz step used when the continued-
fraction denominator good event is imposed in the marked point-process
argument.  A uniform `2r`-moment bound makes the `r`-th moment uniformly
integrable; consequently its integral over any measurable sequence of events
whose probabilities tend to zero also tends to zero.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace Erdos1002

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Cauchy--Schwarz on a measurable event, written in the exact form needed
for moment deletion. -/
theorem setIntegral_le_sqrt_sqIntegral_mul_sqrt_measureReal
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {f : Ω → ℝ} {E : Set Ω}
    (hf : Measurable f) (hf_nonneg : ∀ ω, 0 ≤ f ω)
    (hf_sq : Integrable (fun ω ↦ f ω ^ 2) μ)
    (hE : MeasurableSet E) :
    ∫ ω in E, f ω ∂μ ≤
      Real.sqrt (∫ ω, f ω ^ 2 ∂μ) * Real.sqrt (μ.real E) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hf_mem : MemLp f 2 μ :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2 hf_sq
  have hE_mem : MemLp (E.indicator (fun _ ↦ (1 : ℝ))) 2 μ :=
    memLp_indicator_const 2 hE 1 (Or.inr (measure_ne_top μ E))
  have hf_mem' : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using! hf_mem
  have hE_mem' : MemLp (E.indicator (fun _ ↦ (1 : ℝ)))
      (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using! hE_mem
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (ae_of_all μ hf_nonneg)
    (ae_of_all μ fun ω ↦
      indicator_nonneg (fun _ _ ↦ (zero_le_one : (0 : ℝ) ≤ 1)) ω)
    hf_mem' hE_mem'
  have hleft :
      (∫ ω in E, f ω ∂μ) =
        ∫ ω, f ω * E.indicator (fun _ ↦ (1 : ℝ)) ω ∂μ := by
    rw [← integral_indicator hE]
    apply integral_congr_ae
    filter_upwards with ω
    by_cases hω : ω ∈ E <;> simp [Set.indicator, hω]
  have hE_sq :
      (∫ ω, E.indicator (fun _ ↦ (1 : ℝ)) ω ^ (2 : ℝ) ∂μ) =
        μ.real E := by
    convert! integral_indicator_one hE using 1
    apply integral_congr_ae
    filter_upwards with ω
    by_cases hω : ω ∈ E <;> simp [Set.indicator, hω]
  rw [← hleft] at hholder
  rw [hE_sq] at hholder
  simpa [Real.rpow_two, Real.sqrt_eq_rpow, one_div] using! hholder

/-- A uniformly square-integrable sequence has vanishing integral on a
sequence of events whose measures tend to zero. -/
theorem tendsto_setIntegral_zero_of_uniform_sq_integral
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : ℕ → Ω → ℝ) (E : ℕ → Set Ω)
    (hf : ∀ n, Measurable (f n))
    (hf_nonneg : ∀ n ω, 0 ≤ f n ω)
    (hf_sq : ∀ n, Integrable (fun ω ↦ f n ω ^ 2) μ)
    (hE : ∀ n, MeasurableSet (E n))
    (hE_zero : Tendsto (fun n ↦ μ.real (E n)) atTop (𝓝 0))
    {C : ℝ} (hC : ∀ n, ∫ ω, f n ω ^ 2 ∂μ ≤ C) :
    Tendsto (fun n ↦ ∫ ω in E n, f n ω ∂μ) atTop (𝓝 0) := by
  have hC_nonneg : 0 ≤ C := by
    exact (integral_nonneg fun ω ↦ sq_nonneg (f 0 ω)).trans (hC 0)
  have hsqrt_measure :
      Tendsto (fun n ↦ Real.sqrt (μ.real (E n))) atTop (𝓝 0) := by
    simpa using! (Real.continuous_sqrt.tendsto 0).comp hE_zero
  have hupper :
      Tendsto (fun n ↦ Real.sqrt C * Real.sqrt (μ.real (E n)))
        atTop (𝓝 0) := by
    simpa using! tendsto_const_nhds.mul hsqrt_measure
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards with n
    exact setIntegral_nonneg (hE n) fun ω _ ↦ hf_nonneg n ω
  · filter_upwards with n
    refine (setIntegral_le_sqrt_sqIntegral_mul_sqrt_measureReal
      μ (hf n) (hf_nonneg n) (hf_sq n) (hE n)).trans ?_
    exact mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt (hC n)) (Real.sqrt_nonneg _)

/-- Natural-valued moment version.  The explicit integrability hypothesis is
important: a Bochner integral is defined to be zero for a non-integrable
function, so a numerical upper bound on that integral alone cannot certify
integrability. -/
theorem tendsto_setIntegral_natCast_pow_on_vanishing_events
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℕ) (E : ℕ → Set Ω) (r : ℕ)
    (hX : ∀ n, Measurable (X n))
    (hX_moment : ∀ n,
      Integrable (fun ω ↦ (X n ω : ℝ) ^ (2 * r)) μ)
    (hE : ∀ n, MeasurableSet (E n))
    (hE_zero : Tendsto (fun n ↦ μ.real (E n)) atTop (𝓝 0))
    {C : ℝ}
    (hC : ∀ n, ∫ ω, (X n ω : ℝ) ^ (2 * r) ∂μ ≤ C) :
    Tendsto
      (fun n ↦ ∫ ω in E n, (X n ω : ℝ) ^ r ∂μ)
      atTop (𝓝 0) := by
  apply tendsto_setIntegral_zero_of_uniform_sq_integral μ
    (fun n ω ↦ (X n ω : ℝ) ^ r) E (C := C)
  · intro n
    exact ((measurable_of_countable (fun k : ℕ ↦ (k : ℝ))).comp (hX n)).pow_const r
  · intro n ω
    positivity
  · intro n
    simpa [pow_two, ← pow_add, two_mul] using! hX_moment n
  · exact hE
  · exact hE_zero
  · intro n
    simpa [pow_two, ← pow_add, two_mul] using! hC n

end

end Erdos1002
