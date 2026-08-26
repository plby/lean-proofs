/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos254.FourierAverages

namespace Erdos254

open Filter MeasureTheory Set
open scoped BigOperators Topology ComplexConjugate

/-- Nonnegative-index Fourier coefficients of a finite measure on the circle. -/
noncomputable def circleCoeff (μ : Measure Circle) (n : ℕ) : ℂ :=
  ∫ z, (z : ℂ) ^ n ∂μ

noncomputable def circleQuotient : C(Circle × Circle, Circle) :=
  ⟨fun p ↦ p.1 / p.2, by fun_prop⟩

@[simp] lemma circleQuotient_apply (p : Circle × Circle) : circleQuotient p = p.1 / p.2 := rfl

lemma integral_circleCorrelation (μ : Measure Circle) [IsFiniteMeasure μ] (n : ℕ) :
    (∫ p : Circle × Circle, (circleQuotient p : ℂ) ^ n ∂μ.prod μ) =
      ((‖circleCoeff μ n‖ ^ 2 : ℝ) : ℂ) := by
  calc
    _ = ∫ p : Circle × Circle, (p.1 : ℂ) ^ n * conj ((p.2 : ℂ) ^ n) ∂μ.prod μ := by
      congr 1
      funext p
      simp only [circleQuotient_apply, div_eq_mul_inv, Circle.coe_mul,
        Circle.coe_inv_eq_conj, mul_pow, map_pow]
    _ = (∫ z : Circle, (z : ℂ) ^ n ∂μ) * ∫ z : Circle, conj ((z : ℂ) ^ n) ∂μ :=
      integral_prod_mul (μ := μ) (ν := μ) (L := ℂ)
        (fun z : Circle ↦ (z : ℂ) ^ n) (fun z : Circle ↦ conj ((z : ℂ) ^ n))
    _ = _ := by rw [integral_conj, Complex.mul_conj]; simp [circleCoeff, Complex.normSq_eq_norm_sq]

/-- A positive bound for all translated Fourier-square averages of the same length. -/
noncomputable def wienerBound (μ : Measure Circle) (N : ℕ) : ℝ :=
  ∫ p : Circle × Circle, ‖circleAverage N (circleQuotient p)‖ ∂μ.prod μ

lemma circle_window_integral (μ : Measure Circle) [IsFiniteMeasure μ] (m N : ℕ) :
    (∫ p : Circle × Circle,
        (circleQuotient p : ℂ) ^ m * circleAverage N (circleQuotient p) ∂μ.prod μ) =
      (N + 1 : ℂ)⁻¹ * ∑ k ∈ Finset.range (N + 1),
        ((‖circleCoeff μ (m + k)‖ ^ 2 : ℝ) : ℂ) := by
  have hpoint (p : Circle × Circle) :
      (circleQuotient p : ℂ) ^ m * circleAverage N (circleQuotient p) =
        (N + 1 : ℂ)⁻¹ * ∑ k ∈ Finset.range (N + 1),
          (circleQuotient p : ℂ) ^ (m + k) := by
    rw [circleAverage_apply]
    simp_rw [pow_add, ← Finset.mul_sum]
    ring
  simp_rw [hpoint]
  rw [integral_const_mul, integral_finsetSum]
  · simp_rw [integral_circleCorrelation]
  · intro k _
    exact ((continuous_subtype_val.comp circleQuotient.continuous).pow
      (m + k)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

lemma circleCoeff_window_le (μ : Measure Circle) [IsFiniteMeasure μ] (m N : ℕ) :
    (N + 1 : ℝ)⁻¹ * ∑ k ∈ Finset.range (N + 1), ‖circleCoeff μ (m + k)‖ ^ 2 ≤
      wienerBound μ N := by
  let F : Circle × Circle → ℂ := fun p ↦
    (circleQuotient p : ℂ) ^ m * circleAverage N (circleQuotient p)
  have hreal : (∫ p, F p ∂μ.prod μ).re =
      (N + 1 : ℝ)⁻¹ * ∑ k ∈ Finset.range (N + 1), ‖circleCoeff μ (m + k)‖ ^ 2 := by
    change (∫ p : Circle × Circle,
      (circleQuotient p : ℂ) ^ m * circleAverage N (circleQuotient p) ∂μ.prod μ).re = _
    rw [circle_window_integral]
    have hc : (N + 1 : ℂ)⁻¹ * ∑ k ∈ Finset.range (N + 1),
        ((‖circleCoeff μ (m + k)‖ ^ 2 : ℝ) : ℂ) =
        (((N + 1 : ℝ)⁻¹ * ∑ k ∈ Finset.range (N + 1),
          ‖circleCoeff μ (m + k)‖ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
    exact congrArg Complex.re hc
  rw [← hreal]
  calc
    _ ≤ ‖∫ p, F p ∂μ.prod μ‖ := Complex.re_le_norm _
    _ ≤ ∫ p, ‖F p‖ ∂μ.prod μ := norm_integral_le_integral_norm _
    _ = wienerBound μ N := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p ↦ by
        simp only [F, norm_mul, norm_pow, Circle.norm_coe, one_pow, one_mul]

/-- Wiener decay in a form uniform over the initial point of an interval. -/
theorem tendsto_wienerBound (μ : Measure Circle) [IsFiniteMeasure μ]
    [NullSingletonClass μ] : Tendsto (wienerBound μ) atTop (𝓝 0) := by
  have hneq : ∀ᵐ p : Circle × Circle ∂μ.prod μ, p.1 ≠ p.2 := by
    apply (Measure.ae_prod_iff_ae_ae
      (isClosed_eq continuous_fst continuous_snd).measurableSet.compl).2
    apply Filter.Eventually.of_forall
    intro z
    simpa [eq_comm] using (Set.countable_singleton z).ae_notMem μ
  have hlim : ∀ᵐ p : Circle × Circle ∂μ.prod μ,
      Tendsto (fun N ↦ ‖circleAverage N (circleQuotient p)‖) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hneq] with p hp
    have hq : circleQuotient p ≠ 1 := fun h ↦ hp (div_eq_one.mp h)
    simpa using (tendsto_circleAverage_of_ne_one hq).norm
  have h := tendsto_integral_of_dominated_convergence (μ := μ.prod μ)
    (fun _ ↦ (1 : ℝ))
    (fun N ↦ (show Continuous (fun p : Circle × Circle ↦
      ‖circleAverage N (circleQuotient p)‖) by fun_prop).aestronglyMeasurable)
    (integrable_const 1)
    (fun N ↦ Filter.Eventually.of_forall fun p ↦ by
      simpa only [norm_norm] using norm_circleAverage_le_one N (circleQuotient p)) hlim
  change Tendsto (fun N ↦ ∫ p : Circle × Circle,
    ‖circleAverage N (circleQuotient p)‖ ∂μ.prod μ) atTop (𝓝 0)
  simpa only [integral_zero] using h

theorem uniform_wiener (μ : Measure Circle) [IsFiniteMeasure μ] [NullSingletonClass μ]
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ (N : ℕ) in atTop, ∀ m : ℕ,
      (N + 1 : ℝ)⁻¹ * ∑ k ∈ Finset.range (N + 1), ‖circleCoeff μ (m + k)‖ ^ 2 < ε := by
  filter_upwards [(tendsto_wienerBound μ).eventually_lt_const hε] with N hN m
  exact (circleCoeff_window_le μ m N).trans_lt hN

end Erdos254
