/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Finite-dimensional Gaussian limits for weighted fair-sign vectors.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.WeightedCentralLimit
import Mathlib.Probability.Distributions.Gaussian.CharFun

namespace Erdos521

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem measurable_vector_sign_sum (s : Finset ℕ) (a : ℕ → E) :
    Measurable (fun ε : ℕ → ℝ ↦ ∑ i ∈ s, ε i • a i) :=
  Finset.measurable_sum _ fun i _ ↦ (measurable_pi_apply i).smul measurable_const

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
noncomputable def vectorSignLaw (s : Finset ℕ) (a : ℕ → E) : ProbabilityMeasure E :=
  ⟨sequenceLaw.map (fun ε : ℕ → ℝ ↦ ∑ i ∈ s, ε i • a i),
    Measure.isProbabilityMeasure_map (measurable_vector_sign_sum s a).aemeasurable⟩

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem charFun_vector_sign_sum (s : Finset ℕ) (a : ℕ → E) (t : E) :
    charFun (sequenceLaw.map (fun ε ↦ ∑ i ∈ s, ε i • a i)) t =
      charFun (sequenceLaw.map (fun ε ↦ ∑ i ∈ s, ⟪a i, t⟫_ℝ * ε i)) 1 := by
  have hv := measurable_vector_sign_sum s a
  have hr : Measurable (fun ε : ℕ → ℝ ↦ ∑ i ∈ s, ⟪a i, t⟫_ℝ * ε i) :=
    Finset.measurable_sum _ fun i _ ↦ measurable_const.mul (measurable_pi_apply i)
  rw [charFun_apply, charFun_apply_real,
    integral_map hv.aemeasurable (by fun_prop), integral_map hr.aemeasurable (by fun_prop)]
  apply integral_congr_ae
  filter_upwards [] with ε
  simp only [sum_inner, real_inner_smul_left]
  congr 2
  rw [Complex.ofReal_one, one_mul]
  apply congrArg Complex.ofReal
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

omit [FiniteDimensional ℝ E] in
theorem triangular_vector_sign_charFun_tendsto (s : ℕ → Finset ℕ) (a : ℕ → ℕ → E)
    (ν : Measure E) [IsGaussian ν] (hmean : (∫ x, x ∂ν) = 0) (t : E)
    (hsmall : ∀ r : ℝ, 0 < r → ∀ᶠ n : ℕ in atTop, ∀ i ∈ s n, |⟪a n i, t⟫_ℝ| < r)
    (hvariance : Tendsto (fun n ↦ ∑ i ∈ s n, ⟪a n i, t⟫_ℝ ^ 2) atTop
      (𝓝 (covarianceBilin ν t t))) :
    Tendsto (fun n ↦ charFun (sequenceLaw.map (fun ε : ℕ → ℝ ↦ ∑ i ∈ s n, ε i • a n i)) t)
      atTop (𝓝 (charFun ν t)) := by
  simp only [IsGaussian.charFun_eq', id, hmean, inner_zero_right]
  simp_rw [charFun_vector_sign_sum]
  have h := triangular_linearForm_charFun_tendsto s (fun n i ↦ ⟪a n i, t⟫_ℝ)
    (covarianceBilin_self_nonneg (μ := ν) t) hsmall hvariance 1
  simpa only [one_pow, mul_one, Complex.ofReal_zero, zero_mul, zero_sub,
    Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat, neg_div] using h

theorem triangular_vector_sign_law_tendsto (s : ℕ → Finset ℕ) (a : ℕ → ℕ → E)
    (ν : ProbabilityMeasure E) [IsGaussian (ν : Measure E)]
    (hmean : (∫ x, x ∂(ν : Measure E)) = 0)
    (hsmall : ∀ t : E, ∀ r : ℝ, 0 < r → ∀ᶠ n : ℕ in atTop, ∀ i ∈ s n, |⟪a n i, t⟫_ℝ| < r)
    (hvariance : ∀ t : E, Tendsto (fun n ↦ ∑ i ∈ s n, ⟪a n i, t⟫_ℝ ^ 2) atTop
      (𝓝 (covarianceBilin (ν : Measure E) t t))) :
    Tendsto (fun n ↦ vectorSignLaw (s n) (a n)) atTop (𝓝 ν) := by
  exact ProbabilityMeasure.tendsto_of_tendsto_charFun (E := E)
    (μ := fun n ↦ vectorSignLaw (s n) (a n)) (μ₀ := ν)
    (fun t ↦ triangular_vector_sign_charFun_tendsto s a ν hmean t (hsmall t) (hvariance t))

theorem triangular_vector_sign_central_limit (s : ℕ → Finset ℕ) (a : ℕ → ℕ → E)
    (ν : Measure E) [IsGaussian ν] (hmean : (∫ x, x ∂ν) = 0)
    (hsmall : ∀ t : E, ∀ r : ℝ, 0 < r → ∀ᶠ n : ℕ in atTop, ∀ i ∈ s n, |⟪a n i, t⟫_ℝ| < r)
    (hvariance : ∀ t : E, Tendsto (fun n ↦ ∑ i ∈ s n, ⟪a n i, t⟫_ℝ ^ 2) atTop
      (𝓝 (covarianceBilin ν t t))) :
    TendstoInDistribution (fun (n : ℕ) (ε : ℕ → ℝ) ↦ ∑ i ∈ s n, ε i • a n i) atTop (fun x : E ↦ x)
      (fun _ ↦ sequenceLaw) ν where
  forall_aemeasurable n := (measurable_vector_sign_sum (s n) (a n)).aemeasurable
  tendsto := by
    let ν₀ : ProbabilityMeasure E := ⟨ν, inferInstance⟩
    have : IsGaussian (ν₀ : Measure E) := by change IsGaussian ν; infer_instance
    have h := triangular_vector_sign_law_tendsto s a ν₀ hmean hsmall hvariance
    simpa only [vectorSignLaw, ν₀, Measure.map_id'] using h

end Erdos521
