import ErdosProblems.Erdos67.StationaryConditionalAtomMass

/-!
# Spectral mass of a dilation fiber with one root removed

Finite differences of modulated averages detect exactly the rest of a
dilation fiber. No orthogonality or eigenprojection is left as an assumption.
-/

open scoped BigOperators ComplexConjugate Topology
open Finset Filter MeasureTheory

namespace Erdos67.StationaryModel

theorem tendsto_atomKernel (θ : FrequencyCircle) :
    Tendsto (fun N ↦ atomKernel N θ) atTop (nhds (if θ = 0 then (1 : ℂ) else 0)) := by
  by_cases hθ : θ = 0
  · subst θ
    simp only [atomKernel_zero]
    exact tendsto_const_nhds
  · rw [if_neg hθ]
    exact tendsto_geometricPolynomial_average hθ

theorem tendsto_integral_atomKernel_difference (σ : ProbabilityMeasure FrequencyCircle)
    (T S : FrequencyCircle → FrequencyCircle) (hT : Continuous T) (hS : Continuous S)
    (hsub : ∀ θ, S θ = 0 → T θ = 0) :
    Tendsto (fun N ↦ ∫ θ, Complex.normSq (atomKernel N (T θ) - atomKernel N (S θ))
      ∂(σ : Measure FrequencyCircle)) atTop
        (nhds ((σ : Measure FrequencyCircle).real {θ | T θ = 0 ∧ S θ ≠ 0})) := by
  have hset : MeasurableSet {θ | T θ = 0 ∧ S θ ≠ 0} :=
    ((isClosed_eq hT continuous_const).measurableSet).inter
      ((isClosed_eq hS continuous_const).measurableSet).compl
  have ht : Tendsto
      (fun N ↦ ∫ θ, Complex.normSq (atomKernel N (T θ) - atomKernel N (S θ))
        ∂(σ : Measure FrequencyCircle)) atTop
      (nhds (∫ θ, (if T θ = 0 ∧ S θ ≠ 0 then (1 : ℝ) else 0)
        ∂(σ : Measure FrequencyCircle))) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ (4 : ℝ))
    · intro N
      exact (Complex.continuous_normSq.comp
        (((continuous_atomKernel N).comp hT).sub
          ((continuous_atomKernel N).comp hS))).aestronglyMeasurable
    · exact integrable_const _
    · intro N
      exact Eventually.of_forall fun θ ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
        have hb := norm_sub_le (atomKernel N (T θ)) (atomKernel N (S θ))
        nlinarith [norm_atomKernel_le N (T θ), norm_atomKernel_le N (S θ),
          norm_nonneg (atomKernel N (T θ) - atomKernel N (S θ))]
    · apply Eventually.of_forall
      intro θ
      have hc := Complex.continuous_normSq.continuousAt.tendsto.comp
        ((tendsto_atomKernel (T θ)).sub (tendsto_atomKernel (S θ)))
      by_cases hs : S θ = 0
      · simpa only [hs, hsub θ hs, if_pos rfl, ne_eq, not_true_eq_false, and_false,
          if_false, sub_self, Complex.normSq_zero, Function.comp_def] using hc
      · by_cases ht : T θ = 0
        · simpa only [hs, ht, if_pos rfl, if_neg hs, ne_eq, not_false_eq_true,
            and_self, if_true, if_false, sub_zero, Complex.normSq_one, Function.comp_def] using hc
        · simpa only [if_neg hs, if_neg ht, ht, false_and, if_false,
            sub_self, Complex.normSq_zero, Function.comp_def] using hc
  have he : (fun θ ↦ if T θ = 0 ∧ S θ ≠ 0 then (1 : ℝ) else 0) =
      Set.indicator {θ | T θ = 0 ∧ S θ ≠ 0} (fun _ ↦ (1 : ℝ)) := by
    funext θ
    simp only [Set.indicator, Set.mem_ofPred_eq]
  rw [he, integral_indicator hset, integral_const] at ht
  simpa only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul, mul_one] using ht

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem coordinatePolynomial_sum_sub (n : ι → ℕ) (m : κ → ℕ) (c : ι → ℂ) (b : κ → ℂ)
    (ω : Configuration) :
    coordinatePolynomial (Sum.elim n m) (Sum.elim c (fun j ↦ -b j)) ω =
      coordinatePolynomial n c ω - coordinatePolynomial m b ω := by
  simp [coordinatePolynomial, Fintype.sum_sum_type, sub_eq_add_neg]

theorem frequencyPolynomial_sum_sub (n : ι → ℕ) (m : κ → ℕ) (c : ι → ℂ) (b : κ → ℂ)
    (θ : FrequencyCircle) :
    frequencyPolynomial (Sum.elim n m) (Sum.elim c (fun j ↦ -b j)) θ =
      frequencyPolynomial n c θ - frequencyPolynomial m b θ := by
  simp [frequencyPolynomial, Fintype.sum_sum_type, sub_eq_add_neg]

theorem integral_modulatedAverage_difference (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ)
    (N d : ℕ) (η ξ : FrequencyCircle) :
    (∫ ω, Complex.normSq (modulatedAverage N d η ω - modulatedAverage N 1 ξ ω)
      ∂(Q : Measure Configuration)) =
      ∫ θ, Complex.normSq (atomKernel N (d • θ - η) - atomKernel N (θ - ξ))
        ∂(σ : Measure FrequencyCircle) := by
  have he := spectral_quadratic_identity Q hQ σ hσ
    (Sum.elim (fun j : Fin (N + 1) ↦ d * j.val) (fun j : Fin (N + 1) ↦ 1 * j.val))
    (Sum.elim (modulationCoefficients N η) (fun j ↦ -modulationCoefficients N ξ j))
  simpa only [coordinatePolynomial_sum_sub, frequencyPolynomial_sum_sub,
    frequencyPolynomial_modulation, one_nsmul, modulatedAverage] using he

theorem tendsto_modulatedAverage_difference (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ)
    (d : ℕ) (η ξ : FrequencyCircle) (hξ : d • ξ = η) :
    Tendsto (fun N ↦ ∫ ω, Complex.normSq (modulatedAverage N d η ω - modulatedAverage N 1 ξ ω)
      ∂(Q : Measure Configuration)) atTop
        (nhds ((σ : Measure FrequencyCircle).real {θ | d • θ = η ∧ θ ≠ ξ})) := by
  have ht := tendsto_integral_atomKernel_difference σ (fun θ ↦ d • θ - η) (fun θ ↦ θ - ξ)
    ((continuous_id.nsmul d).sub continuous_const) (continuous_id.sub continuous_const)
    (fun θ he ↦ by rw [sub_eq_zero] at he; rw [he, hξ, sub_self])
  simpa only [sub_eq_zero, sub_ne_zero, integral_modulatedAverage_difference Q hQ σ hσ] using ht

end Erdos67.StationaryModel
