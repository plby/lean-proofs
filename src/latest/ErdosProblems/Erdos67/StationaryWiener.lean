import ErdosProblems.Erdos67.StationaryNonatomicSpectrum
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Mean-square decay of correlations on every nonzero dilation

The normalized geometric kernel on the product spectrum converges to zero
away from the finite dilation diagonal. Nonatomicity makes that diagonal
null, and dominated convergence gives the required Wiener average directly.
-/

open scoped BigOperators ComplexConjugate Topology
open Finset Filter MeasureTheory

namespace Erdos67.StationaryModel

theorem ae_dilated_difference_ne_zero (σ : ProbabilityMeasure FrequencyCircle)
    [NullSingletonClass (σ : Measure FrequencyCircle)] (d : ℕ+) :
    ∀ᵐ z ∂(σ : Measure FrequencyCircle).prod (σ : Measure FrequencyCircle),
      d.val • (z.1 - z.2) ≠ 0 := by
  have hc : Continuous (fun z : FrequencyCircle × FrequencyCircle ↦ d.val • (z.1 - z.2)) :=
    (continuous_fst.sub continuous_snd).nsmul _
  apply (Measure.ae_prod_iff_ae_ae (isClosed_eq hc continuous_const).measurableSet.compl).mpr
  apply Eventually.of_forall
  intro θ
  rw [ae_iff]
  obtain ⟨s, hs, _⟩ := exists_finset_dilation_fiber d (d.val • θ)
  have he : {η : FrequencyCircle | ¬ d.val • (θ - η) ≠ 0} = (s : Set FrequencyCircle) := by
    rw [hs]
    ext η
    simp only [Set.mem_ofPred_eq, not_not, nsmul_sub, sub_eq_zero]
    exact eq_comm
  change (σ : Measure FrequencyCircle) {η | ¬ d.val • (θ - η) ≠ 0} = 0
  rw [he]
  exact s.finite_toSet.measure_zero (σ : Measure FrequencyCircle)

theorem tendsto_integral_product_atomKernel (σ : ProbabilityMeasure FrequencyCircle)
    [NullSingletonClass (σ : Measure FrequencyCircle)] (d : ℕ+) :
    Tendsto (fun N ↦ ∫ z, atomKernel N (d.val • (z.1 - z.2))
      ∂(σ : Measure FrequencyCircle).prod (σ : Measure FrequencyCircle)) atTop (nhds 0) := by
  have ht : Tendsto (fun N ↦ ∫ z, atomKernel N (d.val • (z.1 - z.2))
      ∂(σ : Measure FrequencyCircle).prod (σ : Measure FrequencyCircle)) atTop
      (nhds (∫ _ : FrequencyCircle × FrequencyCircle, (0 : ℂ)
        ∂(σ : Measure FrequencyCircle).prod (σ : Measure FrequencyCircle))) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ))
    · intro N
      exact ((continuous_atomKernel N).comp
        ((continuous_fst.sub continuous_snd).nsmul d.val)).aestronglyMeasurable
    · exact integrable_const _
    · intro N
      exact Eventually.of_forall fun z ↦ norm_atomKernel_le N _
    · filter_upwards [ae_dilated_difference_ne_zero σ d] with z hz
      simpa only [if_neg hz] using tendsto_atomKernel (d.val • (z.1 - z.2))
  simpa only [integral_zero] using ht

theorem integral_product_fourier_difference (Q : ProbabilityMeasure Configuration)
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ) (h : ℤ) :
    (∫ z : FrequencyCircle × FrequencyCircle, fourier h (z.1 - z.2)
      ∂(σ : Measure FrequencyCircle).prod (σ : Measure FrequencyCircle)) =
        ((correlation Q h : ℝ) : ℂ) ^ 2 := by
  simp_rw [fourier_sub_argument]
  rw [integral_prod_mul (fun θ : FrequencyCircle ↦ fourier h θ)
    (fun η : FrequencyCircle ↦ conj (fourier h η)), integral_conj, hσ h]
  simp only [Complex.conj_ofReal, pow_two]

theorem integral_product_atomKernel_eq (Q : ProbabilityMeasure Configuration)
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ) (d N : ℕ) :
    (∫ z : FrequencyCircle × FrequencyCircle, atomKernel N (d • (z.1 - z.2))
      ∂(σ : Measure FrequencyCircle).prod (σ : Measure FrequencyCircle)) =
        ((∑ n ∈ range (N + 1), correlation Q ((d * n : ℕ) : ℤ) ^ 2) /
          ((N + 1 : ℕ) : ℝ) : ℝ) := by
  unfold atomKernel
  simp_rw [geometricPolynomial_eq_sum, fourier_nsmul_argument]
  rw [integral_div, integral_finsetSum]
  · simp_rw [integral_product_fourier_difference Q σ hσ]
    push_cast
    rfl
  · intro n _
    exact ((fourier _).continuous.comp
      (continuous_fst.sub continuous_snd)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem tendsto_correlation_square_average (Q : ProbabilityMeasure Configuration)
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ)
    [NullSingletonClass (σ : Measure FrequencyCircle)] (d : ℕ+) :
    Tendsto (fun N ↦ (∑ n ∈ range (N + 1), correlation Q ((d.val * n : ℕ) : ℤ) ^ 2) /
      ((N + 1 : ℕ) : ℝ)) atTop (nhds 0) := by
  have ht := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_integral_product_atomKernel σ d)
  simpa only [integral_product_atomKernel_eq Q σ hσ, Complex.ofReal_re, Complex.zero_re,
    Function.comp_def] using ht

end Erdos67.StationaryModel
