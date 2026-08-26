import ErdosProblems.Erdos67.StationarySpectralQuadratic

/-!
# Kernels detecting spectral atoms and dilation fibers

Normalized geometric sums converge to the indicator of zero frequency.
Their uniform bound permits dominated convergence against every spectral law.
-/

open scoped BigOperators ComplexConjugate Topology
open Finset Filter MeasureTheory

namespace Erdos67.StationaryModel

noncomputable def atomKernel (N : ℕ) (θ : FrequencyCircle) : ℂ :=
  geometricPolynomial (N + 1) θ / ((N + 1 : ℕ) : ℂ)

theorem continuous_atomKernel (N : ℕ) : Continuous (atomKernel N) :=
  (continuous_geometricPolynomial (N + 1)).div_const _

theorem atomKernel_zero (N : ℕ) : atomKernel N 0 = 1 := by
  rw [atomKernel, geometricPolynomial_zero]
  exact div_self (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero N))

theorem norm_atomKernel_le (N : ℕ) (θ : FrequencyCircle) : ‖atomKernel N θ‖ ≤ 1 := by
  rw [atomKernel, norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.succ_pos N))).2
  rw [one_mul, geometricPolynomial_eq_sum]
  calc
    _ ≤ ∑ j ∈ range (N + 1), ‖fourier (j : ℤ) θ‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_fourier_frequency, sum_const, card_range, nsmul_eq_mul, mul_one]

theorem normSq_atomKernel_le (N : ℕ) (θ : FrequencyCircle) :
    Complex.normSq (atomKernel N θ) ≤ 1 := by
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [norm_atomKernel_le N θ, norm_nonneg (atomKernel N θ)]

theorem tendsto_normSq_atomKernel (θ : FrequencyCircle) :
    Tendsto (fun N ↦ Complex.normSq (atomKernel N θ)) atTop
      (nhds (if θ = 0 then 1 else 0 : ℝ)) := by
  by_cases hθ : θ = 0
  · subst θ
    simp only [atomKernel_zero, Complex.normSq_one]
    exact tendsto_const_nhds
  · rw [if_neg hθ]
    have ht := Complex.continuous_normSq.continuousAt.tendsto.comp
      (tendsto_geometricPolynomial_average hθ)
    simpa only [Complex.normSq_zero, atomKernel, Function.comp_def] using ht

theorem tendsto_integral_atomKernel (σ : ProbabilityMeasure FrequencyCircle)
    (T : FrequencyCircle → FrequencyCircle) (hT : Continuous T) :
    Tendsto (fun N ↦ ∫ θ, Complex.normSq (atomKernel N (T θ)) ∂(σ : Measure FrequencyCircle))
      atTop (nhds ((σ : Measure FrequencyCircle).real {θ | T θ = 0})) := by
  have hzero : MeasurableSet {θ | T θ = 0} := (isClosed_eq hT continuous_const).measurableSet
  have ht : Tendsto
      (fun N ↦ ∫ θ, Complex.normSq (atomKernel N (T θ)) ∂(σ : Measure FrequencyCircle)) atTop
      (nhds (∫ θ, (if T θ = 0 then (1 : ℝ) else 0) ∂(σ : Measure FrequencyCircle))) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ))
    · intro N
      exact (Complex.continuous_normSq.comp
        ((continuous_atomKernel N).comp hT)).aestronglyMeasurable
    · exact integrable_const _
    · intro N
      exact Eventually.of_forall fun θ ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _)]
        exact normSq_atomKernel_le N (T θ)
    · exact Eventually.of_forall fun θ ↦ tendsto_normSq_atomKernel (T θ)
  convert ht using 1
  congr 1
  have he : (fun θ ↦ if T θ = 0 then (1 : ℝ) else 0) =
      Set.indicator {θ | T θ = 0} (fun _ ↦ (1 : ℝ)) := by
    funext θ
    simp only [Set.indicator, Set.mem_ofPred_eq]
  rw [he]
  rw [integral_indicator hzero, integral_const]
  simp

end Erdos67.StationaryModel
