import Util.Bernays.LaplaceMeasure

/-!
# A half-power Laplace Tauberian theorem

A positive measure whose Laplace transform is asymptotic to `C / sqrt s`
has cumulative mass asymptotic to `2*C*sqrt x / sqrt π`. The proof uses
compact moment convergence and the two-sided cutoff approximations.
-/

open MeasureTheory Filter Topology Real
open scoped unitInterval NNReal

namespace Bernays

theorem laplace_ratio_tendsto {ι : Type*} {l : Filter ι}
    (μ : Measure ℝ≥0) {C : ℝ} (hC : 0 < C)
    (hL : Tendsto (fun t : ℝ => sqrt t * laplace μ t) (𝓝[Set.Ioi 0] 0) (𝓝 C))
    (s : ι → ℝ) (hs : ∀ i, 0 < s i) (hs₀ : Tendsto s l (𝓝 0))
    {K : ℝ} (hK : 0 < K) :
    Tendsto (fun i => laplace μ (K * s i) / laplace μ (s i)) l (𝓝 (1 / sqrt K)) := by
  have hst : Tendsto s l (𝓝[Set.Ioi 0] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hs₀, Filter.Eventually.of_forall hs⟩
  have hKst : Tendsto (fun i => K * s i) l (𝓝[Set.Ioi 0] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [mul_zero] using hs₀.const_mul K
    · exact Filter.Eventually.of_forall fun i => mul_pos hK (hs i)
  have hrat := ((hL.comp hKst).div (hL.comp hst) hC.ne').div_const (sqrt K)
  rw [div_self hC.ne'] at hrat
  apply hrat.congr'
  apply Filter.Eventually.of_forall
  intro i
  change (sqrt (K * s i) * laplace μ (K * s i) /
    (sqrt (s i) * laplace μ (s i))) / sqrt K = _
  rw [sqrt_mul hK.le]
  have hsi : sqrt (s i) ≠ 0 := (sqrt_pos.mpr (hs i)).ne'
  have hKi : sqrt K ≠ 0 := (sqrt_pos.mpr hK).ne'
  calc
    (sqrt K * sqrt (s i) * laplace μ (K * s i) /
        (sqrt (s i) * laplace μ (s i))) / sqrt K =
      (sqrt (s i) * (sqrt K * laplace μ (K * s i)) /
        (sqrt (s i) * laplace μ (s i))) / sqrt K := by ring
    _ = (sqrt K * laplace μ (K * s i) / laplace μ (s i)) / sqrt K := by
      rw [mul_div_mul_left _ _ hsi]
    _ = laplace μ (K * s i) / laplace μ (s i) := by
      rw [mul_div_assoc, mul_div_cancel_left₀ _ hKi]

theorem halfPowerTauberian {ι : Type*} {l : Filter ι}
    (μ : Measure ℝ≥0)
    (hIntegrable : ∀ t : ℝ, 0 < t → Integrable (fun y : ℝ≥0 => exp (-t * y)) μ)
    {C : ℝ} (hC : 0 < C)
    (hL : Tendsto (fun t : ℝ => sqrt t * laplace μ t) (𝓝[Set.Ioi 0] 0) (𝓝 C))
    (s : ι → ℝ) (hs : ∀ i, 0 < s i) (hs₀ : Tendsto s l (𝓝 0)) :
    Tendsto (fun i => sqrt (s i) * μ.real {y : ℝ≥0 | (y : ℝ) ≤ (s i)⁻¹}) l
      (𝓝 (2 * C / sqrt π)) := by
  let ν : ι → FiniteMeasure I := fun i =>
    compactLaplaceMeasure μ (s i) (hs i) (hIntegrable (s i) (hs i))
  have hm (k : ℕ) : Tendsto (fun i => ∫ x : I, (x : ℝ) ^ k ∂(ν i : Measure I)) l
      (𝓝 (∫ x : I, (x : ℝ) ^ k ∂(halfPowerMeasure : Measure I))) := by
    simp only [ν, compactLaplaceMeasure_moment, halfPowerMeasure_moment]
    exact laplace_ratio_tendsto μ hC hL s hs hs₀ (by positivity)
  have hcut := cutoff_integral_tendsto_of_moments hm
    (reciprocalCutWeight (exp (-1)) (exp_pos _))
    (reciprocalCutWeight_nonneg _ _) (exp (-1)) halfPowerMeasure_null_cutoff
  simp only [ν, compactLaplaceMeasure_cutoff, halfPowerMeasure_cutoff_integral] at hcut
  have hst : Tendsto s l (𝓝[Set.Ioi 0] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hs₀, Filter.Eventually.of_forall hs⟩
  have hmain := hcut.mul (hL.comp hst)
  have hfinal : Tendsto
      (fun i => sqrt (s i) * μ.real {y : ℝ≥0 | (y : ℝ) ≤ (s i)⁻¹}) l
      (𝓝 (2 / sqrt π * C)) := by
    apply hmain.congr'
    filter_upwards [(hL.comp hst).eventually (lt_mem_nhds hC)] with i hi
    change 0 < sqrt (s i) * laplace μ (s i) at hi
    have hne : laplace μ (s i) ≠ 0 := by
      intro heq
      simp only [heq, mul_zero, lt_self_iff_false] at hi
    change μ.real {y : ℝ≥0 | (y : ℝ) ≤ (s i)⁻¹} / laplace μ (s i) *
      (sqrt (s i) * laplace μ (s i)) = _
    field_simp
  convert hfinal using 1
  congr 1
  ring

end Bernays
