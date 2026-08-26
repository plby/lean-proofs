/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Two-sided concentration for bounded independent local statistics.
Formal proof: Codex.
-/
import Mathlib.Probability.Moments.SubGaussian

namespace Erdos521

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

theorem subGaussian_abs_probability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0} (hX : HasSubgaussianMGF X c μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |X ω|} ≤ 2 * Real.exp (-t ^ 2 / (2 * (c : ℝ))) := by
  have hsub : {ω | t ≤ |X ω|} ⊆ {ω | t ≤ X ω} ∪ {ω | t ≤ -X ω} := by
    intro ω hω
    change t ≤ |X ω| at hω
    change t ≤ X ω ∨ t ≤ -X ω
    rcases le_total 0 (X ω) with h | h
    · exact Or.inl (by simpa only [abs_of_nonneg h] using hω)
    · exact Or.inr (by simpa only [abs_of_nonpos h] using hω)
  have h := (measureReal_mono (μ := μ) hsub).trans (measureReal_union_le _ _)
  have hright := hX.measure_ge_le ht
  have hleft := hX.neg.measure_ge_le ht
  dsimp only [Pi.neg_apply] at hleft
  linarith

theorem bounded_independent_sum_probability {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Finset ι) {X : ι → Ω → ℝ}
    (hind : iIndepFun X μ) (hX : ∀ i, AEMeasurable (X i) μ) {T : ℝ} (hT : 0 ≤ T)
    (hbound : ∀ i ∈ S, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc 0 T) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i ∈ S, (X i ω - ∫ z, X i z ∂μ)|} ≤
      2 * Real.exp (-t ^ 2 / (2 * (S.card : ℝ) * (T / 2) ^ 2)) := by
  have hi : iIndepFun (fun i ω ↦ X i ω - ∫ z, X i z ∂μ) μ :=
    hind.comp (fun i x ↦ x - ∫ z, X i z ∂μ) (fun _ ↦ by fun_prop)
  have hsub (i : ι) (hiS : i ∈ S) :
      HasSubgaussianMGF (fun ω ↦ X i ω - ∫ z, X i z ∂μ) ((‖T‖₊ / 2) ^ 2) μ := by
    simpa only [sub_zero] using hasSubgaussianMGF_of_mem_Icc (hX i) (hbound i hiS)
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hi hsub
  have h := subGaussian_abs_probability μ hsum ht
  simpa only [Finset.sum_const, nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast,
    NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg hT,
    ← mul_assoc] using h

end Erdos521
