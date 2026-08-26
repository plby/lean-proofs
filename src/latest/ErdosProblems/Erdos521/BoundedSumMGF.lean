/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The moment-generating-function bound for a bounded independent sum.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.BlockConcentration

namespace Erdos521

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

theorem bounded_independent_sum_subGaussian {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Finset ι) {X : ι → Ω → ℝ}
    (hind : iIndepFun X μ) (hX : ∀ i, AEMeasurable (X i) μ) {T : ℝ}
    (hbound : ∀ i ∈ S, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc 0 T) :
    HasSubgaussianMGF (fun ω ↦ ∑ i ∈ S, (X i ω - ∫ z, X i z ∂μ))
      ((S.card : ℝ≥0) * (‖T‖₊ / 2) ^ 2) μ := by
  have hi : iIndepFun (fun i ω ↦ X i ω - ∫ z, X i z ∂μ) μ :=
    hind.comp (fun i x ↦ x - ∫ z, X i z ∂μ) (fun _ ↦ by fun_prop)
  have hsub (i : ι) (hiS : i ∈ S) :
      HasSubgaussianMGF (fun ω ↦ X i ω - ∫ z, X i z ∂μ) ((‖T‖₊ / 2) ^ 2) μ := by
    simpa only [sub_zero] using hasSubgaussianMGF_of_mem_Icc (hX i) (hbound i hiS)
  simpa only [Finset.sum_const, nsmul_eq_mul] using HasSubgaussianMGF.sum_of_iIndepFun hi hsub

end Erdos521
