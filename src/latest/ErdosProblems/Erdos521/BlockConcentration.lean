/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Combining sub-Gaussian bounds for blocks without independence between blocks.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.BoundedConcentration

namespace Erdos521

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

theorem subGaussian_parameter_mono {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {c d : ℝ≥0} (hX : HasSubgaussianMGF X c μ) (hcd : c ≤ d) :
    HasSubgaussianMGF X d μ := by
  refine ⟨hX.integrable_exp_mul, ?_⟩
  intro t
  apply (hX.mgf_le t).trans
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr hcd) (sq_nonneg t)) (by norm_num)

theorem subGaussian_finsetSum {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (S : Finset ι) {X : ι → Ω → ℝ} {c : ι → ℝ≥0}
    (hX : ∀ i ∈ S, HasSubgaussianMGF (X i) (c i) μ) :
    HasSubgaussianMGF (fun ω ↦ ∑ i ∈ S, X i ω) ((∑ i ∈ S, (c i).sqrt) ^ 2) μ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hfirst := hX i (Finset.mem_insert_self _ _)
    have hrest := ih (fun j hj ↦ hX j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi, NNReal.sqrt_sq] using hfirst.add hrest

theorem subGaussian_block_sum_probability {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (S : Finset ι) {X : ι → Ω → ℝ} {c : ℝ≥0}
    (hX : ∀ i ∈ S, HasSubgaussianMGF (X i) c μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i ∈ S, X i ω|} ≤
      2 * Real.exp (-t ^ 2 / (2 * (S.card : ℝ) ^ 2 * (c : ℝ))) := by
  have h := subGaussian_abs_probability μ (subGaussian_finsetSum μ S hX) ht
  have heq : ((∑ _i ∈ S, c.sqrt) ^ 2 : ℝ≥0) = (S.card : ℝ≥0) ^ 2 * c := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_pow, NNReal.sq_sqrt]
  simpa only [heq, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast, ← mul_assoc] using h

end Erdos521
