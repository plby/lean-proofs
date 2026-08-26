import ErdosProblems.Erdos69.MomentErrorBounds
import ErdosProblems.Erdos69.ProgressionBounds

/-! # Vanishing of the concrete small-prime characteristic function -/

open Filter
open scoped BigOperators Topology

namespace Erdos69.Elementary

theorem tendsto_modelCharacteristic_norm {q : ℝ} (hq : 0 < q) :
    Tendsto (fun m ↦ ‖modelCharacteristic q m‖) atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_primeReciprocal_error_constant
  have hε := (tendsto_coefficientMassBound q).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  apply squeeze_zero' (Filter.Eventually.of_forall (fun m ↦ norm_nonneg _)) _
    (tendsto_independent_decay hq)
  filter_upwards [eventually_ge_atTop (1 : ℕ), hε, eventually_goodPrime_mass_ge_quarter hC]
    with m hm he hmass
  have hi : |firstCoefficient q m| ≤ 1 / 2 := (firstCoefficient_abs_le_mass q m).trans he.le
  have h := constructionModel_fourier_le (by omega : 0 < m) q hi
  apply h.trans
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ 4 * firstCoefficient q m ^ 2)
  nlinarith

theorem tendsto_smallCharacteristic_norm {q : ℝ} (hq : 0 < q) :
    Tendsto (fun m ↦ ‖smallCharacteristic q m‖) atTop (𝓝 0) := by
  have h := (tendsto_modelCharacteristic_norm hq).add (tendsto_small_sub_model_norm q)
  simp only [add_zero] at h
  apply squeeze_zero (fun m ↦ norm_nonneg _) _ h
  intro m
  have ht := norm_le_norm_add_norm_sub (modelCharacteristic q m) (smallCharacteristic q m)
  simpa only [norm_sub_rev (modelCharacteristic q m)] using ht

end Erdos69.Elementary
