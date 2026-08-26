import ErdosProblems.Erdos1148.ModularHaarMeasure

/-! # Null sets and full support of the modular Haar probability -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Measure
open scoped MatrixGroups ENNReal Pointwise

lemma integral_smul_modular_preimage (γ : SL(2, ℤ)) (U : Set ModularOrbitSpace) :
    γ • (modularMk ⁻¹' U) = modularMk ⁻¹' U := by
  rw [← Set.preimage_smul_inv]
  ext g
  simp only [Set.mem_preimage, integralRealMatrix_smul, modularMk_integral_mul]

theorem modularHaarMeasure_null_iff {U : Set ModularOrbitSpace} (hU : MeasurableSet U) :
    modularHaarMeasure U = 0 ↔
      (Measure.haar (G := SL(2, ℝ))) (modularMk ⁻¹' U) = 0 := by
  rw [modularHaarMeasure_apply hU]
  constructor
  · exact modularHaarDomain_isFundamentalDomain.measure_zero_of_invariant
      (modularMk ⁻¹' U) (fun γ => integral_smul_modular_preimage γ U)
  · exact measure_mono_null Set.inter_subset_left

theorem normalizedModularHaarMeasure_null_iff (U : Set ModularOrbitSpace) :
    normalizedModularHaarMeasure U = 0 ↔ modularHaarMeasure U = 0 := by
  rw [normalizedModularHaarMeasure, Measure.smul_apply, smul_eq_mul]
  exact mul_eq_zero.trans (or_iff_right (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)))

theorem normalizedModularHaarMeasure_open_pos {U : Set ModularOrbitSpace}
    (hU : IsOpen U) (hne : U.Nonempty) : 0 < normalizedModularHaarMeasure U := by
  apply pos_iff_ne_zero.mpr
  intro hzero
  have hnull := (modularHaarMeasure_null_iff hU.measurableSet).mp
    ((normalizedModularHaarMeasure_null_iff U).mp hzero)
  have hpre : (modularMk ⁻¹' U).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨x.out, by simpa only [Set.mem_preimage, modularMk, Quotient.out_eq] using hx⟩
  exact (IsOpen.measure_pos (Measure.haar (G := SL(2, ℝ)))
    (hU.preimage continuous_modularMk) hpre).ne' hnull

instance normalizedModularHaarMeasure_openPos :
    normalizedModularHaarMeasure.IsOpenPosMeasure :=
  ⟨fun U hU hne => (normalizedModularHaarMeasure_open_pos hU hne).ne'⟩

end Erdos1148.DukeArithmetic
