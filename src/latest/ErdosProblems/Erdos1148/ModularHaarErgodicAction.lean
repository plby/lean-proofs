import ErdosProblems.Erdos1148.ModularHaarNullSets
import Mathlib.Dynamics.Ergodic.Action.Regular

/-! # Ergodicity of all right translations on the modular Haar probability -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Measure Filter
open scoped MatrixGroups ENNReal

theorem normalizedModularHaarMeasure_ae_lift_iff {p : ModularOrbitSpace → Prop}
    (hp : MeasurableSet {x | p x}) :
    (∀ᵐ x ∂normalizedModularHaarMeasure, p x) ↔
      ∀ᵐ g ∂(Measure.haar (G := SL(2, ℝ))), p (modularMk g) := by
  rw [ae_iff, ae_iff, normalizedModularHaarMeasure_null_iff]
  simpa only [Set.compl_def, Set.mem_setOf_eq, Set.preimage] using
    modularHaarMeasure_null_iff hp.compl

theorem normalizedModularHaarMeasure_aeconst_of_right_invariant
    {U : Set ModularOrbitSpace} (hU : MeasurableSet U)
    (hinv : ∀ g : SL(2, ℝ), (modularRightTranslate g) ⁻¹' U =ᵐ[normalizedModularHaarMeasure] U) :
    EventuallyConst U (ae normalizedModularHaarMeasure) := by
  have hB : EventuallyConst (modularMk ⁻¹' U) (ae (Measure.haar (G := SL(2, ℝ)))) := by
    apply aeconst_of_forall_preimage_smul_ae_eq (SL(2, ℝ))ᵐᵒᵖ
      (hU.preimage continuous_modularMk.measurable).nullMeasurableSet
    intro g
    have hp : MeasurableSet {x | modularRightTranslate g.unop x ∈ U ↔ x ∈ U} :=
      ((hU.preimage (continuous_modularRightTranslate g.unop).measurable).mem.iff hU.mem).setOf
    have hlift := (normalizedModularHaarMeasure_ae_lift_iff hp).mp (hinv g.unop).mem_iff
    exact hlift.mono fun k hk => propext hk
  simp only [eventuallyConst_set] at hB ⊢
  rcases hB with hB | hB
  · left
    exact (normalizedModularHaarMeasure_ae_lift_iff hU).mpr hB
  · right
    exact (normalizedModularHaarMeasure_ae_lift_iff hU.compl).mpr hB

end Erdos1148.DukeArithmetic
