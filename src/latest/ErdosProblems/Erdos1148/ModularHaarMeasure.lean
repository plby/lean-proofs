import ErdosProblems.Erdos1148.ModularHaarFundamentalDomain
import ErdosProblems.Erdos1148.ClosedOrbitInvariance
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! # A finite right-invariant Haar measure on the modular quotient -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Measure
open scoped MatrixGroups ENNReal

instance specialLinearHaarRightInvariant : IsMulRightInvariant (Measure.haar (G := SL(2, ℝ))) :=
  ⟨specialLinear_haar_map_right (Measure.haar (G := SL(2, ℝ)))⟩

noncomputable def modularHaarMeasure : Measure ModularOrbitSpace :=
  Measure.map modularMk ((Measure.haar (G := SL(2, ℝ))).restrict modularHaarDomain)

lemma modularHaarMeasure_apply {U : Set ModularOrbitSpace} (hU : MeasurableSet U) :
    modularHaarMeasure U = (Measure.haar (G := SL(2, ℝ))) (modularMk ⁻¹' U ∩ modularHaarDomain) := by
  rw [modularHaarMeasure, Measure.map_apply continuous_modularMk.measurable hU,
    Measure.restrict_apply (hU.preimage continuous_modularMk.measurable)]

lemma modularHaarMeasure_univ : modularHaarMeasure Set.univ =
    (Measure.haar (G := SL(2, ℝ))) modularHaarDomain := by
  rw [modularHaarMeasure_apply MeasurableSet.univ, Set.preimage_univ, Set.univ_inter]

instance modularHaarMeasure_finite : IsFiniteMeasure modularHaarMeasure where
  measure_univ_lt_top := by rw [modularHaarMeasure_univ]; exact modularHaarDomain_mass_finite

instance modularHaarMeasure_neZero : NeZero modularHaarMeasure := by
  constructor
  intro hzero
  have hpos := modularHaarDomain_mass_pos
  rw [← modularHaarMeasure_univ] at hpos
  simpa [hzero] using hpos

theorem modularHaarMeasure_right_invariant (g : SL(2, ℝ)) :
    Measure.map (modularRightTranslate g) modularHaarMeasure = modularHaarMeasure := by
  let F' := (fun x : SL(2, ℝ) => x * g⁻¹) ⁻¹' modularHaarDomain
  have hfd' : IsFundamentalDomain SL(2, ℤ) F' (Measure.haar (G := SL(2, ℝ))) := by
    apply modularHaarDomain_isFundamentalDomain.preimage_of_equiv
      (measurePreserving_mul_right (Measure.haar (G := SL(2, ℝ))) g⁻¹).quasiMeasurePreserving
      Function.bijective_id
    intro γ x
    exact mul_assoc (γ : SL(2, ℝ)) x g⁻¹
  ext U hU
  rw [Measure.map_apply (continuous_modularRightTranslate g).measurable hU,
    modularHaarMeasure_apply (hU.preimage (continuous_modularRightTranslate g).measurable),
    modularHaarMeasure_apply hU]
  have hsame := hfd'.measure_set_eq modularHaarDomain_isFundamentalDomain
    (hU.preimage continuous_modularMk.measurable) (fun γ => by
      ext x
      simp only [Set.mem_preimage, integralRealMatrix_smul, modularMk_integral_mul])
  rw [← hsame, ← measure_preimage_mul_right (Measure.haar (G := SL(2, ℝ))) g
    (modularMk ⁻¹' U ∩ F')]
  congr 1
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, F', modularRightTranslate_mk, mul_inv_cancel_right]

noncomputable def normalizedModularHaarMeasure : Measure ModularOrbitSpace :=
  (modularHaarMeasure Set.univ)⁻¹ • modularHaarMeasure

instance normalizedModularHaarMeasure_probability : IsProbabilityMeasure normalizedModularHaarMeasure :=
  inferInstanceAs (IsProbabilityMeasure ((modularHaarMeasure Set.univ)⁻¹ • modularHaarMeasure))

noncomputable def modularHaarProbability : ProbabilityMeasure ModularOrbitSpace :=
  ⟨normalizedModularHaarMeasure, inferInstance⟩

theorem normalizedModularHaarMeasure_right_invariant (g : SL(2, ℝ)) :
    Measure.map (modularRightTranslate g) normalizedModularHaarMeasure =
      normalizedModularHaarMeasure := by
  rw [normalizedModularHaarMeasure, Measure.map_smul, modularHaarMeasure_right_invariant]

end Erdos1148.DukeArithmetic
