import ErdosProblems.Erdos1148.SpecialLinearHaar
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction

/-! # The locally finite invariant image of group Haar measure on the upper half-plane -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Measure
open scoped MatrixGroups

noncomputable def upperHalfPlaneHaarImage : Measure UpperHalfPlane :=
  Measure.map (fun g : SL(2, ℝ) => g • UpperHalfPlane.I) (Measure.haar (G := SL(2, ℝ)))

lemma measurable_smul_I : Measurable (fun g : SL(2, ℝ) => g • UpperHalfPlane.I) :=
  (continuous_id.smul continuous_const).measurable

instance upperHalfPlaneHaarImage_finiteOnCompacts : IsFiniteMeasureOnCompacts upperHalfPlaneHaarImage where
  lt_top_of_isCompact K hK := by
    rw [upperHalfPlaneHaarImage, Measure.map_apply measurable_smul_I hK.measurableSet]
    exact (UpperHalfPlane.isProperMap_smul_I.isCompact_preimage hK).measure_lt_top

instance upperHalfPlaneHaarImage_locallyFinite : IsLocallyFiniteMeasure upperHalfPlaneHaarImage :=
  inferInstance

instance upperHalfPlaneHaarImage_sigmaFinite : SigmaFinite upperHalfPlaneHaarImage := inferInstance

instance upperHalfPlaneHaarImage_invariant :
    SMulInvariantMeasure SL(2, ℝ) UpperHalfPlane upperHalfPlaneHaarImage :=
  smulInvariantMeasure_map (Measure.haar (G := SL(2, ℝ)))
    (fun g : SL(2, ℝ) => g • UpperHalfPlane.I) (fun a g => mul_smul a g UpperHalfPlane.I)
    measurable_smul_I

theorem upperHalfPlaneHaarImage_open_pos {U : Set UpperHalfPlane}
    (hU : IsOpen U) (hne : U.Nonempty) : 0 < upperHalfPlaneHaarImage U := by
  rw [upperHalfPlaneHaarImage, Measure.map_apply measurable_smul_I hU.measurableSet]
  apply IsOpen.measure_pos (Measure.haar (G := SL(2, ℝ)))
    (hU.preimage (continuous_id.smul continuous_const))
  obtain ⟨z, hz⟩ := hne
  refine ⟨z.toSL2R, ?_⟩
  change z.toSL2R • UpperHalfPlane.I ∈ U
  rwa [UpperHalfPlane.toSL2R_smul_I]

end Erdos1148.DukeArithmetic
