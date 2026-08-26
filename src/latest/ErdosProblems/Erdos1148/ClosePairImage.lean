import ErdosProblems.Erdos1148.ClosedPairImageMeasure
import ErdosProblems.Erdos1148.SignedFlow

/-! # The measure bound for the close-time image of one pair of closed orbits -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups

lemma continuous_realMatrixEntry (i j : Fin 2) : Continuous (fun g : SL(2, ℝ) => g i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous)

lemma isClosed_entryCloseOne (η : ℝ) : IsClosed {g : SL(2, ℝ) | EntryCloseOne η g} := by
  exact (isClosed_le ((continuous_realMatrixEntry 0 0).sub continuous_const).abs
    continuous_const).inter
    ((isClosed_le (continuous_realMatrixEntry 0 1).abs continuous_const).inter
      ((isClosed_le (continuous_realMatrixEntry 1 0).abs continuous_const).inter
        (isClosed_le ((continuous_realMatrixEntry 1 1).sub continuous_const).abs continuous_const)))

lemma isClosed_closeDiagonalFlowTimes (g : SL(2, ℝ)) (η : ℝ) :
    IsClosed (closeDiagonalFlowTimes g η) :=
  (isClosed_entryCloseOne η).preimage
    (((continuous_diagonalFlow.comp (continuous_apply 0).neg).mul continuous_const).mul
      (continuous_diagonalFlow.comp (continuous_apply 1)))

lemma isClosed_signedCloseDiagonalFlowTimes (g : SL(2, ℝ)) (η : ℝ) :
    IsClosed (signedCloseDiagonalFlowTimes g η) :=
  (isClosed_closeDiagonalFlowTimes g η).union (isClosed_closeDiagonalFlowTimes (-g) η)

lemma measurableSet_image_of_isClosed_sigmaCompact {X Y : Type*}
    [TopologicalSpace X] [SigmaCompactSpace X] [TopologicalSpace Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y] {f : X → Y} (hf : Continuous f)
    {E : Set X} (hE : IsClosed E) : MeasurableSet (f '' E) := by
  have hs := isSigmaCompact_univ.of_isClosed_subset hE (Set.subset_univ E)
  obtain ⟨K, hK, hcov⟩ := IsSigmaCompact.image hf hs
  rw [← hcov]
  exact MeasurableSet.iUnion (fun n => (hK n).measurableSet)

noncomputable def finPairFlowCurve (g h : SL(2, ℝ)) :
    (Fin 2 → ℝ) → ModularOrbitSpace × ModularOrbitSpace :=
  fun x => (modularFlowCurve g (x 0), modularFlowCurve h (x 1))

lemma continuous_finPairFlowCurve (g h : SL(2, ℝ)) : Continuous (finPairFlowCurve g h) :=
  ((continuous_modularFlowCurve g).comp (continuous_apply 0)).prodMk
    ((continuous_modularFlowCurve h).comp (continuous_apply 1))

lemma volume_finTwoArrow_image (E : Set (Fin 2 → ℝ)) :
    volume (MeasurableEquiv.finTwoArrow '' E) = volume E := by
  have h := (volume_preserving_finTwoArrow ℝ).measure_preimage_equiv
    (MeasurableEquiv.finTwoArrow '' E)
  rw [Set.preimage_image_eq _ MeasurableEquiv.finTwoArrow.injective] at h
  exact h.symm

theorem closedPair_image_le_parameterArea {g h : SL(2, ℝ)} {T U : ℝ}
    [Fact (0 < T)] [Fact (0 < U)] (hT : T ∈ flowPeriodGroup g) (hU : U ∈ flowPeriodGroup h)
    (hgenT : flowPeriodGroup g = AddSubgroup.zmultiples T)
    (hgenU : flowPeriodGroup h = AddSubgroup.zmultiples U)
    (E : Set (Fin 2 → ℝ)) (hE : MeasurableSet (finPairFlowCurve g h '' E)) :
    (closedOrbitMeasure hT).prod (closedOrbitMeasure hU)
      (finPairFlowCurve g h '' E) ≤ volume E := by
  have himage : pairFlowCurve g h '' (MeasurableEquiv.finTwoArrow '' E) =
      finPairFlowCurve g h '' E := by
    rw [Set.image_image]
    rfl
  have hbound := closedOrbitMeasure_prod_image_le hT hU hgenT hgenU
    (MeasurableEquiv.finTwoArrow '' E) (himage.symm ▸ hE)
  simpa only [himage, volume_finTwoArrow_image] using hbound

theorem closedPair_closeImage_le {g h : SL(2, ℝ)} {T U : ℝ}
    [Fact (0 < T)] [Fact (0 < U)] (hT : T ∈ flowPeriodGroup g) (hU : U ∈ flowPeriodGroup h)
    (hgenT : flowPeriodGroup g = AddSubgroup.zmultiples T)
    (hgenU : flowPeriodGroup h = AddSubgroup.zmultiples U)
    {d ℓ : ℤ} (hd : 0 < d) (hℓ : ℓ ≠ 2 * d) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 2)
    (hpair : (ℓ : ℝ) = (d : ℝ) * (2 + 4 * (g⁻¹ * h) 0 1 * (g⁻¹ * h) 1 0)) :
    (closedOrbitMeasure hT).prod (closedOrbitMeasure hU)
      (finPairFlowCurve g h '' signedCloseDiagonalFlowTimes (g⁻¹ * h) η) ≤
        ENNReal.ofReal (16 * η * Real.log (4 * (d : ℝ))) := by
  let E := signedCloseDiagonalFlowTimes (g⁻¹ * h) η
  have hmeas : MeasurableSet (finPairFlowCurve g h '' E) :=
    measurableSet_image_of_isClosed_sigmaCompact (continuous_finPairFlowCurve g h)
      (isClosed_signedCloseDiagonalFlowTimes (g⁻¹ * h) η)
  have hbound := closedPair_image_le_parameterArea hT hU hgenT hgenU E hmeas
  exact hbound.trans (volume_signedCloseDiagonalFlowTimes_le hd hℓ hη0 hη _ hpair)

end Erdos1148.DukeArithmetic
