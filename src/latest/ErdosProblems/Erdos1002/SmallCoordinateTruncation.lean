import ErdosProblems.Erdos1002.MarkedShotFunctional
import ErdosProblems.Erdos1002.ResonanceCellMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Removing a neighbourhood of the singular shot coordinate

The marked shot kernel is singular at `x = 0`.  For the continuous-mapping
argument one first keeps only points with `ε ≤ |x| ≤ A`.  This file proves
that the original finite shot and this annular truncation can differ only
when a primitive resonance lies in the explicit `|x| ≤ ε` union, and then
applies the previously proved cell-measure bound, including `p = 1`.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

local instance smallCoordinateTruncationPropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The finite marked shot with a deleted `ε`-neighbourhood of `x = 0`. -/
def annularMarkedShotFunctional
    (N : ℕ) (ε A : ℝ) (α : ℝ) : ℝ :=
  ∑ p ∈ Finset.Icc 1 N,
    if IsPrimitiveResonance p α ∧
        ε ≤ |scaledResonanceCoordinate N p α| ∧
        |scaledResonanceCoordinate N p α| ≤ A then
      markedShotKernel (markedResonancePoint N p α)
    else 0

theorem measurable_annularMarkedShotFunctional (N : ℕ) (ε A : ℝ) :
    Measurable (annularMarkedShotFunctional N ε A) := by
  classical
  unfold annularMarkedShotFunctional
  apply Finset.measurable_fun_sum
  intro p _hp
  apply Measurable.ite
  · exact (measurableSet_isPrimitiveResonance p).inter <|
      (measurableSet_le measurable_const
        (measurable_scaledResonanceCoordinate N p).abs).inter <|
      measurableSet_le (measurable_scaledResonanceCoordinate N p).abs measurable_const
  · exact measurable_markedShotKernel.comp (measurable_markedResonancePoint N p)
  · exact measurable_const

/-- On the unit interval, disagreement with the annular truncation forces a
primitive marked coordinate into the deleted `ε`-window. -/
theorem finiteShot_ne_annular_subset_smallCoordinateUnion
    (N : ℕ) (ε A : ℝ) :
    Ioo (0 : ℝ) 1 ∩
        {α | normalizedFiniteResonanceShotSum N A α ≠
          annularMarkedShotFunctional N ε A α} ⊆
      ⋃ p ∈ Finset.Icc 1 N, scaledPrimitiveResonanceBand N p ε := by
  intro α hα
  rcases hα with ⟨hunit, hne⟩
  change normalizedFiniteResonanceShotSum N A α ≠
    annularMarkedShotFunctional N ε A α at hne
  rw [normalizedFiniteResonanceShotSum_eq_markedFiniteShotFunctional] at hne
  by_cases hex : ∃ p ∈ Finset.Icc 1 N,
      IsPrimitiveResonance p α ∧
        |scaledResonanceCoordinate N p α| < ε
  · obtain ⟨p, hp, hprim, hsmall⟩ := hex
    rw [mem_iUnion]
    refine ⟨p, ?_⟩
    rw [mem_iUnion]
    refine ⟨hp, ?_⟩
    exact ⟨hunit, hprim, hsmall.le⟩
  · exfalso
    apply hne
    classical
    unfold markedFiniteShotFunctional annularMarkedShotFunctional
    apply Finset.sum_congr rfl
    intro p hp
    have hnotSmall : IsPrimitiveResonance p α →
        ε ≤ |scaledResonanceCoordinate N p α| := by
      intro hprim
      exact not_lt.mp (fun hlt ↦ hex ⟨p, hp, hprim, hlt⟩)
    by_cases hprim : IsPrimitiveResonance p α
    · by_cases hcut : |scaledResonanceCoordinate N p α| ≤ A
      · simp [hprim, hcut, hnotSmall hprim]
      · simp [hprim, hcut]
    · simp [hprim]

/-- Quantitative probability bound for deleting the singular-coordinate
window.  The right side is explicit and tends to `2 ε` as `N → ∞` at fixed
`ε`; no unspoken endpoint convention is used. -/
theorem uniform01Measure_real_finiteShot_ne_annular_le
    {N : ℕ} (hN : 2 ≤ N) {ε : ℝ} (hε : 0 ≤ ε) (A : ℝ) :
    uniform01Measure.real
        {α | normalizedFiniteResonanceShotSum N A α ≠
          annularMarkedShotFunctional N ε A α} ≤
      4 * ε / Real.log (N : ℝ) +
        (2 * ε / Real.log (N : ℝ)) * (1 + Real.log (N : ℝ)) := by
  let E : Set ℝ :=
    {α | normalizedFiniteResonanceShotSum N A α ≠
      annularMarkedShotFunctional N ε A α}
  let U : Set ℝ :=
    ⋃ p ∈ Finset.Icc 1 N, scaledPrimitiveResonanceBand N p ε
  have hE : MeasurableSet E := by
    have heq := measurableSet_eq_fun
      (measurable_normalizedFiniteResonanceShotSum N A)
      (measurable_annularMarkedShotFunctional N ε A)
    simpa only [E, ne_eq] using! heq.compl
  have hsub : Ioo (0 : ℝ) 1 ∩ E ⊆ U := by
    exact finiteShot_ne_annular_subset_smallCoordinateUnion N ε A
  have hUsub : U ⊆ Icc (0 : ℝ) 1 := by
    intro α hα
    dsimp [U] at hα
    simp only [mem_iUnion] at hα
    obtain ⟨p, _hp, hband⟩ := hα
    exact ⟨hband.1.1.le, hband.1.2.le⟩
  have hUne : volume U ≠ ⊤ := by
    apply measure_ne_top_of_subset hUsub
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  rw [uniform01Measure, measureReal_restrict_apply hE]
  calc
    volume.real (E ∩ Ioo (0 : ℝ) 1) =
        volume.real (Ioo (0 : ℝ) 1 ∩ E) := by rw [inter_comm]
    _ ≤ volume.real U := measureReal_mono hsub hUne
    _ ≤ 4 * ε / Real.log (N : ℝ) +
        (2 * ε / Real.log (N : ℝ)) * (1 + Real.log (N : ℝ)) :=
      volumeReal_scaledResonanceUnion_Icc_one_le hN hε

/-- The explicit right side of the deletion estimate. -/
def smallCoordinateDeletionBound (N : ℕ) (ε : ℝ) : ℝ :=
  4 * ε / Real.log (N : ℝ) +
    (2 * ε / Real.log (N : ℝ)) * (1 + Real.log (N : ℝ))

theorem smallCoordinateDeletionBound_eq
    {N : ℕ} (hN : 2 ≤ N) (ε : ℝ) :
    smallCoordinateDeletionBound N ε =
      2 * ε + 6 * ε / Real.log (N : ℝ) := by
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hN))
  unfold smallCoordinateDeletionBound
  field_simp
  ring

/-- At fixed window width, the complete finite-`N` deletion bound tends to
`2 ε`; both extra endpoint and harmonic-error terms are shown to vanish. -/
theorem tendsto_smallCoordinateDeletionBound (ε : ℝ) :
    Tendsto (fun N : ℕ ↦ smallCoordinateDeletionBound N ε)
      atTop (nhds (2 * ε)) := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hvanish : Tendsto (fun N : ℕ ↦ 6 * ε / Real.log (N : ℝ))
      atTop (nhds 0) := hlog.const_div_atTop (6 * ε)
  have hsum : Tendsto
      (fun N : ℕ ↦ 2 * ε + 6 * ε / Real.log (N : ℝ))
      atTop (nhds (2 * ε)) := by
    simpa only [add_zero] using! tendsto_const_nhds.add hvanish
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact (smallCoordinateDeletionBound_eq hN ε).symm

/-- Consequently, any tolerance strictly larger than `2 ε` eventually
dominates the probability that deletion changes the finite shot. -/
theorem eventually_uniform01Measure_real_finiteShot_ne_annular_lt
    {ε δ : ℝ} (hε : 0 ≤ ε) (hεδ : 2 * ε < δ) (A : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      uniform01Measure.real
          {α | normalizedFiniteResonanceShotSum N A α ≠
            annularMarkedShotFunctional N ε A α} < δ := by
  have hboundEventually : ∀ᶠ N : ℕ in atTop,
      smallCoordinateDeletionBound N ε < δ :=
    (tendsto_smallCoordinateDeletionBound ε)
      (Iio_mem_nhds hεδ)
  filter_upwards [eventually_ge_atTop 2, hboundEventually] with N hN hbound
  exact (uniform01Measure_real_finiteShot_ne_annular_le hN hε A).trans_lt hbound

end

end Erdos1002
