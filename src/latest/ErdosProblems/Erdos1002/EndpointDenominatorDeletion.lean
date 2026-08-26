import ErdosProblems.Erdos1002.ResonanceCellMeasure
import ErdosProblems.Erdos1002.ShotLaws
import ErdosProblems.Erdos1002.WeakPerturbation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Deleting the terminal denominator in the finite shot process

The continued-fraction point process in the manuscript is indexed by
`p < N`, whereas the finite shot sum is initially written with `p ≤ N`.
This file proves the comparison directly.  In particular, disagreement can
occur only on the single primitive resonance band with denominator `N`, whose
Lebesgue measure is bounded explicitly by

`(2 A / log N) * φ(N) / N²`.

Thus the endpoint convention is not hidden in an `O`-term.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

local instance endpointDenominatorDeletionPropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

local instance endpointDenominatorDeletionWeakTopology :
    TopologicalSpace (ProbabilityMeasure ℝ) :=
  ProbabilityMeasure.instTopologicalSpace

/-- The retained shot sum with the terminal denominator `p = N` omitted. -/
def finiteResonanceShotSumBefore (N : ℕ) (A : ℝ) (α : ℝ) : ℝ :=
  ∑ p ∈ Finset.Ico 1 N,
    if |scaledResonanceCoordinate N p α| ≤ A then primitiveShot N p α else 0

/-- The preceding sum with the manuscript's logarithmic normalization. -/
def normalizedFiniteResonanceShotSumBefore
    (N : ℕ) (A : ℝ) (α : ℝ) : ℝ :=
  finiteResonanceShotSumBefore N A α / Real.log (N : ℝ)

theorem measurable_finiteResonanceShotSumBefore (N : ℕ) (A : ℝ) :
    Measurable (finiteResonanceShotSumBefore N A) := by
  classical
  unfold finiteResonanceShotSumBefore
  apply Finset.measurable_fun_sum
  intro p _hp
  apply Measurable.ite
  · exact measurableSet_le
      (measurable_scaledResonanceCoordinate N p).abs measurable_const
  · exact measurable_primitiveShot N p
  · exact measurable_const

theorem measurable_normalizedFiniteResonanceShotSumBefore
    (N : ℕ) (A : ℝ) :
    Measurable (normalizedFiniteResonanceShotSumBefore N A) :=
  (measurable_finiteResonanceShotSumBefore N A).div_const _

/-- Law of the normalized finite shot with `p = N` omitted. -/
def finiteResonanceShotBeforeLaw (N : ℕ) (A : ℝ) : ProbabilityMeasure ℝ :=
  uniform01.map
    (measurable_normalizedFiniteResonanceShotSumBefore N A).aemeasurable

/-- Exact decomposition of the `p ≤ N` sum into the `p < N` sum and its
single terminal summand. -/
theorem finiteResonanceShotSum_eq_before_add_terminal
    {N : ℕ} (hN : 1 ≤ N) (A α : ℝ) :
    finiteResonanceShotSum N A α =
      finiteResonanceShotSumBefore N A α +
        (if |scaledResonanceCoordinate N N α| ≤ A then
          primitiveShot N N α else 0) := by
  classical
  have hIcc : Finset.Icc 1 N = insert N (Finset.Ico 1 N) := by
    ext p
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]
    omega
  have hNnot : N ∉ Finset.Ico 1 N := by simp
  unfold finiteResonanceShotSum finiteResonanceShotSumBefore
  rw [hIcc, Finset.sum_insert hNnot, add_comm]

/-- The scaled primitive resonance band is measurable. -/
theorem scaledPrimitiveResonanceBand_measurable (N p : ℕ) (A : ℝ) :
    MeasurableSet (scaledPrimitiveResonanceBand N p A) := by
  exact measurableSet_Ioo.inter <|
    (measurableSet_isPrimitiveResonance p).inter <|
      measurableSet_le
        (measurable_scaledResonanceCoordinate N p).abs measurable_const

/-- On the state space `(0,1)`, disagreement after deleting `p = N` forces
the terminal primitive resonance into the retained window. -/
theorem finiteShot_ne_before_subset_terminalBand
    {N : ℕ} (hN : 1 ≤ N) (A : ℝ) :
    Ioo (0 : ℝ) 1 ∩
        {α | normalizedFiniteResonanceShotSum N A α ≠
          normalizedFiniteResonanceShotSumBefore N A α} ⊆
      scaledPrimitiveResonanceBand N N A := by
  intro α hα
  rcases hα with ⟨hunit, hne⟩
  refine ⟨hunit, ?_⟩
  by_cases hcut : |scaledResonanceCoordinate N N α| ≤ A
  · refine ⟨?_, hcut⟩
    by_contra hprim
    apply hne
    rw [normalizedFiniteResonanceShotSum,
      finiteResonanceShotSum_eq_before_add_terminal hN A α,
      if_pos hcut, primitiveShot_of_not_primitive N N α hprim,
      add_zero, normalizedFiniteResonanceShotSumBefore]
  · exfalso
    apply hne
    rw [normalizedFiniteResonanceShotSum,
      finiteResonanceShotSum_eq_before_add_terminal hN A α,
      if_neg hcut, add_zero, normalizedFiniteResonanceShotSumBefore]

/-- Exact probability bound for deleting the terminal denominator. -/
theorem uniform01Measure_real_finiteShot_ne_before_le
    {N : ℕ} (hN : 2 ≤ N) {A : ℝ} (hA : 0 ≤ A) :
    uniform01Measure.real
        {α | normalizedFiniteResonanceShotSum N A α ≠
          normalizedFiniteResonanceShotSumBefore N A α} ≤
      (2 * A / Real.log (N : ℝ)) *
        ((Nat.totient N : ℝ) / (N : ℝ) ^ 2) := by
  let E : Set ℝ :=
    {α | normalizedFiniteResonanceShotSum N A α ≠
      normalizedFiniteResonanceShotSumBefore N A α}
  let B : Set ℝ := scaledPrimitiveResonanceBand N N A
  have hE : MeasurableSet E := by
    have heq := measurableSet_eq_fun
      (measurable_normalizedFiniteResonanceShotSum N A)
      (measurable_normalizedFiniteResonanceShotSumBefore N A)
    simpa only [E, ne_eq] using! heq.compl
  have hsub : Ioo (0 : ℝ) 1 ∩ E ⊆ B := by
    exact finiteShot_ne_before_subset_terminalBand (by omega) A
  have hBsub : B ⊆ Icc (0 : ℝ) 1 := by
    intro α hα
    exact ⟨hα.1.1.le, hα.1.2.le⟩
  have hBne : volume B ≠ ⊤ := by
    apply measure_ne_top_of_subset hBsub
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  rw [uniform01Measure, measureReal_restrict_apply hE]
  calc
    volume.real (E ∩ Ioo (0 : ℝ) 1) =
        volume.real (Ioo (0 : ℝ) 1 ∩ E) := by rw [inter_comm]
    _ ≤ volume.real B := measureReal_mono hsub hBne
    _ ≤ (2 * A / Real.log (N : ℝ)) *
        ((Nat.totient N : ℝ) / (N : ℝ) ^ 2) := by
      exact volumeReal_scaledPrimitiveResonanceBand_le hN hN hA

/-- A simpler majorant, making the vanishing of the endpoint error
transparent. -/
theorem uniform01Measure_real_finiteShot_ne_before_le_log
    {N : ℕ} (hN : 2 ≤ N) {A : ℝ} (hA : 0 ≤ A) :
    uniform01Measure.real
        {α | normalizedFiniteResonanceShotSum N A α ≠
          normalizedFiniteResonanceShotSumBefore N A α} ≤
      2 * A / Real.log (N : ℝ) := by
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have htot : (Nat.totient N : ℝ) / (N : ℝ) ^ 2 ≤ 1 := by
    have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
    have hφ : (Nat.totient N : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast totient_le_self N
    have hsq : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    exact (div_le_one (sq_pos_of_pos (by positivity))).mpr (hφ.trans hsq)
  exact (uniform01Measure_real_finiteShot_ne_before_le hN hA).trans <| by
    have hfactor : 0 ≤ 2 * A / Real.log (N : ℝ) := by positivity
    nlinarith

/-- The sharper estimate quoted in the manuscript: the terminal term has
probability at most `2 A / (N log N)`. -/
theorem uniform01Measure_real_finiteShot_ne_before_le_nat_log
    {N : ℕ} (hN : 2 ≤ N) {A : ℝ} (hA : 0 ≤ A) :
    uniform01Measure.real
        {α | normalizedFiniteResonanceShotSum N A α ≠
          normalizedFiniteResonanceShotSumBefore N A α} ≤
      2 * A / ((N : ℝ) * Real.log (N : ℝ)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have hφ : (Nat.totient N : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast totient_le_self N
  have hratio : (Nat.totient N : ℝ) / (N : ℝ) ^ 2 ≤
      1 / (N : ℝ) := by
    calc
      (Nat.totient N : ℝ) / (N : ℝ) ^ 2 ≤
          (N : ℝ) / (N : ℝ) ^ 2 := by
        exact div_le_div_of_nonneg_right hφ (sq_nonneg (N : ℝ))
      _ = 1 / (N : ℝ) := by field_simp
  calc
    uniform01Measure.real
        {α | normalizedFiniteResonanceShotSum N A α ≠
          normalizedFiniteResonanceShotSumBefore N A α} ≤
        (2 * A / Real.log (N : ℝ)) *
          ((Nat.totient N : ℝ) / (N : ℝ) ^ 2) :=
      uniform01Measure_real_finiteShot_ne_before_le hN hA
    _ ≤ (2 * A / Real.log (N : ℝ)) * (1 / (N : ℝ)) := by
      gcongr
    _ = 2 * A / ((N : ℝ) * Real.log (N : ℝ)) := by
      field_simp

/-- For every fixed cutoff, deleting `p = N` changes the finite shot with
probability tending to zero. -/
theorem tendsto_uniform01Measure_real_finiteShot_ne_before
    (A : ℝ) (hA : 0 ≤ A) :
    Tendsto
      (fun N : ℕ ↦ uniform01Measure.real
        {α | normalizedFiniteResonanceShotSum N A α ≠
          normalizedFiniteResonanceShotSumBefore N A α})
      atTop (nhds 0) := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun N : ℕ ↦ 2 * A / Real.log (N : ℝ))
      atTop (nhds 0) := hlog.const_div_atTop (2 * A)
  apply squeeze_zero'
  · exact Eventually.of_forall fun _N ↦ measureReal_nonneg
  · filter_upwards [eventually_ge_atTop 2] with N hN
    exact uniform01Measure_real_finiteShot_ne_before_le_log hN hA
  · exact hupper

/-- Deleting the terminal denominator is a vanishing perturbation in
probability, not merely an equality outside an unspecified exceptional
set. -/
theorem tendstoInMeasure_finiteShot_sub_before
    (A : ℝ) (hA : 0 ≤ A) :
    TendstoInMeasure uniform01Measure
      (fun N α ↦ normalizedFiniteResonanceShotSum N A α -
        normalizedFiniteResonanceShotSumBefore N A α)
      atTop 0 := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro r hr
  let D : ℕ → Set ℝ := fun N ↦
    {α | normalizedFiniteResonanceShotSum N A α ≠
      normalizedFiniteResonanceShotSumBefore N A α}
  have hD : Tendsto (fun N ↦ uniform01Measure.real (D N))
      atTop (nhds 0) := by
    simpa only [D] using!
      tendsto_uniform01Measure_real_finiteShot_ne_before A hA
  apply squeeze_zero'
  · exact Eventually.of_forall fun _N ↦ measureReal_nonneg
  · exact Eventually.of_forall fun N ↦ by
      apply measureReal_mono
      · intro α hα
        simp only [Pi.zero_apply, sub_zero] at hα
        change r ≤
          ‖normalizedFiniteResonanceShotSum N A α -
            normalizedFiniteResonanceShotSumBefore N A α‖ at hα
        change normalizedFiniteResonanceShotSum N A α ≠
          normalizedFiniteResonanceShotSumBefore N A α
        intro heq
        rw [heq, sub_self, norm_zero] at hα
        linarith
      · exact measure_ne_top _ _
  · exact hD

/-- Consequently, a weak limit proved for the `p < N` convention is exactly
the weak limit of the manuscript's `p ≤ N` finite shot law. -/
theorem tendsto_finiteResonanceShotLaw_of_before
    (A : ℝ) (hA : 0 ≤ A) (ν : ProbabilityMeasure ℝ)
    (hbefore : Tendsto (fun N ↦ finiteResonanceShotBeforeLaw N A)
      atTop
      (@nhds (ProbabilityMeasure ℝ)
        endpointDenominatorDeletionWeakTopology ν)) :
    Tendsto (fun N ↦ finiteResonanceShotLaw N A)
      atTop
      (@nhds (ProbabilityMeasure ℝ)
        endpointDenominatorDeletionWeakTopology ν) := by
  refine tendsto_map_of_tendsto_map_of_tendstoInMeasure_sub
    (μ := uniform01Measure)
    (fun N ↦ normalizedFiniteResonanceShotSumBefore N A)
    (fun N ↦ normalizedFiniteResonanceShotSum N A) ν ?_ ?_ ?_ ?_
  · intro N
    exact (measurable_normalizedFiniteResonanceShotSumBefore N A).aemeasurable
  · intro N
    exact (measurable_normalizedFiniteResonanceShotSum N A).aemeasurable
  · simpa [finiteResonanceShotBeforeLaw, uniform01] using! hbefore
  · simpa only [Pi.sub_apply] using! tendstoInMeasure_finiteShot_sub_before A hA

end

end Erdos1002
