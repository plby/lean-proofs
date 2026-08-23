import ErdosProblems.Erdos1166.Erdos1166HLOZBandRatios
import ErdosProblems.Erdos1166.Erdos1166HLOZProp48Truncated

/-!
# The one-coordinate estimate in HLOZ Proposition 4.9

This file connects the checked finite-sum comparison (4.58) to the literal
truncated negative-binomial coordinate law obtained from the stopped-path
decomposition.  In particular, the conditioning denominator is bounded
below by the mass of the broad cell; no conditional probability estimate is
left as a premise.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace Erdos1166.HLOZProp49Coordinate

open HLOZUrn HLOZBandRatios HLOZProp48Truncated HLOZLemma412Windows

/-- Translate a finite band of total local times into lazy-coordinate values. -/
def shiftedBand (i : ℕ) (A : Finset ℕ) : Finset ℕ :=
  A.image fun j ↦ j - i

/-- The literal lazy-coordinate version of the narrow top band in (4.58). -/
noncomputable def sourceProp49NarrowBand (m i : ℕ) (alpha : ℝ) : Set ℕ :=
  ↑(shiftedBand i (openTopBand m
    (sourceNarrowWidth m (alpha + HLOZProp47Parameters.delta))))

lemma measurableSet_sourceProp49NarrowBand (m i : ℕ) (alpha : ℝ) :
    MeasurableSet (sourceProp49NarrowBand m i alpha) :=
  MeasurableSet.of_discrete

lemma shiftedBand_mass
    (i : ℕ) (A : Finset ℕ) (hA : ∀ j ∈ A, i ≤ j) :
    (negBinMeasure i).real (↑(shiftedBand i A) : Set ℕ) =
      bandMass (barNegBinMass i) A := by
  rw [← sum_measureReal_singleton]
  unfold shiftedBand bandMass
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [negBinMeasure_real_singleton]
    rfl
  · intro a ha b hb hab
    have ha' := hA a ha
    have hb' := hA b hb
    change a - i = b - i at hab
    omega

lemma shiftedBand_subset_sourceBelow
    (m i : ℕ) (A : Finset ℕ)
    (hiA : ∀ j ∈ A, i ≤ j) (hAm : ∀ j ∈ A, j < m) :
    (↑(shiftedBand i A) : Set ℕ) ⊆ sourceBelowSet m i := by
  intro k hk
  change k ∈ shiftedBand i A at hk
  simp only [shiftedBand, Finset.mem_image] at hk
  rcases hk with ⟨j, hj, rfl⟩
  simp only [sourceBelowSet, Set.mem_ofPred_eq]
  have hij := hiA j hj
  have hjm := hAm j hj
  omega

lemma sourceTruncatedNegBinMeasure_shiftedBand_real_le_bandRatio
    (m i : ℕ) (narrow broad : Finset ℕ)
    (hiN : ∀ j ∈ narrow, i ≤ j) (hNm : ∀ j ∈ narrow, j < m)
    (hiB : ∀ j ∈ broad, i ≤ j) (hBm : ∀ j ∈ broad, j < m)
    (hBpos : 0 < bandMass (barNegBinMass i) broad) :
    (sourceTruncatedNegBinMeasure m i).real
        (↑(shiftedBand i narrow) : Set ℕ) ≤
      bandRatio (barNegBinMass i) narrow broad := by
  have hNsub := shiftedBand_subset_sourceBelow m i narrow hiN hNm
  have hBsub := shiftedBand_subset_sourceBelow m i broad hiB hBm
  have hNnonneg : 0 ≤ bandMass (barNegBinMass i) narrow :=
    bandMass_nonneg (fun j ↦ negBinMass_nonneg i (j - i)) narrow
  have hBmeasure : bandMass (barNegBinMass i) broad ≤
      (negBinMeasure i).real (sourceBelowSet m i) := by
    rw [← shiftedBand_mass i broad hiB]
    exact measureReal_mono hBsub
  have hcond :
      (sourceTruncatedNegBinMeasure m i).real
          (↑(shiftedBand i narrow) : Set ℕ) =
        bandMass (barNegBinMass i) narrow /
          (negBinMeasure i).real (sourceBelowSet m i) := by
    rw [sourceTruncatedNegBinMeasure, measureReal_def,
      cond_apply (measurableSet_sourceBelowSet m i)]
    have hinter : sourceBelowSet m i ∩ (↑(shiftedBand i narrow) : Set ℕ) =
        (↑(shiftedBand i narrow) : Set ℕ) := Set.inter_eq_right.mpr hNsub
    rw [hinter, ENNReal.toReal_mul, ENNReal.toReal_inv]
    change ((negBinMeasure i).real (sourceBelowSet m i))⁻¹ *
        (negBinMeasure i).real (↑(shiftedBand i narrow) : Set ℕ) = _
    rw [shiftedBand_mass i narrow hiN]
    simp only [div_eq_mul_inv, mul_comm]
  rw [hcond, bandRatio]
  exact div_le_div_of_nonneg_left hNnonneg hBpos hBmeasure

lemma sourceTruncatedNegBinMeasure_shiftedBand_le_bandRatio
    (m i : ℕ) (narrow broad : Finset ℕ)
    (hiN : ∀ j ∈ narrow, i ≤ j) (hNm : ∀ j ∈ narrow, j < m)
    (hiB : ∀ j ∈ broad, i ≤ j) (hBm : ∀ j ∈ broad, j < m)
    (hBpos : 0 < bandMass (barNegBinMass i) broad) :
    sourceTruncatedNegBinMeasure m i
        (↑(shiftedBand i narrow) : Set ℕ) ≤
      ENNReal.ofReal (bandRatio (barNegBinMass i) narrow broad) := by
  have hBmeasure : bandMass (barNegBinMass i) broad ≤
      (negBinMeasure i).real (sourceBelowSet m i) := by
    rw [← shiftedBand_mass i broad hiB]
    exact measureReal_mono
      (shiftedBand_subset_sourceBelow m i broad hiB hBm)
  have hbelow : negBinMeasure i (sourceBelowSet m i) ≠ 0 := by
    intro hzero
    have hreal : (negBinMeasure i).real (sourceBelowSet m i) = 0 := by
      rw [measureReal_def, hzero]
      simp
    rw [hreal] at hBmeasure
    linarith
  letI : IsProbabilityMeasure (sourceTruncatedNegBinMeasure m i) :=
    ProbabilityTheory.cond_isProbabilityMeasure hbelow
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal
    (sourceTruncatedNegBinMeasure_shiftedBand_real_le_bandRatio
      m i narrow broad hiN hNm hiB hBm hBpos)

lemma equation458_profile_bounds (c m i : ℕ)
    (hgrowth : SourceWindowGrowth c m)
    (hiwin : InEquation458ExternalWindow c m i) :
    1 ≤ i ∧ i ≤ m - sourceCellWidth m := by
  rcases hgrowth with ⟨hm, hdev, hgap, hlarge, hscale⟩
  unfold InEquation458ExternalWindow at hiwin
  have hcell : 1 ≤ sourceCellWidth m :=
    HLOZProp48SourceBands.sourceCellWidth_pos m hm
  omega

lemma openTopBand_bandMass_pos (c m i : ℕ)
    (hgrowth : SourceWindowGrowth c m)
    (hiwin : InEquation458ExternalWindow c m i) :
    0 < bandMass (barNegBinMass i) (openTopBand m (sourceCellWidth m)) := by
  have hibounds := equation458_profile_bounds c m i hgrowth hiwin
  have hwidth : 2 ≤ sourceCellWidth m := by
    rcases hgrowth with ⟨hm, hdev, hgap, hlarge, hscale⟩
    have hmLarge : 2 ≤ m := by
      have hcell := HLOZProp48SourceBands.sourceCellWidth_pos m hm
      omega
    unfold sourceCellWidth
    rw [← Nat.lt_iff_add_one_le, Nat.lt_ceil]
    norm_num only [Nat.cast_one]
    exact Real.one_lt_rpow
      (show (1 : ℝ) < (m : ℝ) by exact_mod_cast (show 1 < m by omega))
      HLOZLemma412Windows.kappaOne_pos
  unfold bandMass
  apply Finset.sum_pos
  · intro j hj
    exact HLOZProp48SourceBands.negBinMass_pos i (j - i) hibounds.1
  · refine ⟨m - 1, ?_⟩
    rw [openTopBand, Finset.mem_Ico]
    rcases hgrowth with ⟨hm, hdev, hgap, hlarge, hscale⟩
    omega

/-- Equation (4.58) for the actual truncated coordinate law. -/
theorem sourceTruncatedNegBinMeasure_equation458_le
    (c m i : ℕ) (α : ℝ)
    (hgrowth : SourceWindowGrowth c m)
    (hiwin : InEquation458ExternalWindow c m i)
    (hα0 : 0 ≤ α) (hα : α < HLOZProp47Parameters.kappaOne) :
    sourceTruncatedNegBinMeasure m i
        (↑(shiftedBand i (openTopBand m (sourceNarrowWidth m α))) : Set ℕ) ≤
      HLOZFiniteUnion.polynomialBandRatio
        (4 * Real.exp (sourceComparisonExponent c))
          HLOZProp47Parameters.kappaOne α m := by
  have hibounds := equation458_profile_bounds c m i hgrowth hiwin
  have hnle : sourceNarrowWidth m α ≤ sourceCellWidth m :=
    sourceNarrowWidth_le_cell m hgrowth.1 hα.le
  have hiN : ∀ j ∈ openTopBand m (sourceNarrowWidth m α), i ≤ j := by
    intro j hj
    rw [openTopBand, Finset.mem_Ico] at hj
    have hlower : m - sourceCellWidth m ≤
        m - sourceNarrowWidth m α + 1 := by omega
    exact hibounds.2.trans (hlower.trans hj.1)
  have hNm : ∀ j ∈ openTopBand m (sourceNarrowWidth m α), j < m := by
    intro j hj
    exact (Finset.mem_Ico.mp hj).2
  have hiB : ∀ j ∈ openTopBand m (sourceCellWidth m), i ≤ j := by
    intro j hj
    rw [openTopBand, Finset.mem_Ico] at hj
    exact hibounds.2.trans (by omega)
  have hBm : ∀ j ∈ openTopBand m (sourceCellWidth m), j < m := by
    intro j hj
    exact (Finset.mem_Ico.mp hj).2
  exact (sourceTruncatedNegBinMeasure_shiftedBand_le_bandRatio
    m i (openTopBand m (sourceNarrowWidth m α))
      (openTopBand m (sourceCellWidth m)) hiN hNm hiB hBm
      (openTopBand_bandMass_pos c m i hgrowth hiwin)).trans
    (equation458_bandRatio_le_polynomialBandRatio c m i α
      hgrowth hiwin hα0 hα)

lemma natCast_rpow_neg_le_two_mul_add_one_rpow_neg
    (m : ℕ) (s : ℝ) (hm : 1 ≤ m) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (m : ℝ≥0∞) ^ (-s) ≤
      2 * ((m : ℝ≥0∞) + 1) ^ (-s) := by
  have hbase : (m : ℝ≥0∞) + 1 ≤ 2 * (m : ℝ≥0∞) := by
    exact_mod_cast (show m + 1 ≤ 2 * m by omega)
  have hpow : ((m : ℝ≥0∞) + 1) ^ s ≤
      2 * (m : ℝ≥0∞) ^ s := by
    calc
      ((m : ℝ≥0∞) + 1) ^ s ≤ (2 * (m : ℝ≥0∞)) ^ s :=
        ENNReal.rpow_le_rpow hbase hs0
      _ = (2 : ℝ≥0∞) ^ s * (m : ℝ≥0∞) ^ s := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hs0]
      _ ≤ 2 * (m : ℝ≥0∞) ^ s := by
        simpa using mul_le_mul_left
          (ENNReal.rpow_le_rpow_of_exponent_le
            (show (1 : ℝ≥0∞) ≤ 2 by norm_num) hs1) ((m : ℝ≥0∞) ^ s)
  rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
  have hApos : 0 < (m : ℝ≥0∞) ^ s :=
    ENNReal.rpow_pos (by exact_mod_cast (show 0 < m by omega)) (by simp)
  have hAfin : (m : ℝ≥0∞) ^ s ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hs0 (by simp)
  have hBpos : 0 < ((m : ℝ≥0∞) + 1) ^ s :=
    ENNReal.rpow_pos (by positivity) (by simp)
  have hBfin : ((m : ℝ≥0∞) + 1) ^ s ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hs0 (by simp)
  rw [← one_mul (((m : ℝ≥0∞) ^ s)⁻¹),
    ENNReal.mul_inv_le_iff hApos.ne' hAfin]
  calc
    1 = (((m : ℝ≥0∞) + 1) ^ s)⁻¹ *
        ((m : ℝ≥0∞) + 1) ^ s :=
      (ENNReal.inv_mul_cancel hBpos.ne' hBfin).symm
    _ ≤ (((m : ℝ≥0∞) + 1) ^ s)⁻¹ *
        (2 * (m : ℝ≥0∞) ^ s) := mul_le_mul_right hpow _
    _ = (2 * (((m : ℝ≥0∞) + 1) ^ s)⁻¹) *
        (m : ℝ≥0∞) ^ s := by ac_rfl

/-- Source (4.58), normalized to the `m+1` convention used downstream.
The factor two pays only for replacing `m` by `m+1`. -/
theorem sourceTruncatedNegBinMeasure_prop49CoordinateRate
    (c m i A : ℕ) (alpha : ℝ)
    (hgrowth : SourceWindowGrowth c m)
    (hiwin : InEquation458ExternalWindow c m i)
    (halpha0 : 0 ≤ alpha + HLOZProp47Parameters.delta)
    (halpha : alpha + HLOZProp47Parameters.delta <
      HLOZProp47Parameters.kappaOne)
    (hcoeff : 8 * Real.exp (sourceComparisonExponent c) ≤ A) :
    sourceTruncatedNegBinMeasure m i
        (↑(shiftedBand i
          (openTopBand m (sourceNarrowWidth m
            (alpha + HLOZProp47Parameters.delta)))) : Set ℕ) ≤
      (A : ℝ≥0∞) * ((m : ℝ≥0∞) + 1) ^
        (-(HLOZProp47Parameters.kappaOne -
          (alpha + HLOZProp47Parameters.delta))) := by
  have hband := sourceTruncatedNegBinMeasure_equation458_le
    c m i (alpha + HLOZProp47Parameters.delta) hgrowth hiwin halpha0 halpha
  apply hband.trans
  let s : ℝ := HLOZProp47Parameters.kappaOne -
    (alpha + HLOZProp47Parameters.delta)
  have hs0 : 0 ≤ s := by dsimp [s]; linarith
  have hs1 : s ≤ 1 := by
    dsimp [s]
    norm_num [HLOZProp47Parameters.kappaOne]
    linarith [halpha0]
  have hbase := natCast_rpow_neg_le_two_mul_add_one_rpow_neg
    m s hgrowth.1 hs0 hs1
  have hCnonneg : 0 ≤ 4 * Real.exp (sourceComparisonExponent c) := by positivity
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (show 0 < m from lt_of_lt_of_le Nat.zero_lt_one hgrowth.1)
  have hpoly :
      HLOZFiniteUnion.polynomialBandRatio
          (4 * Real.exp (sourceComparisonExponent c))
          HLOZProp47Parameters.kappaOne
          (alpha + HLOZProp47Parameters.delta) m =
        ENNReal.ofReal (4 * Real.exp (sourceComparisonExponent c)) *
          (m : ℝ≥0∞) ^ (-s) := by
    rw [HLOZFiniteUnion.polynomialBandRatio,
      ENNReal.ofReal_mul hCnonneg,
      ← ENNReal.ofReal_rpow_of_pos hmpos,
      ENNReal.ofReal_natCast]
    congr 2
    dsimp [s]
    ring
  rw [hpoly]
  calc
    ENNReal.ofReal (4 * Real.exp (sourceComparisonExponent c)) *
        (m : ℝ≥0∞) ^
          (-(HLOZProp47Parameters.kappaOne -
            (alpha + HLOZProp47Parameters.delta))) ≤
      ENNReal.ofReal (4 * Real.exp (sourceComparisonExponent c)) *
        (2 * ((m : ℝ≥0∞) + 1) ^
          (-(HLOZProp47Parameters.kappaOne -
            (alpha + HLOZProp47Parameters.delta)))) := by
      exact mul_le_mul_right hbase _
    _ = ENNReal.ofReal (8 * Real.exp (sourceComparisonExponent c)) *
        ((m : ℝ≥0∞) + 1) ^
          (-(HLOZProp47Parameters.kappaOne -
            (alpha + HLOZProp47Parameters.delta))) := by
      rw [← mul_assoc]
      congr 1
      calc
        ENNReal.ofReal (4 * Real.exp (sourceComparisonExponent c)) * 2 =
            ENNReal.ofReal (4 * Real.exp (sourceComparisonExponent c)) *
              ENNReal.ofReal (2 : ℝ) := by norm_num
        _ = ENNReal.ofReal
            ((4 * Real.exp (sourceComparisonExponent c)) * 2) :=
          (ENNReal.ofReal_mul hCnonneg).symm
        _ = ENNReal.ofReal (8 * Real.exp (sourceComparisonExponent c)) := by
          congr 1
          ring
    _ ≤ (A : ℝ≥0∞) * ((m : ℝ≥0∞) + 1) ^
          (-(HLOZProp47Parameters.kappaOne -
            (alpha + HLOZProp47Parameters.delta))) := by
      gcongr
      simpa using ENNReal.ofReal_le_ofReal hcoeff

/-- Named form of the preceding theorem at the canonical narrow band. -/
theorem sourceTruncatedNegBinMeasure_sourceProp49NarrowBand_le
    (c m i A : ℕ) (alpha : ℝ)
    (hgrowth : SourceWindowGrowth c m)
    (hiwin : InEquation458ExternalWindow c m i)
    (halpha0 : 0 ≤ alpha + HLOZProp47Parameters.delta)
    (halpha : alpha + HLOZProp47Parameters.delta <
      HLOZProp47Parameters.kappaOne)
    (hcoeff : 8 * Real.exp (sourceComparisonExponent c) ≤ A) :
    sourceTruncatedNegBinMeasure m i (sourceProp49NarrowBand m i alpha) ≤
      (A : ℝ≥0∞) * ((m : ℝ≥0∞) + 1) ^
        (-(HLOZProp47Parameters.kappaOne -
          (alpha + HLOZProp47Parameters.delta))) := by
  exact sourceTruncatedNegBinMeasure_prop49CoordinateRate
    c m i A alpha hgrowth hiwin halpha0 halpha hcoeff

end Erdos1166.HLOZProp49Coordinate
