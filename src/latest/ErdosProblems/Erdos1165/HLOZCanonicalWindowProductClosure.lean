/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZAllSixLocalCLTProductClosure

/-!
# Canonical-window all-six product screening

This file removes the finite local-CLT geometry fields from the all-six
product interface.  Every away coordinate uses the consecutive canonical
windows from `ScreeningInstantiation`; their nonemptiness, equal cardinality,
moderate-deviation bounds, and mutual separation are checked lemmas.

The remaining data are literal stopped-fibre semantics and cap containment.
For a premise-free finite envelope we use the conservative bound `2^bound`.
Sharper asymptotic applications may replace this envelope after proving the
corresponding HLOZ scale estimate, without changing the path disintegration.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZCanonicalWindowProductClosure

open FiniteDominoProductLaw HLOZAllSixBandProductClosure
open HLOZAllSixExactCoordinateProductClosure
open HLOZAllSixLocalCLTProductClosure
open HLOZAllSixStoppedOnePointInstantiation
open HLOZGapRandomClockScreen HLOZProposition48Candidates
open NearFavoriteThresholded NegativeBinomialLocalCLT
open ScreeningInstantiation TilingAwayNegativeBinomial
open TilingCappedMarginalization TilingSpatialInsertionFiber

noncomputable section

/-- A uniform finite envelope that requires no asymptotic arithmetic. -/
noncomputable def canonicalCrudeProductCost (bound : ℕ) : ℝ :=
  (2 : ℝ) ^ bound

lemma canonicalCrudeProductCost_nonneg (bound : ℕ) :
    0 ≤ canonicalCrudeProductCost bound := by
  exact pow_nonneg (by norm_num) bound

/-- The heterogeneous fixed-total factor is always bounded by `2^bound`.
This estimate uses only nonnegativity of the local mass-ratio constant. -/
lemma productEnvelope_le_canonicalCrudeProductCost
    (C : ℝ) (hC : 0 ≤ C) (threshold : ℕ → ℕ)
    (G j bound total : ℕ) (htotal : total < bound + 1) :
    (1 + C / (1 + C)) ^ total /
        (2 : ℝ) ^ thresholdedGrowthCut threshold G j total ≤
      canonicalCrudeProductCost bound := by
  have hden : (1 : ℝ) ≤
      (2 : ℝ) ^ thresholdedGrowthCut threshold G j total :=
    one_le_pow₀ (by norm_num)
  have hCden : 0 < 1 + C := by linarith
  have hratio : C / (1 + C) ≤ 1 := (div_le_one hCden).2 (by linarith)
  have hbase0 : 0 ≤ 1 + C / (1 + C) := by positivity
  have hbase2 : 1 + C / (1 + C) ≤ 2 := by linarith
  have hpow : (1 + C / (1 + C)) ^ total ≤ (2 : ℝ) ^ total :=
    pow_le_pow_left₀ hbase0 hbase2 total
  have htotalBound : total ≤ bound := by omega
  calc
    (1 + C / (1 + C)) ^ total /
          (2 : ℝ) ^ thresholdedGrowthCut threshold G j total ≤
        (1 + C / (1 + C)) ^ total :=
      div_le_self (pow_nonneg hbase0 total) hden
    _ ≤ (2 : ℝ) ^ total := hpow
    _ ≤ (2 : ℝ) ^ bound := by
      exact pow_le_pow_right₀ (by norm_num) htotalBound
    _ = canonicalCrudeProductCost bound := rfl

/-- Literal stopped-fibre data for the canonical consecutive windows.  No
local-CLT estimate is a field: the only hypotheses identify the path screen
and state that the two displayed finite windows lie below the literal caps. -/
structure TilingCanonicalWindowTailData {index : Type*}
    (piece : index → Set WalkPath) (next : Set WalkPath)
    (threshold : ℕ → ℕ) (G j bound : ℕ) where
  factored : TilingFactoredStoppedCoordinateData piece next (1 : ℝ≥0∞)
  accepts_iff : ∀ z cap ell,
    factored.accepts z cap ell = true ↔
      randomTotalThresholdedUpperTail
        (fun b (v : Fin (factored.upper z cap b)) ↦
          (v : ℕ) ∈ upperFailureWindow
            (Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
              (factored.start z cap) (factored.retained z cap) b.1))
            (canonicalWindowWidth
              (Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
                (factored.start z cap) (factored.retained z cap) b.1))))
        (fun b (v : Fin (factored.upper z cap b)) ↦
          (v : ℕ) ∈ lowerFailureWindow
            (Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
              (factored.start z cap) (factored.retained z cap) b.1))
            (canonicalWindowWidth
              (Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
                (factored.start z cap) (factored.retained z cap) b.1))))
        threshold G j bound ell
  upper_lt_truncation : ∀ z cap b v,
    v ∈ upperFailureWindow
        (Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
          (factored.start z cap) (factored.retained z cap) b.1))
        (canonicalWindowWidth
          (Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
            (factored.start z cap) (factored.retained z cap) b.1))) →
      v < factored.upper z cap b
  lower_lt_truncation : ∀ z cap b v,
    v ∈ lowerFailureWindow
        (Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
          (factored.start z cap) (factored.retained z cap) b.1))
        (canonicalWindowWidth
          (Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
            (factored.start z cap) (factored.retained z cap) b.1))) →
      v < factored.upper z cap b
  upper_le_cap : ∀ z cap
    (b : TilingAwayDomino (factored.tiling z cap) (factored.start z cap)
      (factored.retained z cap) (factored.distinguished z cap)) v,
    v ∈ upperFailureWindow
        (Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
          (factored.start z cap) (factored.retained z cap) b.1))
        (canonicalWindowWidth
          (Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
            (factored.start z cap) (factored.retained z cap) b.1))) →
      v ≤ cap
  lower_le_cap : ∀ z cap
    (b : TilingAwayDomino (factored.tiling z cap) (factored.start z cap)
      (factored.retained z cap) (factored.distinguished z cap)) v,
    v ∈ lowerFailureWindow
        (Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
          (factored.start z cap) (factored.retained z cap) b.1))
        (canonicalWindowWidth
          (Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
            (factored.start z cap) (factored.retained z cap) b.1))) →
      v ≤ cap
  coordinate_count_ge : ∀ z cap
    (b : TilingAwayDomino (factored.tiling z cap) (factored.start z cap)
      (factored.retained z cap) (factored.distinguished z cap)),
    120 ≤ Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
      (factored.start z cap) (factored.retained z cap) b.1)

/-- Insert all deterministic canonical-window facts, including the finite
envelope, into the local-CLT product datum. -/
noncomputable def localCLTTailDataOfCanonicalWindowData
    {index : Type*} {piece : index → Set WalkPath} {next : Set WalkPath}
    {threshold : ℕ → ℕ} {G j bound : ℕ}
    (data : TilingCanonicalWindowTailData piece next threshold G j bound) :
    TilingLocalCLTRandomTotalTailData piece next threshold G j bound
      (canonicalCrudeProductCost bound) where
  factored := data.factored
  upperWindow := fun z cap b ↦
    upperFailureWindow
      (Fintype.card (TilingCoordinatesAt (data.factored.tiling z cap)
        (data.factored.start z cap) (data.factored.retained z cap) b.1))
      (canonicalWindowWidth
        (Fintype.card (TilingCoordinatesAt (data.factored.tiling z cap)
          (data.factored.start z cap) (data.factored.retained z cap) b.1)))
  lowerWindow := fun z cap b ↦
    lowerFailureWindow
      (Fintype.card (TilingCoordinatesAt (data.factored.tiling z cap)
        (data.factored.start z cap) (data.factored.retained z cap) b.1))
      (canonicalWindowWidth
        (Fintype.card (TilingCoordinatesAt (data.factored.tiling z cap)
          (data.factored.start z cap) (data.factored.retained z cap) b.1)))
  accepts_iff := data.accepts_iff
  windows_disjoint := by
    intro z cap b
    rw [Finset.disjoint_left]
    intro v hvUpper hvLower
    rw [upperFailureWindow, Finset.mem_Ico] at hvUpper
    rw [lowerFailureWindow, Finset.mem_Ico] at hvLower
    omega
  upper_lt_truncation := data.upper_lt_truncation
  lower_lt_truncation := data.lower_lt_truncation
  upper_le_cap := data.upper_le_cap
  lower_le_cap := data.lower_le_cap
  coordinate_count_pos := by
    intro z cap b
    exact (canonicalWindowWidth_numeric
      (data.coordinate_count_ge z cap b)).1
  deviationRadius := fun z cap b ↦
    adjacentWindowRadius
      (canonicalWindowWidth
        (Fintype.card (TilingCoordinatesAt (data.factored.tiling z cap)
          (data.factored.start z cap) (data.factored.retained z cap) b.1)))
  windowSeparation := fun z cap b ↦
    adjacentWindowSeparation
      (canonicalWindowWidth
        (Fintype.card (TilingCoordinatesAt (data.factored.tiling z cap)
          (data.factored.start z cap) (data.factored.retained z cap) b.1)))
  deviationRadius_nonneg := by
    intro z cap b
    exact adjacentWindowRadius_nonneg _
  windowSeparation_nonneg := by
    intro z cap b
    exact adjacentWindowSeparation_nonneg _
  moderate := by
    intro z cap b
    exact adjacentWindowRadius_le_thirtieth
      (canonicalWindowWidth_numeric (data.coordinate_count_ge z cap b)).2.2
  lower_nonempty := by
    intro z cap b
    exact lowerFailureWindow_nonempty
      (canonicalWindowWidth_numeric (data.coordinate_count_ge z cap b)).2.1
  window_card := by
    intro z cap b
    rw [upperFailureWindow_card, lowerFailureWindow_card]
  upper_deviation := by
    intro z cap b v hv
    exact upperFailureWindow_deviation_le hv
  lower_deviation := by
    intro z cap b v hv
    exact lowerFailureWindow_deviation_le hv
  pair_deviation := by
    intro z cap b u hu l hl
    exact adjacentFailureWindow_deviation_sub_le hu hl
  ratioConstant := fun z cap ↦
    ∑ b : TilingAwayDomino (data.factored.tiling z cap)
        (data.factored.start z cap) (data.factored.retained z cap)
        (data.factored.distinguished z cap),
      adjacentLocalRatio
        (Fintype.card (TilingCoordinatesAt (data.factored.tiling z cap)
          (data.factored.start z cap) (data.factored.retained z cap) b.1))
        (adjacentWindowRadius
          (canonicalWindowWidth
            (Fintype.card (TilingCoordinatesAt (data.factored.tiling z cap)
              (data.factored.start z cap) (data.factored.retained z cap) b.1))))
        (adjacentWindowSeparation
          (canonicalWindowWidth
            (Fintype.card (TilingCoordinatesAt (data.factored.tiling z cap)
              (data.factored.start z cap) (data.factored.retained z cap) b.1))))
  ratioConstant_nonneg := by
    intro z cap
    apply Finset.sum_nonneg
    intro b _
    exact adjacentLocalRatio_nonneg _ _ _
  localRatio_le := by
    intro z cap b
    classical
    let f := fun b' : TilingAwayDomino (data.factored.tiling z cap)
        (data.factored.start z cap) (data.factored.retained z cap)
        (data.factored.distinguished z cap) ↦
      adjacentLocalRatio
        (Fintype.card (TilingCoordinatesAt (data.factored.tiling z cap)
          (data.factored.start z cap) (data.factored.retained z cap) b'.1))
        (adjacentWindowRadius
          (canonicalWindowWidth
            (Fintype.card (TilingCoordinatesAt (data.factored.tiling z cap)
              (data.factored.start z cap) (data.factored.retained z cap) b'.1))))
        (adjacentWindowSeparation
          (canonicalWindowWidth
            (Fintype.card (TilingCoordinatesAt (data.factored.tiling z cap)
              (data.factored.start z cap) (data.factored.retained z cap) b'.1))))
    change f b ≤ ∑ b', f b'
    exact Finset.single_le_sum (f := f)
      (fun b' _ ↦ by
        dsimp only [f]
        exact adjacentLocalRatio_nonneg _ _ _)
      (Finset.mem_univ b)
  cost_nonneg := canonicalCrudeProductCost_nonneg bound
  envelope := by
    intro z cap total htotal
    exact productEnvelope_le_canonicalCrudeProductCost _
      (by
        apply Finset.sum_nonneg
        intro b _
        exact adjacentLocalRatio_nonneg _ _ _)
      threshold G j bound total htotal

/-- A balancedness law for the whole path space.  It has empty exceptional
site set and therefore contributes exactly zero balance budget. -/
def univGeometricBalanceLaw (m : ℕ) (hm : 0 < m) :
    HLOZThresholdedShellScreening.GeometricBalanceLaw
      (Site := Point) simpleRandomWalk (Set.univ : Set WalkPath) m where
  sites := ∅
  lowerBad := fun _ ↦ ∅
  upperBad := fun _ ↦ ∅
  budget := 0
  successes := fun _ ↦ m
  identify := by
    ext s
    simp [Screening.someCandidateBad, Balancedness.twoSidedBad]
  m_pos := hm
  card_le := by simp
  successes_pos := by simp
  successes_le := by simp
  deviation_le := by simp
  lower_law := by simp
  upper_law := by simp

/-- One adjacent-shell interface with canonical windows and a premise-free
finite envelope. -/
structure TilingCanonicalWindowInterfaceData
    (t : TilingLazyDecomposition.DominoTiling) (m k : ℕ)
    (next : Set WalkPath) (threshold : ℕ → ℕ)
    (G j bound : ℕ) where
  measurable_next : MeasurableSet next
  next_subset_stage :
    next ⊆ VariableStoppedTracePartition.thresholdReachStage m k
  tail : TilingCanonicalWindowTailData
    (TilingVariableStoppedTracePartition.favoriteTilingStagePiece t m k
      (VariableStoppedTracePartition.thresholdReachStage m k))
    next threshold G j bound

/-- Insert the canonical local-CLT facts into one adjacent-shell interface. -/
noncomputable def localCLTInterfaceDataOfCanonicalWindowData
    {t : TilingLazyDecomposition.DominoTiling} {m k : ℕ}
    {next : Set WalkPath} {threshold : ℕ → ℕ}
    {G j bound : ℕ}
    (data : TilingCanonicalWindowInterfaceData t m k next
      threshold G j bound) :
    TilingLocalCLTInterfaceProductData t m k next threshold G j bound
      (canonicalCrudeProductCost bound) where
  measurable_next := data.measurable_next
  next_subset_stage := data.next_subset_stage
  tail := localCLTTailDataOfCanonicalWindowData data.tail

/-- All-six adjacent-shell product data with no balance-law or analytic
window fields.  Choosing `balanced = univ` is sound because the literal
interface product is required on the entire thresholded growth event. -/
structure AllSixCanonicalWindowProductData
    (t : TilingLazyDecomposition.DominoTiling) (m cutoff : ℕ)
    (band : RandomClockBand) where
  totalBound : ℕ → ℕ
  product : 0 < m →
    ∀ shell, shell < shellCount48 m band.beta - 1 →
      TilingCanonicalWindowInterfaceData t m band.oldRank
        (Set.univ ∩ thresholdedGrowthFailure
          (tilingBandOccupancy t m cutoff band)
          (geometricShellThreshold (initialBudget48 m) shellGrowth48)
          shellGrowth48 shell)
        (geometricShellThreshold (initialBudget48 m) shellGrowth48)
        shellGrowth48 shell (totalBound shell)

/-- Convert literal canonical-window data to the general all-six local-CLT
package.  Its balance budget is zero and its interface costs are the checked
finite envelopes `2^(totalBound shell)`. -/
noncomputable def allSixLocalCLTDataOfCanonicalWindowData
    {t : TilingLazyDecomposition.DominoTiling} {m cutoff : ℕ}
    {band : RandomClockBand}
    (data : AllSixCanonicalWindowProductData t m cutoff band) :
    AllSixLocalCLTBandProductData t m cutoff band where
  lawStart := 1
  balanced := fun _ ↦ Set.univ
  balanceLaw := by
    intro _hstart hm shell
    exact univGeometricBalanceLaw m hm
  interfaceCost := fun shell ↦
    canonicalCrudeProductCost (data.totalBound shell)
  interfaceCost_nonneg := fun shell ↦
    canonicalCrudeProductCost_nonneg (data.totalBound shell)
  totalBound := data.totalBound
  product := by
    intro _hstart hm shell hshell
    exact localCLTInterfaceDataOfCanonicalWindowData
      (data.product hm shell hshell)

/-- Finite-band stopped Proposition 4.8 with all local-CLT and balance-law
fields discharged.  What remains is literal stopped-fibre/cap data plus the
endpoint-phase cutoff and band arithmetic. -/
theorem eventually_simpleRandomWalk_tilingRandomClockCandidateOverflow_le_sum_of_canonicalWindowData
    (t : TilingLazyDecomposition.DominoTiling)
    (cutoff : ℕ → ℕ) (bands : ℕ → Finset RandomClockBand)
    (hcutoff : ∀ᶠ m : ℕ in atTop,
      cutoff m ≤ ExternalProposition44.hlozCutoff44 m)
    (hphase : ∀ m band, band ∈ bands m → band.vertexPhase = false)
    (hthreshold : ∀ᶠ m : ℕ in atTop, ∀ band ∈ bands m,
      ExternalProposition44.hlozOnePointLevel44 m + 1 ≤
        band.externalThreshold)
    (hbeta : ∀ m band, band ∈ bands m → kappaOne ≤ band.beta)
    (data : ∀ m band,
      AllSixCanonicalWindowProductData t m (cutoff m) band) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk
          (HLOZTilingGapRandomClockScreen.tilingRandomClockCandidateOverflow
            t m (cutoff m) (bands m)) ≤
        ∑ band ∈ bands m,
          HLOZAllSixBandProductClosure.allSixBandOverflowCoefficient
            (HLOZAllSixFactoredProductClosure.allSixBandProductDataOfFactoredData
              (allSixFactoredBandProductDataOfExactCoordinateData
                (allSixExactCoordinateDataOfLocalCLTData
                  (allSixLocalCLTDataOfCanonicalWindowData
                    (data m band))))) := by
  apply eventually_simpleRandomWalk_tilingRandomClockCandidateOverflow_le_sum_of_localCLTData
    t cutoff bands hcutoff hphase hthreshold hbeta
      (fun m band ↦ allSixLocalCLTDataOfCanonicalWindowData (data m band))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  intro band _hband
  exact hm

end

end Erdos1165.HLOZCanonicalWindowProductClosure
