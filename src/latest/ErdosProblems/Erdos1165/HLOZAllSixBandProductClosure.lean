/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos1165.HLOZLowScaleProductInstantiation
import ErdosProblems.Erdos1165.HLOZStoppedLazyLawClosure
import ErdosProblems.Erdos1165.HLOZTilingGapRandomClockClosure

/-!
# All-six stopped-trace product closure for the low HLOZ bands

The retained trace is countable, whereas the insertion coordinates inside
one trace fibre are finite.  It would therefore be incorrect to identify a
global fixed-total event with one finite product.  This file performs the
operations in the sound order:

1. sum the genuinely random adjacent-pair total inside each finite fibre;
2. bound that finite product screen without a factor equal to the number of
   possible totals;
3. use the all-six capped trace certificate to sum the countable retained
   traces.

All constructors below require the explicit positive-level and tail-start
hypotheses.  No geometric deviation law is asserted at the finitely many
small levels.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZAllSixBandProductClosure

open HeterogeneousProductTail HLOZLowScaleCandidateOverflow
open HLOZLowScaleProductInstantiation HLOZDynamicStoppedOnePointClosure
open HLOZDynamicThresholdedScreening HLOZThresholdedShellScreening
open HLOZLazyOverflow HLOZLazyOverflowClosure HLOZGapRandomClockScreen
open HLOZGapEstimate HLOZProposition48Candidates NearFavoriteThresholded
open NearFavoriteShells ScreeningInstantiation ExternalStoppedWeightedOnePoint
open ExternalThickCount
open HLOZPathEvents
open TilingStoppedProductDisintegration TilingVariableStoppedTracePartition
open VariableStoppedTracePartition
open HLOZTraceCappedProductScreening FiniteDominoProductLaw
open LazyDecomposition
open HLOZTilingGapRandomClockScreen

noncomputable section

variable {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
variable {State : Coordinate → Type*} [∀ c, Fintype (State c)]

/-- The union, inside one finite product fibre, of all admissible exact-total
upper-tail screens. -/
def randomTotalThresholdedUpperTail
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (threshold : ℕ → ℕ) (G j bound : ℕ) (ℓ : ∀ c, State c) : Prop :=
  let total := (pairSupport upper lower ℓ).card
  total < bound + 1 ∧
    thresholdedGrowthCut threshold G j total ≤ upperCount upper ℓ

instance instDecidablePredRandomTotalThresholdedUpperTail
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (threshold : ℕ → ℕ) (G j bound : ℕ) :
    DecidablePred
      (randomTotalThresholdedUpperTail upper lower threshold G j bound) :=
  fun ℓ ↦ by
    unfold randomTotalThresholdedUpperTail
    infer_instance

/-- Partition the aggregate screen by its actual adjacent-pair total. -/
theorem sum_randomTotalThresholdedUpperTail_eq_sum_fixedTotal
    (weight : ∀ c, State c → ℝ)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (threshold : ℕ → ℕ) (G j bound : ℕ) :
    (∑ ℓ : ∀ c, State c,
        if randomTotalThresholdedUpperTail upper lower threshold G j bound ℓ
        then productPointMass weight ℓ else 0) =
      ∑ total ∈ Finset.range (bound + 1),
        ∑ ℓ : ∀ c, State c,
          if fixedTotalUpperTail upper lower total
              (thresholdedGrowthCut threshold G j total) ℓ
          then productPointMass weight ℓ else 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ℓ _
  by_cases hbound : (pairSupport upper lower ℓ).card < bound + 1
  · have hmem : (pairSupport upper lower ℓ).card ∈
        Finset.range (bound + 1) := Finset.mem_range.mpr hbound
    rw [Finset.sum_eq_single (pairSupport upper lower ℓ).card]
    · by_cases hcut :
          thresholdedGrowthCut threshold G j
              (pairSupport upper lower ℓ).card ≤ upperCount upper ℓ <;>
        simp [randomTotalThresholdedUpperTail, hbound, hcut,
          fixedTotalUpperTail]
    · intro total htotal hne
      have hcard : (pairSupport upper lower ℓ).card ≠ total := Ne.symm hne
      simp [fixedTotalUpperTail, hcard]
    · exact fun hnot ↦ (hnot hmem).elim
  · have hout : (pairSupport upper lower ℓ).card ∉
        Finset.range (bound + 1) := by simpa using hbound
    rw [Finset.sum_eq_zero]
    · simp [randomTotalThresholdedUpperTail, hbound]
    · intro total htotal
      have hne : (pairSupport upper lower ℓ).card ≠ total := by
        intro heq
        apply hout
        simpa [heq] using htotal
      simp [fixedTotalUpperTail, hne]

/-- The no-cardinality-loss heterogeneous product estimate for the entire
threshold-relevant interface in one finite retained-trace fibre. -/
theorem randomTotalThresholdedUpperTail_product_bound
    (weight : ∀ c, State c → ℝ)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (threshold : ℕ → ℕ) (G j bound : ℕ)
    (hweight : ∀ c v, 0 ≤ weight c v)
    (hnorm : ∀ c, (∑ v, weight c v) ≤ 1)
    (hdisjoint : ∀ c v, ¬ (upper c v ∧ lower c v))
    {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hratio : ∀ c,
      (∑ v, if upper c v then weight c v else 0) ≤
        C * ∑ v, if lower c v then weight c v else 0)
    (henvelope : ∀ total < bound + 1,
      (1 + C / (1 + C)) ^ total /
          (2 : ℝ) ^ thresholdedGrowthCut threshold G j total ≤ K) :
    (∑ ℓ : ∀ c, State c,
        if randomTotalThresholdedUpperTail upper lower threshold G j bound ℓ
        then productPointMass weight ℓ else 0) ≤ K := by
  rw [sum_randomTotalThresholdedUpperTail_eq_sum_fixedTotal]
  calc
    (∑ total ∈ Finset.range (bound + 1),
      ∑ ℓ : ∀ c, State c,
        if fixedTotalUpperTail upper lower total
            (thresholdedGrowthCut threshold G j total) ℓ
        then productPointMass weight ℓ else 0) ≤
        ∑ total ∈ Finset.range (bound + 1),
          exactPairTotalMass weight upper lower total *
            ((1 + C / (1 + C)) ^ total /
              (2 : ℝ) ^ thresholdedGrowthCut threshold G j total) := by
      apply Finset.sum_le_sum
      intro total _
      simpa only [mul_div_assoc] using
        (fixedTotalUpperTail_product_bound weight upper lower hweight
          hdisjoint hC hratio total
            (thresholdedGrowthCut threshold G j total))
    _ ≤ K := sum_exactPairTotalMass_mul_cost_le weight upper lower
      hweight hnorm bound
      (fun total ↦ (1 + C / (1 + C)) ^ total /
        (2 : ℝ) ^ thresholdedGrowthCut threshold G j total)
      hK henvelope

/-! ## Improving a literal all-six coordinate specification -/

/-- Product-tail data attached to a literal all-six stopped-coordinate
specification.  The `raw` certificate uses the harmless unit bound; its exact
`coordinate_identity` and path coverage are retained.  The remaining fields
identify the Boolean coordinate screen with the aggregate random-total tail
and prove the one-coordinate window comparisons used below. -/
structure TilingRandomTotalProductTailSpec {index : Type*}
    (piece : index → Set WalkPath) (next : Set WalkPath)
    (threshold : ℕ → ℕ) (G j bound : ℕ) (K : ℝ) where
  raw : TilingStoppedCoordinateProductSpec piece next (1 : ℝ≥0∞)
  upperWindow : ∀ z cap
    (b : TilingAwayDomino (raw.tiling z cap) (raw.start z cap)
      (raw.retained z cap) (raw.distinguished z cap)),
      Fin (raw.upper z cap b) → Prop
  lowerWindow : ∀ z cap
    (b : TilingAwayDomino (raw.tiling z cap) (raw.start z cap)
      (raw.retained z cap) (raw.distinguished z cap)),
      Fin (raw.upper z cap b) → Prop
  upperDecidable : ∀ z cap b, DecidablePred (upperWindow z cap b)
  lowerDecidable : ∀ z cap b, DecidablePred (lowerWindow z cap b)
  accepts_iff : ∀ z cap ℓ,
    raw.accepts z cap ℓ = true ↔
      randomTotalThresholdedUpperTail
        (upperWindow z cap) (lowerWindow z cap) threshold G j bound ℓ
  coordinate_nonneg : ∀ z cap
    (b : TilingAwayDomino (raw.tiling z cap) (raw.start z cap)
      (raw.retained z cap) (raw.distinguished z cap))
    (v : Fin (raw.upper z cap b)),
      0 ≤ coordinateMass (raw.pointMass z cap) (raw.upper z cap) b v
  coordinate_sum_le_one : ∀ z cap
    (b : TilingAwayDomino (raw.tiling z cap) (raw.start z cap)
      (raw.retained z cap) (raw.distinguished z cap)),
      (∑ v : Fin (raw.upper z cap b),
        coordinateMass (raw.pointMass z cap) (raw.upper z cap) b v) ≤ 1
  upper_lower_disjoint : ∀ z cap
    (b : TilingAwayDomino (raw.tiling z cap) (raw.start z cap)
      (raw.retained z cap) (raw.distinguished z cap))
    (v : Fin (raw.upper z cap b)),
      ¬ (upperWindow z cap b v ∧ lowerWindow z cap b v)
  ratioConstant : index → ℕ → ℝ
  ratioConstant_nonneg : ∀ z cap, 0 ≤ ratioConstant z cap
  window_ratio : ∀ z cap
    (b : TilingAwayDomino (raw.tiling z cap) (raw.start z cap)
      (raw.retained z cap) (raw.distinguished z cap)),
      (∑ v : Fin (raw.upper z cap b), if upperWindow z cap b v then
          coordinateMass (raw.pointMass z cap) (raw.upper z cap) b v else 0) ≤
        ratioConstant z cap *
          ∑ v : Fin (raw.upper z cap b), if lowerWindow z cap b v then
            coordinateMass (raw.pointMass z cap) (raw.upper z cap) b v else 0
  cost_nonneg : 0 ≤ K
  envelope : ∀ z cap total, total < bound + 1 →
    (1 + ratioConstant z cap / (1 + ratioConstant z cap)) ^ total /
        (2 : ℝ) ^ thresholdedGrowthCut threshold G j total ≤ K

/-- Replace the unit product bound on a literal all-six stopped-coordinate
specification by the checked aggregate heterogeneous product bound. -/
def tilingStoppedCoordinateProductSpecOfRandomTotalTail
    {index : Type*} {piece : index → Set WalkPath} {next : Set WalkPath}
    {threshold : ℕ → ℕ} {G j bound : ℕ} {K : ℝ}
    (data : TilingRandomTotalProductTailSpec piece next threshold G j bound K) :
    TilingStoppedCoordinateProductSpec piece next (ENNReal.ofReal K) := by
  letI (z : index) (cap : ℕ)
      (b : TilingAwayDomino (data.raw.tiling z cap) (data.raw.start z cap)
        (data.raw.retained z cap) (data.raw.distinguished z cap)) :
      DecidablePred (data.upperWindow z cap b) :=
    data.upperDecidable z cap b
  letI (z : index) (cap : ℕ)
      (b : TilingAwayDomino (data.raw.tiling z cap) (data.raw.start z cap)
        (data.raw.retained z cap) (data.raw.distinguished z cap)) :
      DecidablePred (data.lowerWindow z cap b) :=
    data.lowerDecidable z cap b
  refine { data.raw with product_bound := ?_ }
  intro z cap
  rw [screenMass_eq_product]
  calc
    (∑ ℓ,
      if data.raw.accepts z cap ℓ = true then
        ∏ b, coordinateMass (data.raw.pointMass z cap)
          (data.raw.upper z cap) b (ℓ b)
      else 0) =
        ∑ ℓ,
          if randomTotalThresholdedUpperTail
              (data.upperWindow z cap) (data.lowerWindow z cap)
              threshold G j bound ℓ then
            productPointMass
              (fun (b : TilingAwayDomino (data.raw.tiling z cap)
                  (data.raw.start z cap) (data.raw.retained z cap)
                  (data.raw.distinguished z cap))
                (v : Fin (data.raw.upper z cap b)) ↦
                  coordinateMass (data.raw.pointMass z cap)
                    (data.raw.upper z cap) b (v : ℕ)) ℓ
          else 0 := by
      apply Finset.sum_congr rfl
      intro ℓ _
      rw [productPointMass]
      exact if_congr (data.accepts_iff z cap ℓ) rfl rfl
    _ ≤ K := randomTotalThresholdedUpperTail_product_bound
      (fun (b : TilingAwayDomino (data.raw.tiling z cap)
          (data.raw.start z cap) (data.raw.retained z cap)
          (data.raw.distinguished z cap))
        (v : Fin (data.raw.upper z cap b)) ↦
          coordinateMass (data.raw.pointMass z cap)
            (data.raw.upper z cap) b (v : ℕ))
      (data.upperWindow z cap) (data.lowerWindow z cap)
      threshold G j bound (data.coordinate_nonneg z cap)
      (data.coordinate_sum_le_one z cap)
      (data.upper_lower_disjoint z cap)
      (data.ratioConstant_nonneg z cap) data.cost_nonneg
      (data.window_ratio z cap) (data.envelope z cap)
    _ = (ENNReal.ofReal K).toReal := by
      rw [ENNReal.toReal_ofReal data.cost_nonneg]

/-! ## Countable trace summation and the interface shell recurrence -/

/-- One complete all-six trace screen for an adjacent-shell interface. -/
structure TilingInterfaceProductData
    (t : TilingLazyDecomposition.DominoTiling) (m k : ℕ)
    (next : Set WalkPath) (threshold : ℕ → ℕ)
    (G j bound : ℕ) (K : ℝ) where
  measurable_next : MeasurableSet next
  next_subset_stage : next ⊆ thresholdReachStage m k
  tail : TilingRandomTotalProductTailSpec
    (favoriteTilingStagePiece t m k (thresholdReachStage m k)) next
    threshold G j bound K

/-- The aggregate finite-product estimate on every trace atom sums to a
global interface estimate.  The only pathwise content in `data.tail` is the
literal stopped-coordinate coverage of `next`. -/
theorem simpleRandomWalk_real_interface_le_of_tilingProduct
    {t : TilingLazyDecomposition.DominoTiling} {m k : ℕ}
    {next : Set WalkPath} {threshold : ℕ → ℕ}
    {G j bound : ℕ} {K : ℝ}
    (data : TilingInterfaceProductData t m k next threshold G j bound K) :
    simpleRandomWalk.real next ≤ K := by
  let spec := tilingStoppedCoordinateProductSpecOfRandomTotalTail data.tail
  let screen : SomeTraceCappedProductScreening
      (thresholdReachStage m k) next (ENNReal.ofReal K) :=
    someFavoriteTilingTraceCappedScreenOfStoppedCoordinateSpec
      t m k (thresholdReachStage m k) next (ENNReal.ofReal K)
      (measurableSet_thresholdReachStage m k) (fun _ hs ↦ hs)
      data.next_subset_stage spec
  have hstage : simpleRandomWalk (thresholdReachStage m k) ≤ 1 := by
    simpa using measure_mono (μ := simpleRandomWalk)
      (subset_univ (thresholdReachStage m k))
  have hmeasure : simpleRandomWalk next ≤ ENNReal.ofReal K := by
    calc
      simpleRandomWalk next ≤
          ENNReal.ofReal K * simpleRandomWalk (thresholdReachStage m k) :=
        @transition_measure_le_of_traceCappedProductScreening
          screen.Index screen.countableIndex (thresholdReachStage m k) next
          data.measurable_next (ENNReal.ofReal K) ENNReal.ofReal_ne_top
          screen.screening
      _ ≤ ENNReal.ofReal K * 1 := by gcongr
      _ = ENNReal.ofReal K := mul_one _
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
  simpa only [Measure.real, ENNReal.toReal_ofReal data.tail.cost_nonneg] using hreal

/-- A direct product estimate for every threshold-relevant adjacent shell.
Unlike `RandomTotalProductLaw`, this interface has already summed the exact
totals inside each finite retained-trace fibre. -/
structure ThresholdedInterfaceProductLaw {Omega : Type*}
    [MeasurableSpace Omega] (mu : Measure Omega)
    (balanced : ℕ → Set Omega) (occupancy : Omega → ℕ → ℕ)
    (threshold : ℕ → ℕ) (G shellCount : ℕ) where
  cost : ℕ → ℝ
  cost_nonneg : ∀ j, 0 ≤ cost j
  interface_bound : ∀ j < shellCount - 1,
    mu.real (balanced j ∩
      thresholdedGrowthFailure occupancy threshold G j) ≤ cost j

/-- Shell propagation after exact totals have been summed fibrewise. -/
theorem measureReal_totalOverflow_le_of_geometricBalance_and_interfaceProduct
    {Omega Site : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (balanced : ℕ → Set Omega) (occupancy : Omega → ℕ → ℕ)
    (threshold : ℕ → ℕ) (G shellCount m : ℕ)
    (hstep : ∀ j, j + 1 < shellCount →
      G * threshold j ≤ threshold (j + 1))
    (balanceLaw : ∀ j,
      GeometricBalanceLaw (Site := Site) mu (balanced j) m)
    (productLaw : ThresholdedInterfaceProductLaw mu balanced occupancy
      threshold G shellCount)
    {baseCost : ℝ}
    (hbase : mu.real (shellOverflow occupancy threshold 0) ≤ baseCost) :
    mu.real (totalOverflow occupancy threshold shellCount) ≤
      baseCost + ∑ j ∈ Finset.range (shellCount - 1),
        ((((balanceLaw j).budget : ℝ≥0∞) *
            (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
              ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)))).toReal +
          productLaw.cost j) := by
  refine (NearFavoriteThresholded.measureReal_totalOverflow_le mu balanced
    occupancy threshold G
    shellCount hstep).trans ?_
  gcongr with j hj
  have hjlt : j < shellCount - 1 := Finset.mem_range.mp hj
  calc
    mu.real (thresholdedInterfaceBad balanced occupancy threshold G j) ≤
        mu.real (balanced j)ᶜ +
          mu.real (balanced j ∩
            thresholdedGrowthFailure occupancy threshold G j) :=
      measureReal_thresholdedInterfaceBad_le mu balanced occupancy threshold G j
    _ ≤ (((balanceLaw j).budget : ℝ≥0∞) *
          (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
            ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)))).toReal +
        productLaw.cost j :=
      add_le_add
        (measureReal_compl_le_of_geometricBalanceLaw mu (balanced j) m
          (balanceLaw j))
        (productLaw.interface_bound j hjlt)

/-- Low-scale data after exact totals and countable traces have both been
summed in the correct order. -/
structure BandInterfaceScreen (m cutoff : ℕ) (band : RandomClockBand) where
  balanced : ℕ → Set WalkPath
  balanceLaw : ∀ j,
    GeometricBalanceLaw (Site := Point) simpleRandomWalk (balanced j) m
  interfaceLaw : ThresholdedInterfaceProductLaw simpleRandomWalk balanced
    (bandOccupancy m cutoff band)
    (geometricShellThreshold (initialBudget48 m) shellGrowth48)
    shellGrowth48 (shellCount48 m band.beta)

noncomputable def bandInterfaceOverflowCoefficient
    {m cutoff : ℕ} {band : RandomClockBand}
    (screen : BandInterfaceScreen m cutoff band) : ℝ≥0∞ :=
  ENNReal.ofReal
    (((ExternalProposition44.hlozOnePointRate44 m *
          ((ExternalProposition44.hlozCutoff44 m + 1 : ℕ) : ℝ≥0∞) /
          initialBudget48 m).toReal) +
      ∑ j ∈ Finset.range (shellCount48 m band.beta - 1),
        ((((screen.balanceLaw j).budget : ℝ≥0∞) *
            (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
              ENNReal.ofReal
                (Real.exp (-17 * balanceRateScale m)))).toReal +
          screen.interfaceLaw.cost j))

/-- The actual per-band stopped candidate overflow, with exact totals summed
inside the finite all-six fibres and retained traces summed by the capped
certificate. -/
theorem simpleRandomWalk_randomClockDominatingBandOverflow_le_of_interface
    {m cutoff : ℕ} {band : RandomClockBand}
    (hone : CanonicalStoppedOnePointAt m)
    (hbudget : CandidateBudgetArithmeticAt m)
    (hcutoff : cutoff ≤ ExternalProposition44.hlozCutoff44 m)
    (hthreshold : ExternalProposition44.hlozOnePointLevel44 m ≤
      band.externalThreshold)
    (hbeta : kappaOne ≤ band.beta)
    (screen : BandInterfaceScreen m cutoff band) :
    simpleRandomWalk (randomClockDominatingBandOverflow m cutoff band) ≤
      bandInterfaceOverflowCoefficient screen := by
  let visited := stoppedCapVisitedSites band.orientation m
  let tau := pathTruncatedLevelTime m band.oldRank cutoff
  let large := stoppedOrientedLargeEvent band.orientation tau
    band.externalThreshold
  let distinguished := randomClockDistinguishedSites m cutoff band
  let totalLocalTime := randomClockTotalLocalTime m cutoff band
  let occupancy := dynamicShellOccupancy visited large distinguished
    totalLocalTime m (shellWidth48 m)
  let threshold := geometricShellThreshold (initialBudget48 m) shellGrowth48
  have htau : ∀ s, tau s ≤ ExternalProposition44.hlozCutoff44 m :=
    fun s ↦ (pathTruncatedLevelTime_le m band.oldRank cutoff s).trans hcutoff
  have hlarge : ∀ x, MeasurableSet (large x) := by
    intro x
    simpa only [large, tau, ← randomClockExternalLargeEvent_eq_stopped] using
      measurableSet_randomClockExternalLargeEvent m cutoff band x
  have hbase : simpleRandomWalk.real (shellOverflow occupancy threshold 0) ≤
      (ExternalProposition44.hlozOnePointRate44 m *
        ((ExternalProposition44.hlozCutoff44 m + 1 : ℕ) : ℝ≥0∞) /
        initialBudget48 m).toReal := by
    exact simpleRandomWalk_real_dynamicShellOverflow_zero_le
      visited large distinguished totalLocalTime m (shellWidth48 m)
      (initialBudget48 m) shellGrowth48
      (ExternalProposition44.hlozOnePointRate44 m)
      (((ExternalProposition44.hlozCutoff44 m + 1 : ℕ) : ℝ≥0∞))
      (by unfold initialBudget48; omega)
      (ExternalWeightedOnePointCanonical.hlozOnePointRate44_ne_top m)
      ENNReal.coe_ne_top
      (fun x ↦ measurableSet_member_orientedExternalVisitedSites
        band.orientation (ExternalProposition44.hlozCutoff44 m) x)
      hlarge
      (hone band.orientation tau band.externalThreshold hthreshold htau hlarge)
      (by
        simpa only [visited, stoppedCapVisitedSites] using
          lintegral_orientedExternalVisitedSites_card_le band.orientation
            (ExternalProposition44.hlozCutoff44 m))
  have hstep : ∀ j, j + 1 < shellCount48 m band.beta →
      shellGrowth48 * threshold j ≤ threshold (j + 1) := by
    intro j _
    exact (geometricShellThreshold_step (initialBudget48 m)
      shellGrowth48 j).le
  have htotal : simpleRandomWalk.real
      (totalOverflow occupancy threshold (shellCount48 m band.beta)) ≤
        (ExternalProposition44.hlozOnePointRate44 m *
          ((ExternalProposition44.hlozCutoff44 m + 1 : ℕ) : ℝ≥0∞) /
          initialBudget48 m).toReal +
        ∑ j ∈ Finset.range (shellCount48 m band.beta - 1),
          ((((screen.balanceLaw j).budget : ℝ≥0∞) *
              (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
                ENNReal.ofReal
                  (Real.exp (-17 * balanceRateScale m)))).toReal +
            screen.interfaceLaw.cost j) := by
    exact measureReal_totalOverflow_le_of_geometricBalance_and_interfaceProduct
      simpleRandomWalk screen.balanced occupancy threshold shellGrowth48
      (shellCount48 m band.beta) m hstep screen.balanceLaw
      screen.interfaceLaw hbase
  have hreal : simpleRandomWalk.real
      (randomClockDominatingBandOverflow m cutoff band) ≤
        (ExternalProposition44.hlozOnePointRate44 m *
          ((ExternalProposition44.hlozCutoff44 m + 1 : ℕ) : ℝ≥0∞) /
          initialBudget48 m).toReal +
        ∑ j ∈ Finset.range (shellCount48 m band.beta - 1),
          ((((screen.balanceLaw j).budget : ℝ≥0∞) *
              (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
                ENNReal.ofReal
                  (Real.exp (-17 * balanceRateScale m)))).toReal +
            screen.interfaceLaw.cost j) := by
    apply (measureReal_mono ?_).trans htotal
    simpa only [randomClockDominatingBandOverflow,
      randomClockDominatingBandSites, dynamicStoppedCandidateOverflow48,
      visited, large, tau, distinguished, totalLocalTime, occupancy,
      threshold] using
        (dynamicStoppedCandidateOverflow48_subset_totalOverflow visited large
          distinguished totalLocalTime m band.beta
            (hbudget band.beta hbeta))
  rw [← ENNReal.ofReal_toReal (measure_ne_top simpleRandomWalk
    (randomClockDominatingBandOverflow m cutoff band))]
  exact ENNReal.ofReal_mono hreal

/-- Finite union of genuine random-clock bands, with the canonical stopped
one-point estimate and all deterministic-cap transport already consumed. -/
theorem eventually_simpleRandomWalk_randomClockCandidateOverflow_le_sum_of_interface
    (cutoff : ℕ → ℕ) (bands : ℕ → Finset RandomClockBand)
    (hcutoff : ∀ᶠ m : ℕ in Filter.atTop,
      cutoff m ≤ ExternalProposition44.hlozCutoff44 m)
    (hthreshold : ∀ᶠ m : ℕ in Filter.atTop,
      ∀ band ∈ bands m,
        ExternalProposition44.hlozOnePointLevel44 m ≤
          band.externalThreshold)
    (hbeta : ∀ m band, band ∈ bands m → kappaOne ≤ band.beta)
    (screen : ∀ m band, BandInterfaceScreen m (cutoff m) band) :
    ∀ᶠ m : ℕ in Filter.atTop,
      simpleRandomWalk
          (candidateOverflow (bands m) (randomClockBandSites m (cutoff m))
            (fun band ↦ candidateBudget48 m band.beta)) ≤
        ∑ band ∈ bands m,
          bandInterfaceOverflowCoefficient (screen m band) := by
  filter_upwards [eventually_canonicalStoppedOnePointAt,
      eventually_candidateBudgetArithmeticAt, hcutoff, hthreshold] with
      m hone hbudget hcutoffM hthresholdM
  refine (simpleRandomWalk_randomClockCandidateOverflow_le_sum_dominating
    hcutoffM).trans ?_
  apply Finset.sum_le_sum
  intro band hband
  exact simpleRandomWalk_randomClockDominatingBandOverflow_le_of_interface
    hone hbudget hcutoffM (hthresholdM band hband) (hbeta m band hband)
      (screen m band)

/-! ## Exact state-dependent tiling candidate event -/

/-- The shell occupancy used by the genuine state-dependent tiling screen. -/
noncomputable def tilingBandOccupancy
    (t : TilingLazyDecomposition.DominoTiling)
    (m cutoff : ℕ) (band : RandomClockBand) : WalkPath → ℕ → ℕ :=
  dynamicShellOccupancy (tilingRandomClockVisitedSites t m cutoff band)
    (tilingRandomClockExternalLargeEvent t m cutoff band)
    (tilingRandomClockDistinguishedSites t m cutoff band)
    (tilingRandomClockTotalLocalTime m cutoff band)
    m (shellWidth48 m)

theorem tilingExternalPath_length_le
    (t : TilingLazyDecomposition.DominoTiling) (p : List Point) :
    (TilingLazyDecomposition.tilingExternalPath t p).length ≤ p.length := by
  have h := TilingLazyDecomposition.tilingExternalPath_length_add_lazyPoints_length
    t p
  omega

theorem phasedExternalVisitedSites_card_le_length
    (t : TilingLazyDecomposition.DominoTiling) (o : Orientation)
    (p : List Point) :
    (TilingLazyDecomposition.phasedExternalVisitedSites t o p).card ≤
      p.length := by
  calc
    (TilingLazyDecomposition.phasedExternalVisitedSites t o p).card ≤
        (TilingLazyDecomposition.tilingExternalPath t
          (TilingLazyDecomposition.phasedInput o p)).length :=
      List.toFinset_card_le
        (TilingLazyDecomposition.tilingExternalPath t
          (TilingLazyDecomposition.phasedInput o p))
    _ ≤ (TilingLazyDecomposition.phasedInput o p).length :=
      tilingExternalPath_length_le t _
    _ ≤ p.length := by
      cases o <;> cases p <;> simp [TilingLazyDecomposition.phasedInput]

theorem phaseVertices_length_le
    (phase : TilingExternalPhaseSplit.ExternalVertexPhase) (p : List Point) :
    (TilingExternalPhaseSplit.phaseVertices phase p).length ≤ p.length := by
  cases phase
  · induction p using List.twoStepInduction with
    | nil => rfl
    | singleton a => simp [TilingExternalPhaseSplit.phaseVertices,
        TilingExternalPhaseSplit.endpointPhaseVertices]
    | cons_cons a b rest ih _ =>
        simp [TilingExternalPhaseSplit.phaseVertices,
          TilingExternalPhaseSplit.endpointPhaseVertices] at ih ⊢
        omega
  · induction p using List.twoStepInduction with
    | nil => rfl
    | singleton a => simp [TilingExternalPhaseSplit.phaseVertices,
        TilingExternalPhaseSplit.midpointPhaseVertices]
    | cons_cons a b rest ih _ =>
        simp [TilingExternalPhaseSplit.phaseVertices,
          TilingExternalPhaseSplit.midpointPhaseVertices] at ih ⊢
        omega

theorem phasedExternalVertexVisitedSites_card_le_length
    (t : TilingLazyDecomposition.DominoTiling) (o : Orientation)
    (phase : TilingExternalPhaseSplit.ExternalVertexPhase) (p : List Point) :
    (TilingExternalPhaseSplit.phasedExternalVertexVisitedSites
      t o phase p).card ≤ p.length := by
  calc
    (TilingExternalPhaseSplit.phasedExternalVertexVisitedSites
        t o phase p).card ≤
        (TilingExternalPhaseSplit.phasedExternalVertexPath
          t o phase p).length := List.toFinset_card_le _
    _ ≤ (TilingLazyDecomposition.tilingExternalPath t
          (TilingLazyDecomposition.phasedInput o p)).length :=
      phaseVertices_length_le phase _
    _ ≤ (TilingLazyDecomposition.phasedInput o p).length :=
      tilingExternalPath_length_le t _
    _ ≤ p.length := by
      cases o <;> cases p <;> simp [TilingLazyDecomposition.phasedInput]

theorem pathPhasedExternalVisitedSites_card_le
    (t : TilingLazyDecomposition.DominoTiling) (o : Orientation)
    (s : WalkPath) (n : ℕ) :
    (TilingLazyDecomposition.pathPhasedExternalVisitedSites t o s n).card ≤
      n + 1 := by
  simpa [TilingLazyDecomposition.pathPhasedExternalVisitedSites,
    finitePathList] using
    phasedExternalVisitedSites_card_le_length t o
      (finitePathList (pathPrefix s n))

theorem lintegral_tilingRandomClockVisitedSites_card_le
    (t : TilingLazyDecomposition.DominoTiling)
    (m cutoff : ℕ) (band : RandomClockBand) :
    ∫⁻ s, (((tilingRandomClockVisitedSites t m cutoff band s).card : ℕ) :
        ℝ≥0∞) ∂simpleRandomWalk ≤ ((cutoff + 1 : ℕ) : ℝ≥0∞) := by
  classical
  calc
    ∫⁻ s, (((tilingRandomClockVisitedSites t m cutoff band s).card : ℕ) :
        ℝ≥0∞) ∂simpleRandomWalk ≤
        ∫⁻ _s, ((cutoff + 1 : ℕ) : ℝ≥0∞) ∂simpleRandomWalk := by
      apply lintegral_mono
      intro s
      have hcard : (tilingRandomClockVisitedSites t m cutoff band s).card ≤
          cutoff + 1 := by
        calc
          (tilingRandomClockVisitedSites t m cutoff band s).card ≤
              pathTruncatedLevelTime m band.oldRank cutoff s + 1 := by
            simpa [tilingRandomClockVisitedSites,
              pathPhaseFilteredExternalVisitedSites, finitePathList] using
              phasedExternalVertexVisitedSites_card_le_length t
                band.orientation
                (externalVertexPhaseOfBool band.vertexPhase)
                (finitePathList (pathPrefix s
                  (pathTruncatedLevelTime m band.oldRank cutoff s)))
          _ ≤ cutoff + 1 := Nat.add_le_add_right
            (pathTruncatedLevelTime_le m band.oldRank cutoff s) 1
      change (((tilingRandomClockVisitedSites t m cutoff band s).card : ℕ) :
        ℝ≥0∞) ≤ ((cutoff + 1 : ℕ) : ℝ≥0∞)
      exact_mod_cast hcard
    _ = ((cutoff + 1 : ℕ) : ℝ≥0∞) := by simp

/-- The sole external-chain estimate needed by the exact all-tiling screen.
It contains a weighted one-site estimate and the elementary first-moment
bound for the state-dependent external range, but no stopped conditional
disintegration or insertion-product assertion. -/
structure TilingStoppedExternalOnePointData
    (t : TilingLazyDecomposition.DominoTiling)
    (m cutoff : ℕ) (band : RandomClockBand) where
  cutoff_le : cutoff ≤ ExternalProposition44.hlozCutoff44 m
  threshold_margin : ExternalProposition44.hlozOnePointLevel44 m + 1 ≤
    band.externalThreshold
  weighted : ∀ x : Point,
    simpleRandomWalk
        (candidateEvent (tilingRandomClockVisitedSites t m cutoff band)
          (tilingRandomClockExternalLargeEvent t m cutoff band) x) ≤
      ExternalProposition44.hlozOnePointRate44 m * simpleRandomWalk
        (memberEvent (tilingRandomClockVisitedSites t m cutoff band) x)

/-- Product screens for the exact all-tiling shell occupancy. -/
structure TilingBandInterfaceScreen
    (t : TilingLazyDecomposition.DominoTiling)
    (m cutoff : ℕ) (band : RandomClockBand) where
  balanced : ℕ → Set WalkPath
  balanceLaw : ∀ j,
    GeometricBalanceLaw (Site := Point) simpleRandomWalk (balanced j) m
  interfaceLaw : ThresholdedInterfaceProductLaw simpleRandomWalk balanced
    (tilingBandOccupancy t m cutoff band)
    (geometricShellThreshold (initialBudget48 m) shellGrowth48)
    shellGrowth48 (shellCount48 m band.beta)

noncomputable def tilingBandInterfaceOverflowCoefficient
    {t : TilingLazyDecomposition.DominoTiling}
    {m cutoff : ℕ} {band : RandomClockBand}
    (screen : TilingBandInterfaceScreen t m cutoff band) : ℝ≥0∞ :=
  ENNReal.ofReal
    (((ExternalProposition44.hlozOnePointRate44 m *
          ((cutoff + 1 : ℕ) : ℝ≥0∞) /
          initialBudget48 m).toReal) +
      ∑ j ∈ Finset.range (shellCount48 m band.beta - 1),
        ((((screen.balanceLaw j).budget : ℝ≥0∞) *
            (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
              ENNReal.ofReal
                (Real.exp (-17 * balanceRateScale m)))).toReal +
          screen.interfaceLaw.cost j))

/-- Exact per-band state-dependent tiling overflow.  The product part has no
path-probability hypothesis; `onePoint` is precisely the remaining external
one-point input. -/
theorem simpleRandomWalk_tilingRandomClockBandOverflow_le_of_interface
    {t : TilingLazyDecomposition.DominoTiling}
    {m cutoff : ℕ} {band : RandomClockBand}
    (hbudget : CandidateBudgetArithmeticAt m)
    (hbeta : kappaOne ≤ band.beta)
    (onePoint : TilingStoppedExternalOnePointData t m cutoff band)
    (screen : TilingBandInterfaceScreen t m cutoff band) :
    simpleRandomWalk
        {s | candidateBudget48 m band.beta <
          (tilingRandomClockBandSites t m cutoff s band).card} ≤
      tilingBandInterfaceOverflowCoefficient screen := by
  let visited := tilingRandomClockVisitedSites t m cutoff band
  let large := tilingRandomClockExternalLargeEvent t m cutoff band
  let distinguished := tilingRandomClockDistinguishedSites t m cutoff band
  let totalLocalTime := tilingRandomClockTotalLocalTime m cutoff band
  let occupancy := dynamicShellOccupancy visited large distinguished
    totalLocalTime m (shellWidth48 m)
  let threshold := geometricShellThreshold (initialBudget48 m) shellGrowth48
  have hlarge : ∀ x, MeasurableSet (large x) :=
    measurableSet_tilingRandomClockExternalLargeEvent t m cutoff band
  have hbase : simpleRandomWalk.real (shellOverflow occupancy threshold 0) ≤
      (ExternalProposition44.hlozOnePointRate44 m *
        (((cutoff + 1 : ℕ) : ℝ≥0∞)) /
        initialBudget48 m).toReal := by
    exact simpleRandomWalk_real_dynamicShellOverflow_zero_le
      visited large distinguished totalLocalTime m (shellWidth48 m)
      (initialBudget48 m) shellGrowth48
      (ExternalProposition44.hlozOnePointRate44 m)
      (((cutoff + 1 : ℕ) : ℝ≥0∞))
      (by unfold initialBudget48; omega)
      (ExternalWeightedOnePointCanonical.hlozOnePointRate44_ne_top m)
      ENNReal.coe_ne_top
      (measurableSet_memberEvent_tilingRandomClockVisitedSites
        t m cutoff band)
      hlarge onePoint.weighted
      (lintegral_tilingRandomClockVisitedSites_card_le t m cutoff band)
  have hstep : ∀ j, j + 1 < shellCount48 m band.beta →
      shellGrowth48 * threshold j ≤ threshold (j + 1) := by
    intro j _
    exact (geometricShellThreshold_step (initialBudget48 m)
      shellGrowth48 j).le
  have htotal :=
    measureReal_totalOverflow_le_of_geometricBalance_and_interfaceProduct
      simpleRandomWalk screen.balanced occupancy threshold shellGrowth48
      (shellCount48 m band.beta) m hstep screen.balanceLaw
      screen.interfaceLaw hbase
  have hreal : simpleRandomWalk.real
      {s | candidateBudget48 m band.beta <
        (tilingRandomClockBandSites t m cutoff s band).card} ≤
        (ExternalProposition44.hlozOnePointRate44 m *
          (((cutoff + 1 : ℕ) : ℝ≥0∞)) /
          initialBudget48 m).toReal +
        ∑ j ∈ Finset.range (shellCount48 m band.beta - 1),
          ((((screen.balanceLaw j).budget : ℝ≥0∞) *
              (ENNReal.ofReal (Real.exp (-17 * balanceRateScale m)) +
                ENNReal.ofReal
                  (Real.exp (-17 * balanceRateScale m)))).toReal +
            screen.interfaceLaw.cost j) := by
    apply (measureReal_mono ?_).trans htotal
    rw [tilingRandomClockBandOverflow_eq_dynamic]
    exact dynamicStoppedCandidateOverflow48_subset_totalOverflow visited large
      distinguished totalLocalTime m band.beta (hbudget band.beta hbeta)
  rw [← ENNReal.ofReal_toReal (measure_ne_top simpleRandomWalk
    {s | candidateBudget48 m band.beta <
      (tilingRandomClockBandSites t m cutoff s band).card})]
  exact ENNReal.ofReal_mono hreal

/-- Exact finite-band state-dependent overflow, now in the form consumed by
`HLOZTilingGapRandomClockClosure`. -/
theorem eventually_simpleRandomWalk_tilingRandomClockCandidateOverflow_le_sum
    (t : TilingLazyDecomposition.DominoTiling)
    (cutoff : ℕ → ℕ) (bands : ℕ → Finset RandomClockBand)
    (hbeta : ∀ m band, band ∈ bands m → kappaOne ≤ band.beta)
    (onePoint : ∀ m band,
      TilingStoppedExternalOnePointData t m (cutoff m) band)
    (screen : ∀ m band,
      TilingBandInterfaceScreen t m (cutoff m) band) :
    ∀ᶠ m : ℕ in Filter.atTop,
      simpleRandomWalk
          (tilingRandomClockCandidateOverflow t m (cutoff m) (bands m)) ≤
        ∑ band ∈ bands m,
          tilingBandInterfaceOverflowCoefficient (screen m band) := by
  filter_upwards [eventually_candidateBudgetArithmeticAt] with m hbudget
  unfold tilingRandomClockCandidateOverflow candidateOverflow
  refine (Screening.measure_someCandidateBad_le_sum simpleRandomWalk
    (bands m) (fun band ↦
      {s | candidateBudget48 m band.beta <
        (tilingRandomClockBandSites t m (cutoff m) s band).card})).trans ?_
  apply Finset.sum_le_sum
  intro band hband
  exact simpleRandomWalk_tilingRandomClockBandOverflow_le_of_interface
    hbudget (hbeta m band hband) (onePoint m band) (screen m band)

/-! ## Positive-tail assembly from the literal all-six product data -/

/-- Literal product data for every adjacent interface of one all-six band.
The start-level and positivity hypotheses are explicit: no small-level
geometric balance law is manufactured.  Each `product` field ends at a
`TilingRandomTotalProductTailSpec`, whose quantitative conclusion was proved
above from finite normalized coordinate masses. -/
structure AllSixBandProductData
    (t : TilingLazyDecomposition.DominoTiling)
    (m cutoff : ℕ) (band : RandomClockBand) where
  lawStart : ℕ
  balanced : ℕ → Set WalkPath
  balanceLaw : lawStart ≤ m → 0 < m → ∀ j,
    GeometricBalanceLaw (Site := Point) simpleRandomWalk (balanced j) m
  interfaceCost : ℕ → ℝ
  interfaceCost_nonneg : ∀ j, 0 ≤ interfaceCost j
  totalBound : ℕ → ℕ
  product : lawStart ≤ m → 0 < m →
    ∀ j, j < shellCount48 m band.beta - 1 →
      TilingInterfaceProductData t m band.oldRank
        (balanced j ∩ thresholdedGrowthFailure
          (tilingBandOccupancy t m cutoff band)
          (geometricShellThreshold (initialBudget48 m) shellGrowth48)
          shellGrowth48 j)
        (geometricShellThreshold (initialBudget48 m) shellGrowth48)
        shellGrowth48 j (totalBound j) (interfaceCost j)

/-- Assemble the exact all-tiling interface law after the positive-tail
hypotheses have been supplied. -/
def tilingBandInterfaceScreenOfProductData
    {t : TilingLazyDecomposition.DominoTiling}
    {m cutoff : ℕ} {band : RandomClockBand}
    (data : AllSixBandProductData t m cutoff band)
    (hstart : data.lawStart ≤ m) (hm : 0 < m) :
    TilingBandInterfaceScreen t m cutoff band where
  balanced := data.balanced
  balanceLaw := data.balanceLaw hstart hm
  interfaceLaw :=
    { cost := data.interfaceCost
      cost_nonneg := data.interfaceCost_nonneg
      interface_bound := by
        intro j hj
        exact simpleRandomWalk_real_interface_le_of_tilingProduct
          (data.product hstart hm j hj) }

/-- Exact per-band overflow from literal all-six product data. -/
theorem simpleRandomWalk_tilingRandomClockBandOverflow_le_of_productData
    {t : TilingLazyDecomposition.DominoTiling}
    {m cutoff : ℕ} {band : RandomClockBand}
    (hbudget : CandidateBudgetArithmeticAt m)
    (hbeta : kappaOne ≤ band.beta)
    (onePoint : TilingStoppedExternalOnePointData t m cutoff band)
    (data : AllSixBandProductData t m cutoff band)
    (hstart : data.lawStart ≤ m) (hm : 0 < m) :
    simpleRandomWalk
        {s | candidateBudget48 m band.beta <
          (tilingRandomClockBandSites t m cutoff s band).card} ≤
      tilingBandInterfaceOverflowCoefficient
        (tilingBandInterfaceScreenOfProductData data hstart hm) :=
  simpleRandomWalk_tilingRandomClockBandOverflow_le_of_interface hbudget hbeta
    onePoint (tilingBandInterfaceScreenOfProductData data hstart hm)

/-- Totalized coefficient for use in eventual statements.  Only the finite
prefix below `lawStart` is assigned the trivial value one. -/
noncomputable def allSixBandOverflowCoefficient
    {t : TilingLazyDecomposition.DominoTiling}
    {m cutoff : ℕ} {band : RandomClockBand}
    (data : AllSixBandProductData t m cutoff band) : ℝ≥0∞ :=
  if htail : data.lawStart ≤ m ∧ 0 < m then
    tilingBandInterfaceOverflowCoefficient
      (tilingBandInterfaceScreenOfProductData data htail.1 htail.2)
  else 1

/-- Exact all-tiling finite-band overflow from positive-tail product data.
This is the candidate estimate consumed by
`hasGapDeficitReturnHarnack_of_tilingLazyRandomClock_bounds`. -/
theorem eventually_simpleRandomWalk_tilingRandomClockCandidateOverflow_le_sum_of_productData
    (t : TilingLazyDecomposition.DominoTiling)
    (cutoff : ℕ → ℕ) (bands : ℕ → Finset RandomClockBand)
    (hbeta : ∀ m band, band ∈ bands m → kappaOne ≤ band.beta)
    (onePoint : ∀ m band,
      TilingStoppedExternalOnePointData t m (cutoff m) band)
    (data : ∀ m band,
      AllSixBandProductData t m (cutoff m) band)
    (hstart : ∀ᶠ m : ℕ in Filter.atTop,
      ∀ band ∈ bands m, (data m band).lawStart ≤ m) :
    ∀ᶠ m : ℕ in Filter.atTop,
      simpleRandomWalk
          (tilingRandomClockCandidateOverflow t m (cutoff m) (bands m)) ≤
        ∑ band ∈ bands m,
          allSixBandOverflowCoefficient (data m band) := by
  filter_upwards [eventually_candidateBudgetArithmeticAt, hstart,
      eventually_ge_atTop (1 : ℕ)] with m hbudget hstartM hm
  unfold tilingRandomClockCandidateOverflow candidateOverflow
  refine (Screening.measure_someCandidateBad_le_sum simpleRandomWalk
    (bands m) (fun band ↦
      {s | candidateBudget48 m band.beta <
        (tilingRandomClockBandSites t m (cutoff m) s band).card})).trans ?_
  apply Finset.sum_le_sum
  intro band hband
  rw [allSixBandOverflowCoefficient,
    dif_pos ⟨hstartM band hband, hm⟩]
  exact simpleRandomWalk_tilingRandomClockBandOverflow_le_of_productData
    hbudget (hbeta m band hband) (onePoint m band) (data m band)
      (hstartM band hband) hm

end

end Erdos1165.HLOZAllSixBandProductClosure
