/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZSharpWindowProductClosure
import ErdosProblems.Erdos1165.HLOZCanonicalWindowProductClosure

/-!
# Cofinal-cap sharp-window product screening

The original `TilingSharpWindowTailData` asks every active-window value to
be at most every cap.  At cap zero this is inconsistent as soon as an away
coordinate exists and the active upper window is nonempty.  We record that
obstruction explicitly, then give the corrected interface: the window and
local-CLT facts are required only above a trace-dependent cap start.

This is enough for cap removal.  A bounded cap is dominated by the screen at
the larger of that cap and the cap start, so a uniform product estimate on
the cofinal tail controls the same increasing cap union.
-/

open Filter MeasureTheory Set
open scoped ENNReal BigOperators

namespace Erdos1165.HLOZCofinalSharpWindowProductClosure

open FiniteDominoProductLaw HLOZAllSixBandProductClosure
open HLOZAllSixExactCoordinateProductClosure HLOZSharpProductNumerics
open HLOZCanonicalWindowProductClosure
open HLOZSharpWindowProductClosure HLOZSpatialAdapter
open HeterogeneousProductTail
open HLOZProposition48Candidates NearFavoriteThresholded
open ScreeningInstantiation TilingAwayNegativeBinomial
open TilingCappedMarginalization TilingSpatialInsertionFiber
open TilingLazyDecomposition
open TilingStoppedProductDisintegration TilingVariableStoppedTracePartition
open VariableStoppedTracePartition

noncomputable section

/-! ## The zero-cap obstruction in the old interface -/

/-- The old all-cap sharp-window interface is contradictory at cap zero
whenever there is an away domino in an active coordinate.  The left endpoint
of the active upper window is strictly positive, but `upper_le_cap` forces it
to be at most zero. -/
theorem false_of_tilingSharpWindowTailData_at_zero_cap
    {index : Type*} {piece : index → Set WalkPath} {next : Set WalkPath}
    {m : ℕ} {threshold : ℕ → ℕ} {j bound : ℕ}
    (data : TilingSharpWindowTailData piece next m threshold j bound)
    (hwidth : 0 < shellWidth48 m) (z : index)
    (b : TilingCappedMarginalization.TilingAwayDomino (data.factored.tiling z 0)
      (data.factored.start z 0) (data.factored.retained z 0)
      (data.factored.distinguished z 0))
    (hactive : m / 2 ≤
      Fintype.card (TilingCoordinatesAt (data.factored.tiling z 0)
        (data.factored.start z 0) (data.factored.retained z 0) b.1)) :
    False := by
  let i := Fintype.card (TilingCoordinatesAt (data.factored.tiling z 0)
    (data.factored.start z 0) (data.factored.retained z 0) b.1)
  let v := i / 15 + shellWidth48 m
  have hv : v ∈ activeUpperFailureWindow m i := by
    rw [activeUpperFailureWindow_eq_of_active hactive]
    rw [upperFailureWindow, Finset.mem_Ico]
    omega
  have hvle : v ≤ 0 := data.upper_le_cap z 0 b v hv
  have hvpos : 0 < v := by
    dsimp only [v]
    omega
  omega

/-! ## Cofinal cap removal -/

/-- A capped product certificate whose finite-product bound is needed only
above a trace-dependent cap start.  All path semantics remain those of the
literal unit-cost capped certificate. -/
structure CofinalCappedProductScreenCertificate {index : Type*}
    (piece : index → Set WalkPath) (next : Set WalkPath) (cost : ℝ≥0∞) where
  raw : PreStoppingConditionalLaw.CappedProductScreenCertificate
    piece next (1 : ℝ≥0∞)
  capStart : index → ℕ
  product_bound : ∀ z cap, capStart z ≤ cap →
    raw.productProbability z cap ≤ cost.toReal

/-- Continuity from below only needs a product estimate on a cofinal set of
caps.  Earlier caps are dominated by the screen at `max cap (capStart z)`.
-/
theorem atomwiseRestrictedRealScreen_of_cofinalCappedProductCertificate
    {index : Type*} (piece : index → Set WalkPath) (next : Set WalkPath)
    (cost : ℝ≥0∞) (hcost : cost ≠ ∞)
    (certificate : CofinalCappedProductScreenCertificate piece next cost) :
    AtomwiseRestrictedRealScreen piece next cost := by
  let screenUnion : index → Set WalkPath :=
    fun z ↦ ⋃ cap, certificate.raw.screened z cap
  refine ⟨screenUnion, ?_, ?_, ?_⟩
  · intro z
    exact MeasurableSet.iUnion fun cap ↦
      certificate.raw.measurable_screened z cap
  · exact certificate.raw.next_subset
  · intro z
    let nu := simpleRandomWalk.restrict (piece z)
    have hfinite : ∀ cap,
        nu.real (certificate.raw.screened z cap) ≤
          (cost * simpleRandomWalk (piece z)).toReal := by
      intro cap
      let cap' := max cap (certificate.capStart z)
      have hcap : cap ≤ cap' := Nat.le_max_left _ _
      have hstart : certificate.capStart z ≤ cap' := Nat.le_max_right _ _
      calc
        nu.real (certificate.raw.screened z cap) ≤
            nu.real (certificate.raw.screened z cap') :=
          measureReal_mono (certificate.raw.monotone_screened z hcap)
        _ = certificate.raw.productProbability z cap' *
              nu.real (certificate.raw.fiber z cap') :=
          certificate.raw.disintegrate z cap'
        _ ≤ cost.toReal * nu.real (certificate.raw.fiber z cap') :=
          mul_le_mul_of_nonneg_right
            (certificate.product_bound z cap' hstart) ENNReal.toReal_nonneg
        _ ≤ cost.toReal * nu.real Set.univ := by
          apply mul_le_mul_of_nonneg_left
          · exact measureReal_mono (Set.subset_univ _)
          · exact ENNReal.toReal_nonneg
        _ = (cost * simpleRandomWalk (piece z)).toReal := by
          change cost.toReal *
              ((simpleRandomWalk.restrict (piece z)) Set.univ).toReal = _
          rw [Measure.restrict_apply MeasurableSet.univ]
          simp only [Set.univ_inter]
          rw [ENNReal.toReal_mul]
    apply ENNReal.toReal_mono
      (ENNReal.mul_ne_top hcost (by finiteness))
    change nu (screenUnion z) ≤ cost * simpleRandomWalk (piece z)
    rw [show screenUnion z = ⋃ cap, certificate.raw.screened z cap from rfl]
    rw [(certificate.raw.monotone_screened z).measure_iUnion]
    apply iSup_le
    intro cap
    exact (ENNReal.toReal_le_toReal (by finiteness)
      (ENNReal.mul_ne_top hcost (by finiteness))).mp (hfinite cap)

/-! ## Corrected sharp-window data -/

/-- Literal stopped-fibre sharp-window data with the cap conditions stated
only on a cofinal range.  The Boolean screen and its cap monotonicity remain
part of `factored`; only the deterministic truncation facts acquire the
necessary `capStart z ≤ cap` hypothesis. -/
structure TilingCofinalSharpWindowTailData {index : Type*}
    (piece : index → Set WalkPath) (next : Set WalkPath)
    (m : ℕ) (threshold : ℕ → ℕ) (j bound : ℕ) where
  factored : TilingFactoredStoppedCoordinateData piece next (1 : ℝ≥0∞)
  capStart : index → ℕ
  accepts_iff : ∀ z cap ell,
    factored.accepts z cap ell = true ↔
      randomTotalThresholdedUpperTail
        (fun b (v : Fin (factored.upper z cap b)) ↦
          (v : ℕ) ∈ activeUpperFailureWindow m
            (Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
              (factored.start z cap) (factored.retained z cap) b.1)))
        (fun b (v : Fin (factored.upper z cap b)) ↦
          (v : ℕ) ∈ activeLowerFailureWindow m
            (Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
              (factored.start z cap) (factored.retained z cap) b.1)))
        threshold shellGrowth48 j bound ell
  upper_lt_truncation : ∀ z cap, capStart z ≤ cap →
    ∀ (b : TilingCappedMarginalization.TilingAwayDomino (factored.tiling z cap) (factored.start z cap)
      (factored.retained z cap) (factored.distinguished z cap)) v,
    v ∈ activeUpperFailureWindow m
        (Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
          (factored.start z cap) (factored.retained z cap) b.1)) →
      v < factored.upper z cap b
  lower_lt_truncation : ∀ z cap, capStart z ≤ cap →
    ∀ (b : TilingCappedMarginalization.TilingAwayDomino (factored.tiling z cap) (factored.start z cap)
      (factored.retained z cap) (factored.distinguished z cap)) v,
    v ∈ activeLowerFailureWindow m
        (Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
          (factored.start z cap) (factored.retained z cap) b.1)) →
      v < factored.upper z cap b
  upper_le_cap : ∀ z cap, capStart z ≤ cap →
    ∀ (b : TilingCappedMarginalization.TilingAwayDomino (factored.tiling z cap) (factored.start z cap)
      (factored.retained z cap) (factored.distinguished z cap)) v,
    v ∈ activeUpperFailureWindow m
        (Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
          (factored.start z cap) (factored.retained z cap) b.1)) → v ≤ cap
  lower_le_cap : ∀ z cap, capStart z ≤ cap →
    ∀ (b : TilingCappedMarginalization.TilingAwayDomino (factored.tiling z cap) (factored.start z cap)
      (factored.retained z cap) (factored.distinguished z cap)) v,
    v ∈ activeLowerFailureWindow m
        (Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
          (factored.start z cap) (factored.retained z cap) b.1)) → v ≤ cap

/-- A trace-dependent cap start large enough for every active sharp window,
constructed from a uniform bound on the number of retained coordinates. -/
def sharpWindowCapStart (m retainedBound : ℕ) : ℕ :=
  retainedBound + 1 + 2 * shellWidth48 m

/-- Construct all small-cap fields from a cap-independent retained-length
bound.  A literal stopped fibre only has to prove the genuine strict
truncation of the two windows. -/
noncomputable def cofinalSharpWindowTailDataOfLiteralFactoredData
    {index : Type*} {piece : index → Set WalkPath} {next : Set WalkPath}
    {m : ℕ} {threshold : ℕ → ℕ} {j bound : ℕ}
    (factored : TilingFactoredStoppedCoordinateData piece next (1 : ℝ≥0∞))
    (retainedBound : index → ℕ)
    (retainedCount_le : ∀ z cap,
      factored.retainedCount z cap ≤ retainedBound z)
    (accepts_iff : ∀ z cap ell,
      factored.accepts z cap ell = true ↔
        randomTotalThresholdedUpperTail
          (fun b (v : Fin (factored.upper z cap b)) ↦
            (v : ℕ) ∈ activeUpperFailureWindow m
              (Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
                (factored.start z cap) (factored.retained z cap) b.1)))
          (fun b (v : Fin (factored.upper z cap b)) ↦
            (v : ℕ) ∈ activeLowerFailureWindow m
              (Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
                (factored.start z cap) (factored.retained z cap) b.1)))
          threshold shellGrowth48 j bound ell)
    (upper_lt_truncation : ∀ z cap
      (b : TilingCappedMarginalization.TilingAwayDomino
        (factored.tiling z cap) (factored.start z cap)
        (factored.retained z cap) (factored.distinguished z cap)) v,
      v ∈ activeUpperFailureWindow m
          (Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
            (factored.start z cap) (factored.retained z cap) b.1)) →
        v < factored.upper z cap b)
    (lower_lt_truncation : ∀ z cap
      (b : TilingCappedMarginalization.TilingAwayDomino
        (factored.tiling z cap) (factored.start z cap)
        (factored.retained z cap) (factored.distinguished z cap)) v,
      v ∈ activeLowerFailureWindow m
          (Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
            (factored.start z cap) (factored.retained z cap) b.1)) →
        v < factored.upper z cap b) :
    TilingCofinalSharpWindowTailData piece next m threshold j bound where
  factored := factored
  capStart z := sharpWindowCapStart m (retainedBound z)
  accepts_iff := accepts_iff
  upper_lt_truncation z cap _hcap b v hv :=
    upper_lt_truncation z cap b v hv
  lower_lt_truncation z cap _hcap b v hv :=
    lower_lt_truncation z cap b v hv
  upper_le_cap := by
    intro z cap hcap b v hv
    let i := Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
      (factored.start z cap) (factored.retained z cap) b.1)
    have hicard : i ≤ factored.retainedCount z cap + 1 := by
      dsimp only [i]
      simpa using (Fintype.card_subtype_le
        (fun k : Fin (factored.retainedCount z cap + 1) ↦
          tilingBase (factored.tiling z cap)
            (rawExternalBase (factored.start z cap)
              (factored.retained z cap).1 k) = b.1))
    have hretained := retainedCount_le z cap
    by_cases hi : m / 2 ≤ i
    · have hvlt : v < i / 15 + 2 * shellWidth48 m := by
        rw [activeUpperFailureWindow_eq_of_active hi,
          upperFailureWindow, Finset.mem_Ico] at hv
        exact hv.2
      have hidiv : i / 15 ≤ i := Nat.div_le_self _ _
      unfold sharpWindowCapStart at hcap
      omega
    · rw [activeUpperFailureWindow_eq_empty_of_inactive hi] at hv
      simp at hv
  lower_le_cap := by
    intro z cap hcap b v hv
    let i := Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
      (factored.start z cap) (factored.retained z cap) b.1)
    have hicard : i ≤ factored.retainedCount z cap + 1 := by
      dsimp only [i]
      simpa using (Fintype.card_subtype_le
        (fun k : Fin (factored.retainedCount z cap + 1) ↦
          tilingBase (factored.tiling z cap)
            (rawExternalBase (factored.start z cap)
              (factored.retained z cap).1 k) = b.1))
    have hretained := retainedCount_le z cap
    by_cases hi : m / 2 ≤ i
    · have hvlt : v < i / 15 + shellWidth48 m := by
        rw [activeLowerFailureWindow_eq_of_active hi,
          lowerFailureWindow, Finset.mem_Ico] at hv
        exact hv.2
      have hidiv : i / 15 ≤ i := Nat.div_le_self _ _
      unfold sharpWindowCapStart at hcap
      omega
    · rw [activeLowerFailureWindow_eq_empty_of_inactive hi] at hv
      simp at hv

/-- On the cofinal cap range, the literal normalized away-coordinate product
has the sharp HLOZ interface bound. -/
theorem screenMass_le_sharpInterfaceCost_of_cofinalSharpWindowData
    {index : Type*} {piece : index → Set WalkPath} {next : Set WalkPath}
    {m : ℕ} {threshold : ℕ → ℕ} {j bound : ℕ}
    (harith : SharpWindowArithmeticAt m)
    (data : TilingCofinalSharpWindowTailData
      piece next m threshold j bound)
    (z : index) (cap : ℕ) (hcap : data.capStart z ≤ cap) :
    screenMass
        (tilingAwayPointMass (cap := cap) (data.factored.tiling z cap)
          (data.factored.start z cap) (data.factored.retained z cap)
          (data.factored.distinguished z cap))
        (data.factored.upper z cap)
        (fun ell ↦ data.factored.accepts z cap ell = true) ≤
      sharpInterfaceCost threshold j := by
  let upperWindow := fun
      (b : TilingCappedMarginalization.TilingAwayDomino (data.factored.tiling z cap)
        (data.factored.start z cap) (data.factored.retained z cap)
        (data.factored.distinguished z cap))
      (v : Fin (data.factored.upper z cap b)) ↦
        (v : ℕ) ∈ activeUpperFailureWindow m
          (Fintype.card (TilingCoordinatesAt (data.factored.tiling z cap)
            (data.factored.start z cap) (data.factored.retained z cap) b.1))
  let lowerWindow := fun
      (b : TilingCappedMarginalization.TilingAwayDomino (data.factored.tiling z cap)
        (data.factored.start z cap) (data.factored.retained z cap)
        (data.factored.distinguished z cap))
      (v : Fin (data.factored.upper z cap b)) ↦
        (v : ℕ) ∈ activeLowerFailureWindow m
          (Fintype.card (TilingCoordinatesAt (data.factored.tiling z cap)
            (data.factored.start z cap) (data.factored.retained z cap) b.1))
  let pointMass := tilingAwayPointMass (cap := cap)
    (data.factored.tiling z cap) (data.factored.start z cap)
    (data.factored.retained z cap) (data.factored.distinguished z cap)
  let weight := fun
      (b : TilingCappedMarginalization.TilingAwayDomino (data.factored.tiling z cap)
        (data.factored.start z cap) (data.factored.retained z cap)
        (data.factored.distinguished z cap))
      (v : Fin (data.factored.upper z cap b)) ↦
        coordinateMass pointMass (data.factored.upper z cap) b v
  let (b : TilingCappedMarginalization.TilingAwayDomino (data.factored.tiling z cap)
      (data.factored.start z cap) (data.factored.retained z cap)
      (data.factored.distinguished z cap)) : DecidablePred (upperWindow b) :=
    fun v ↦ Finset.decidableMem v.val _
  let (b : TilingCappedMarginalization.TilingAwayDomino (data.factored.tiling z cap)
      (data.factored.start z cap) (data.factored.retained z cap)
      (data.factored.distinguished z cap)) : DecidablePred (lowerWindow b) :=
    fun v ↦ Finset.decidableMem v.val _
  have hnonneg : ∀ b v, 0 ≤ weight b v := by
    intro b v
    apply coordinateMass_nonneg_of_pointMass_nonneg
    intro b' ell
    exact tilingAwayExactTotalMass_nonneg
      (data.factored.tiling z cap) (data.factored.start z cap)
      (data.factored.retained z cap) (data.factored.distinguished z cap)
      b' ell
  have hsum : ∀ b, (∑ v, weight b v) ≤ 1 := by
    intro b
    exact (sum_coordinateMass_eq_one_of_zero_pos pointMass
      (data.factored.upper z cap)
      (fun b' ell ↦ tilingAwayExactTotalMass_nonneg
        (data.factored.tiling z cap) (data.factored.start z cap)
        (data.factored.retained z cap) (data.factored.distinguished z cap)
        b' ell)
      (data.factored.upper_pos z cap)
      (fun b' ↦ tilingAwayExactTotalMass_zero_pos
        (data.factored.tiling z cap) (data.factored.start z cap)
        (data.factored.retained z cap) (data.factored.distinguished z cap) b')
      b).le
  have hdisjoint : ∀ b v, ¬ (upperWindow b v ∧ lowerWindow b v) := by
    intro b v hv
    let i := Fintype.card (TilingCoordinatesAt (data.factored.tiling z cap)
      (data.factored.start z cap) (data.factored.retained z cap) b.1)
    by_cases hi : m / 2 ≤ i
    · rw [show upperWindow b v ↔
          (v : ℕ) ∈ activeUpperFailureWindow m i by rfl,
        show lowerWindow b v ↔
          (v : ℕ) ∈ activeLowerFailureWindow m i by rfl,
        activeUpperFailureWindow_eq_of_active hi,
        activeLowerFailureWindow_eq_of_active hi] at hv
      rw [upperFailureWindow, Finset.mem_Ico] at hv
      rw [lowerFailureWindow, Finset.mem_Ico] at hv
      omega
    · rw [show upperWindow b v ↔
          (v : ℕ) ∈ activeUpperFailureWindow m i by rfl,
        activeUpperFailureWindow_eq_empty_of_inactive hi] at hv
      simp at hv
  have hratio : ∀ b,
      (∑ v, if upperWindow b v then weight b v else 0) ≤
        (4 / 3 : ℝ) * ∑ v, if lowerWindow b v then weight b v else 0 := by
    intro b
    let i := Fintype.card (TilingCoordinatesAt (data.factored.tiling z cap)
      (data.factored.start z cap) (data.factored.retained z cap) b.1)
    by_cases hi : m / 2 ≤ i
    · have hiFacts := harith.2 i hi
      change
        (∑ v : Fin (data.factored.upper z cap b),
          if (v : ℕ) ∈ activeUpperFailureWindow m i then weight b v else 0) ≤
        (4 / 3 : ℝ) *
          ∑ v : Fin (data.factored.upper z cap b),
            if (v : ℕ) ∈ activeLowerFailureWindow m i then weight b v else 0
      simp only [activeUpperFailureWindow_eq_of_active hi,
        activeLowerFailureWindow_eq_of_active hi]
      refine (tilingAway_coordinateMass_window_ratio_of_localCLT
        (data.factored.tiling z cap) (data.factored.start z cap)
        (data.factored.retained z cap) (data.factored.distinguished z cap)
        (data.factored.upper z cap) b
        (upperFailureWindow i (shellWidth48 m))
        (lowerFailureWindow i (shellWidth48 m))
        (fun v hv ↦ data.upper_lt_truncation z cap hcap b v (by
          rw [activeUpperFailureWindow_eq_of_active hi]
          exact hv))
        (fun v hv ↦ data.lower_lt_truncation z cap hcap b v (by
          rw [activeLowerFailureWindow_eq_of_active hi]
          exact hv))
        (fun v hv ↦ data.upper_le_cap z cap hcap b v (by
          rw [activeUpperFailureWindow_eq_of_active hi]
          exact hv))
        (fun v hv ↦ data.lower_le_cap z cap hcap b v (by
          rw [activeLowerFailureWindow_eq_of_active hi]
          exact hv))
        hiFacts.1 (adjacentWindowRadius_nonneg _)
        (adjacentWindowSeparation_nonneg _) hiFacts.2.1
        (lowerFailureWindow_nonempty harith.1)
        (by simp) (fun _ hv ↦ upperFailureWindow_deviation_le hv)
        (fun _ hv ↦ lowerFailureWindow_deviation_le hv)
        (fun _ hu _ hl ↦ adjacentFailureWindow_deviation_sub_le hu hl)).trans ?_
      apply mul_le_mul_of_nonneg_right hiFacts.2.2
      exact Finset.sum_nonneg fun v _ ↦ by
        split
        · exact hnonneg b v
        · exact le_rfl
    · change
        (∑ v : Fin (data.factored.upper z cap b),
          if (v : ℕ) ∈ activeUpperFailureWindow m i then weight b v else 0) ≤
        (4 / 3 : ℝ) *
          ∑ v : Fin (data.factored.upper z cap b),
            if (v : ℕ) ∈ activeLowerFailureWindow m i then weight b v else 0
      simp only [activeUpperFailureWindow_eq_empty_of_inactive hi,
        activeLowerFailureWindow_eq_empty_of_inactive hi]
      simp
  rw [screenMass_eq_product]
  calc
    (∑ ell,
      if data.factored.accepts z cap ell = true then
        ∏ b, weight b (ell b) else 0) =
        ∑ ell,
          if randomTotalThresholdedUpperTail upperWindow lowerWindow
              threshold shellGrowth48 j bound ell then
            productPointMass weight ell else 0 := by
      apply Finset.sum_congr rfl
      intro ell _
      rw [productPointMass]
      exact if_congr (data.accepts_iff z cap ell) rfl rfl
    _ ≤ sharpInterfaceCost threshold j :=
      randomTotalThresholdedUpperTail_product_bound weight upperWindow lowerWindow
        threshold shellGrowth48 j bound hnonneg hsum hdisjoint (by norm_num)
        (sharpInterfaceCost_nonneg threshold j) hratio
        (fun total _ ↦
          thresholdedProductEnvelope_le_sharpInterfaceCost
            (4 / 3) (by norm_num) four_thirds_le_positiveInterfaceRatioConstant
              threshold j total)

/-- The corrected sharp-window data produces a complete cofinal cap
certificate.  Pointwise factorization supplies the path disintegration;
the preceding theorem supplies only the large-cap product estimate. -/
noncomputable def cofinalCappedProductCertificateOfSharpWindowData
    {index : Type*} {piece : index → Set WalkPath} {next : Set WalkPath}
    {m : ℕ} {threshold : ℕ → ℕ} {j bound : ℕ}
    (harith : SharpWindowArithmeticAt m)
    (data : TilingCofinalSharpWindowTailData
      piece next m threshold j bound) :
    CofinalCappedProductScreenCertificate piece next
      (ENNReal.ofReal (sharpInterfaceCost threshold j)) where
  raw := cappedProductScreenCertificateOfTilingStoppedCoordinateProductSpec
    (tilingStoppedCoordinateProductSpecOfFactoredData data.factored)
  capStart := data.capStart
  product_bound := by
    intro z cap hcap
    change FiniteDominoProductLaw.screenMass
      (tilingAwayPointMass (cap := cap) (data.factored.tiling z cap)
        (data.factored.start z cap) (data.factored.retained z cap)
        (data.factored.distinguished z cap))
      (data.factored.upper z cap)
      (fun ell ↦ data.factored.accepts z cap ell = true) ≤
        (ENNReal.ofReal (sharpInterfaceCost threshold j)).toReal
    simpa only [ENNReal.toReal_ofReal
      (sharpInterfaceCost_nonneg threshold j)] using
      screenMass_le_sharpInterfaceCost_of_cofinalSharpWindowData
        harith data z cap hcap

/-- One adjacent-shell interface using the corrected cofinal sharp-window
certificate. -/
structure TilingCofinalSharpWindowInterfaceProductData
    (t : TilingLazyDecomposition.DominoTiling) (m k : ℕ)
    (next : Set WalkPath) (threshold : ℕ → ℕ)
    (j bound : ℕ) where
  measurable_next : MeasurableSet next
  next_subset_stage : next ⊆ thresholdReachStage m k
  tail : TilingCofinalSharpWindowTailData
    (favoriteTilingStagePiece t m k (thresholdReachStage m k)) next
    m threshold j bound

/-- Countable trace summation for a cofinal sharp-window interface. -/
theorem simpleRandomWalk_real_interface_le_of_cofinalSharpWindowData
    {t : TilingLazyDecomposition.DominoTiling} {m k : ℕ}
    {next : Set WalkPath} {threshold : ℕ → ℕ}
    {j bound : ℕ} (harith : SharpWindowArithmeticAt m)
    (data : TilingCofinalSharpWindowInterfaceProductData
      t m k next threshold j bound) :
    simpleRandomWalk.real next ≤ sharpInterfaceCost threshold j := by
  let cost : ℝ≥0∞ := ENNReal.ofReal (sharpInterfaceCost threshold j)
  let certificate : CofinalCappedProductScreenCertificate
      (favoriteTilingStagePiece t m k (thresholdReachStage m k)) next cost :=
    cofinalCappedProductCertificateOfSharpWindowData harith data.tail
  have hscreen : AtomwiseRestrictedRealScreen
      (favoriteTilingStagePiece t m k (thresholdReachStage m k)) next cost :=
    atomwiseRestrictedRealScreen_of_cofinalCappedProductCertificate
      _ next cost ENNReal.ofReal_ne_top certificate
  have hdomination : PathTransitionDomination
      (favoriteTilingStagePiece t m k (thresholdReachStage m k)) next cost :=
    pathTransitionDomination_of_atomwiseRestrictedRealScreen _
      data.measurable_next ENNReal.ofReal_ne_top hscreen
  have hmeasure : simpleRandomWalk next ≤ cost := by
    have hstage : simpleRandomWalk (thresholdReachStage m k) ≤ 1 := by
      simpa using measure_mono (μ := simpleRandomWalk)
        (subset_univ (thresholdReachStage m k))
    calc
      simpleRandomWalk next ≤
          cost * simpleRandomWalk (thresholdReachStage m k) :=
        measure_next_le_of_atomwiseTransition
          (favoriteTilingStagePiece t m k (thresholdReachStage m k))
          (measurableSet_favoriteTilingStagePiece t m k
            (measurableSet_thresholdReachStage m k))
          (fun _ _ h ↦ disjoint_favoriteTilingStagePiece_of_ne
            t m k (thresholdReachStage m k) h)
          (iUnion_favoriteTilingStagePiece t m k (fun _ hs ↦ hs))
          data.next_subset_stage hdomination
      _ ≤ cost * 1 := by gcongr
      _ = cost := mul_one _
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
  simpa only [Measure.real, cost, ENNReal.toReal_ofReal
    (sharpInterfaceCost_nonneg threshold j)] using hreal

/-! ## Literal all-six positive-shell package -/

/-- Every positive adjacent-shell interface is given by corrected cofinal
sharp-window data.  There is no abstract interface law and no balance-law
input: the balanced event is the whole path space and its zero-cost law is
constructed internally. -/
structure AllSixCofinalSharpWindowBandProductData
    (t : TilingLazyDecomposition.DominoTiling)
    (m cutoff : ℕ) (band : HLOZGapRandomClockScreen.RandomClockBand) where
  lawStart : ℕ
  totalBound : ℕ → ℕ
  product : lawStart ≤ m → 0 < m →
    ∀ shell, shell < shellCount48 m band.beta - 1 →
      TilingCofinalSharpWindowInterfaceProductData t m band.oldRank
        (Set.univ ∩ thresholdedGrowthFailure
          (tilingBandOccupancy t m cutoff band)
          (geometricShellThreshold (initialBudget48 m) shellGrowth48)
          shellGrowth48 shell)
        (geometricShellThreshold (initialBudget48 m) shellGrowth48)
        shell (totalBound shell)

/-- The concrete band screen derived from cofinal sharp-window interfaces.
Its balance budget is definitionally zero. -/
noncomputable def tilingBandInterfaceScreenOfCofinalSharpWindowData
    {t : TilingLazyDecomposition.DominoTiling}
    {m cutoff : ℕ} {band : HLOZGapRandomClockScreen.RandomClockBand}
    (data : AllSixCofinalSharpWindowBandProductData t m cutoff band)
    (hstart : data.lawStart ≤ m) (hm : 0 < m)
    (harith : SharpWindowArithmeticAt m) :
    TilingBandInterfaceScreen t m cutoff band where
  balanced := fun _ ↦ Set.univ
  balanceLaw := fun _ ↦ univGeometricBalanceLaw m hm
  interfaceLaw := {
    cost := fun shell ↦ sharpInterfaceCost
      (geometricShellThreshold (initialBudget48 m) shellGrowth48) shell
    cost_nonneg := fun shell ↦ sharpInterfaceCost_nonneg
      (geometricShellThreshold (initialBudget48 m) shellGrowth48) shell
    interface_bound := by
      intro shell hshell
      exact simpleRandomWalk_real_interface_le_of_cofinalSharpWindowData
        harith (data.product hstart hm shell hshell) }

/-- Exact per-band candidate-overflow estimate from the literal cofinal
sharp-window product package. -/
theorem simpleRandomWalk_tilingRandomClockBandOverflow_le_of_cofinalSharpWindowData
    {t : TilingLazyDecomposition.DominoTiling}
    {m cutoff : ℕ} {band : HLOZGapRandomClockScreen.RandomClockBand}
    (hbudget : HLOZLowScaleCandidateOverflow.CandidateBudgetArithmeticAt m)
    (hbeta : kappaOne ≤ band.beta)
    (onePoint : TilingStoppedExternalOnePointData t m cutoff band)
    (data : AllSixCofinalSharpWindowBandProductData t m cutoff band)
    (hstart : data.lawStart ≤ m) (hm : 0 < m)
    (harith : SharpWindowArithmeticAt m) :
    simpleRandomWalk
        {s | candidateBudget48 m band.beta <
          (HLOZTilingGapRandomClockScreen.tilingRandomClockBandSites
            t m cutoff s band).card} ≤
      tilingBandInterfaceOverflowCoefficient
        (tilingBandInterfaceScreenOfCofinalSharpWindowData
          data hstart hm harith) :=
  simpleRandomWalk_tilingRandomClockBandOverflow_le_of_interface
    hbudget hbeta onePoint
      (tilingBandInterfaceScreenOfCofinalSharpWindowData
        data hstart hm harith)


end

end Erdos1165.HLOZCofinalSharpWindowProductClosure
