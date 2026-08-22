/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfaceActualDeltaInterBaseRatio
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairActualDeltaSelected
import ErdosProblems.Erdos1165.HLOZWeightedRandomTotalProductBound

/-!
# Rank-weighted physical interface screen on the exact pair fibre

The source vector is required to lie in the honest prefix-safe base and to
use every exposed pair coordinate.  The comparison lower row is left
unrestricted, so replacements may cross level `m`; their rank multiplicity
is absorbed by the strict moment slack in the weighted product estimate.
-/

open scoped BigOperators

namespace Erdos1165.HLOZPositiveInterfacePairWeightedScreen

open FiniteDominoProductLaw HeterogeneousProductTail
open HLOZAllSixBandProductClosure
open HLOZAllSixExactCoordinateProductClosure
open HLOZPositiveInterfaceActualDeltaInterBaseRatio
open HLOZPositiveInterfacePairActualDeltaSelected
open HLOZPositiveInterfacePairSupportFiber
open HLOZPositiveInterfacePhysicalWindowRatio
open HLOZPositiveInterfacePhysicalWindows
open HLOZProposition48Candidates
open HLOZSharpProductNumerics
open HLOZSourceOrientedThetaExternalProduct
open HLOZSourceOrientedThetaSourceActualDeltaProduct
open HLOZWeightedRandomTotalProductBound
open LazyDecomposition
open SmallWindow
open TilingCappedMarginalization
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedInsertedLocalTime
open TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The accepted source upper row.  Its prefix-safe intersection is kept
coordinatewise so the replacement lower row can remain unrestricted. -/
def positiveInterfaceExternalPairUpper
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (cap : ℕ)
    (b : TilingAwayDomino t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        eta.1.2))
    (v : Fin ((PositiveInterfaceExternalPairFiber eta).upper cap b)) : Prop :=
  (v : ℕ) ∈ acceptedPhysicalDeficitFailureWindow m width
      (Fintype.card (TilingCoordinatesAt t eta.1.1.start
        eta.1.1.retained b.1)) (shell + 1) ∧
    (v : ℕ) ∈ positiveInterfaceExternalPairBaseWindow eta cap b

/-- The unrestricted replacement row. -/
def positiveInterfaceExternalPairLower
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (cap : ℕ)
    (b : TilingAwayDomino t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        eta.1.2))
    (v : Fin ((PositiveInterfaceExternalPairFiber eta).upper cap b)) : Prop :=
  (v : ℕ) ∈ acceptedPhysicalDeficitFailureWindow m width
    (Fintype.card (TilingCoordinatesAt t eta.1.1.start
      eta.1.1.retained b.1)) shell

instance instDecidablePredPositiveInterfaceExternalPairUpper
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (cap : ℕ) :
    ∀ b, DecidablePred (positiveInterfaceExternalPairUpper eta cap b) :=
  fun b v ↦ by
    unfold positiveInterfaceExternalPairUpper
    infer_instance

instance instDecidablePredPositiveInterfaceExternalPairLower
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (cap : ℕ) :
    ∀ b, DecidablePred (positiveInterfaceExternalPairLower eta cap b) :=
  fun b v ↦ by
    unfold positiveInterfaceExternalPairLower
    infer_instance

/-- The accepted physical rows at two adjacent deficit labels are disjoint.
This pointwise wrapper keeps downstream product arguments from unfolding the
finite physical windows during typeclass synthesis. -/
theorem positiveInterfaceExternalPairUpper_lower_disjoint
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (cap : ℕ)
    (b : PositiveInterfaceExternalPairCoordinate eta)
    (v : Fin ((PositiveInterfaceExternalPairFiber eta).upper cap b)) :
    ¬ (positiveInterfaceExternalPairUpper eta cap b v ∧
      positiveInterfaceExternalPairLower eta cap b v) := by
  rintro ⟨hupper, hlower⟩
  unfold positiveInterfaceExternalPairUpper at hupper
  unfold positiveInterfaceExternalPairLower at hlower
  rw [mem_acceptedPhysicalDeficitFailureWindow] at hupper hlower
  omega

/-- The source screen keeps the honest base, the physical threshold tail,
and the fact that the selected support contains exactly all active pair
coordinates. -/
noncomputable def positiveInterfaceExternalPairSourceScreen
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (cap : ℕ)
    (threshold : ℕ → ℕ) (bound : ℕ)
    (ell : TruncatedTotals
      ((PositiveInterfaceExternalPairFiber eta).upper cap)) : Prop := by
  letI : Fintype (PositiveInterfaceExternalPairCoordinate eta) :=
    instFintypeTilingAwayDomino t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        eta.1.2)
  exact positiveInterfaceExternalPairBaseProp eta cap ell ∧
    randomTotalThresholdedUpperTail
      (positiveInterfaceExternalPairUpper eta cap)
      (positiveInterfaceExternalPairLower eta cap)
      threshold shellGrowth48 shell bound ell ∧
    pairSupport (positiveInterfaceExternalPairUpper eta cap)
      (positiveInterfaceExternalPairLower eta cap) ell = Finset.univ

/-- Normalized away mass of the source screen. -/
noncomputable def positiveInterfaceExternalPairSourceScreenMass
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (cap : ℕ)
    (threshold : ℕ → ℕ) (bound : ℕ) : ℝ :=
  let data := PositiveInterfaceExternalPairFiber eta
  @screenMass
    (TilingAwayDomino t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        eta.1.2))
    (instFintypeTilingAwayDomino t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        eta.1.2))
    (fun a b ↦ Subtype.instDecidableEq a b)
    (tilingAwayPointMass (cap := data.coordinateCap cap) t eta.1.1.start
      eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        eta.1.2))
    (data.upper cap)
    (positiveInterfaceExternalPairSourceScreen eta cap threshold bound)
    (Classical.decPred _)

/-- Number of honest endpoint-increment ranks for this exact pair support. -/
noncomputable def positiveInterfaceExternalPairRankMultiplicity
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) : ℕ := by
  letI : Fintype (PositiveInterfaceExternalPairCoordinate eta) :=
    instFintypeTilingAwayDomino t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        eta.1.2)
  exact 2 * Fintype.card (PositiveInterfaceExternalPairCoordinate eta) + 1

/-- Rank-weighted normalized product tail used by the strict envelope. -/
noncomputable def positiveInterfaceExternalPairWeightedTailMass
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (cap : ℕ)
    (threshold : ℕ → ℕ) (bound : ℕ) : ℝ := by
  let data := PositiveInterfaceExternalPairFiber eta
  let D := supportComplementDistinguished t eta.1.1.start
    eta.1.1.retained eta.1.2
  letI : Fintype (PositiveInterfaceExternalPairCoordinate eta) :=
    instFintypeTilingAwayDomino t eta.1.1.start eta.1.1.retained D
  let weight := tilingAwayPointMass (cap := data.coordinateCap cap) t
    eta.1.1.start eta.1.1.retained D
  exact ∑ ell : TruncatedTotals (data.upper cap),
    if randomTotalThresholdedUpperTail
        (positiveInterfaceExternalPairUpper eta cap)
        (positiveInterfaceExternalPairLower eta cap)
        threshold shellGrowth48 shell bound ell then
      ((2 * (pairSupport (positiveInterfaceExternalPairUpper eta cap)
        (positiveInterfaceExternalPairLower eta cap) ell).card + 1 : ℕ) : ℝ) *
        productPointMass
          (fun (c : PositiveInterfaceExternalPairCoordinate eta)
            (v : Fin (data.upper cap c)) ↦
              coordinateMass weight (data.upper cap) c v) ell
    else 0

/-- Public expansion of the rank-weighted tail with the canonical away
coordinate enumeration fixed. -/
theorem positiveInterfaceExternalPairWeightedTailMass_eq
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (cap : ℕ)
    (threshold : ℕ → ℕ) (bound : ℕ) :
    positiveInterfaceExternalPairWeightedTailMass eta cap threshold bound = by
      let data := PositiveInterfaceExternalPairFiber eta
      let D := supportComplementDistinguished t eta.1.1.start
        eta.1.1.retained eta.1.2
      letI : Fintype (PositiveInterfaceExternalPairCoordinate eta) :=
        instFintypeTilingAwayDomino t eta.1.1.start eta.1.1.retained D
      let weight := tilingAwayPointMass (cap := data.coordinateCap cap) t
        eta.1.1.start eta.1.1.retained D
      exact ∑ ell : TruncatedTotals (data.upper cap),
        if randomTotalThresholdedUpperTail
            (positiveInterfaceExternalPairUpper eta cap)
            (positiveInterfaceExternalPairLower eta cap)
            threshold shellGrowth48 shell bound ell then
          ((2 * (pairSupport (positiveInterfaceExternalPairUpper eta cap)
            (positiveInterfaceExternalPairLower eta cap) ell).card + 1 : ℕ) :
              ℝ) *
            productPointMass
              (fun (c : PositiveInterfaceExternalPairCoordinate eta)
                (v : Fin (data.upper cap c)) ↦
                  coordinateMass weight (data.upper cap) c v) ell
        else 0 := by
  rfl

/-- The exact cap-independent hypotheses needed on every exposed pair
coordinate.  The adjacent-window comparison is stored directly: it may be
proved either on the monotone side of the negative-binomial law or by the
local central-limit estimate. -/
structure PositiveInterfaceExternalPairArithmetic
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (cap : ℕ) : Prop where
  external_pos : 0 < externalThreshold
  width_ge_four : 4 ≤ width
  window_ratio : ∀ b : TilingAwayDomino t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        eta.1.2),
    windowMass
        (Fintype.card (TilingCoordinatesAt t eta.1.1.start
          eta.1.1.retained b.1))
        (acceptedPhysicalDeficitFailureWindow m width
          (Fintype.card (TilingCoordinatesAt t eta.1.1.start
            eta.1.1.retained b.1)) (shell + 1)) ≤
      positiveInterfaceRatioConstant * windowMass
        (Fintype.card (TilingCoordinatesAt t eta.1.1.start
          eta.1.1.retained b.1))
        (acceptedPhysicalDeficitFailureWindow m width
          (Fintype.card (TilingCoordinatesAt t eta.1.1.start
            eta.1.1.retained b.1)) shell)
  boundary_lt : ∀ b : TilingAwayDomino t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        eta.1.2),
    prefixedTilingFixedBoundaryDominoMax eta.1.1.initial.1 eta.1.1.start
        eta.1.1.retained (positiveInterfaceExternalPairTerminal eta) b.1 <
      Fintype.card (TilingCoordinatesAt t eta.1.1.start
          eta.1.1.retained b.1) + max 1 (shell * width)

/-- The balance margin makes the lower comparison row prefix-safe at both
endpoints. -/
theorem positiveInterfaceExternalPairLower_mem_baseWindow
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (cap : ℕ)
    (arith : PositiveInterfaceExternalPairArithmetic eta cap)
    (b : PositiveInterfaceExternalPairCoordinate eta)
    (v : Fin ((PositiveInterfaceExternalPairFiber eta).upper cap b))
    (hv : positiveInterfaceExternalPairLower eta cap b v) :
    (v : ℕ) ∈ positiveInterfaceExternalPairBaseWindow eta cap b := by
  have hwidth : 0 < width := lt_of_lt_of_le (by norm_num) arith.width_ge_four
  have hboundary := arith.boundary_lt b
  unfold positiveInterfaceExternalPairLower at hv
  rw [mem_acceptedPhysicalDeficitFailureWindow] at hv
  unfold positiveInterfaceExternalPairBaseWindow
  rw [Finset.mem_range]
  by_cases hshell : shell = 0
  · subst shell
    simp only [zero_mul, max_eq_left (Nat.zero_le 1)] at hboundary
    omega
  · have hshellPos : 0 < shell := Nat.pos_of_ne_zero hshell
    have hprodPos : 0 < shell * width := Nat.mul_pos hshellPos hwidth
    have hmax : max 1 (shell * width) = shell * width :=
      max_eq_right (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hprodPos))
    rw [hmax] at hboundary
    have hdeficit : shell * width ≤ m -
        (Fintype.card (TilingCoordinatesAt t eta.1.1.start
          eta.1.1.retained b.1) + (v : ℕ)) := by
      rw [← Nat.le_div_iff_mul_le hwidth, hv.2]
    omega

/-- Coordinatewise uniform ratio for the exact external pair fibre. -/
theorem positiveInterfaceExternalPair_coordinateMass_ratio
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (cap : ℕ)
    (arith : PositiveInterfaceExternalPairArithmetic eta cap)
    (b : TilingAwayDomino t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        eta.1.2)) :
    (∑ v : Fin ((PositiveInterfaceExternalPairFiber eta).upper cap b),
      if positiveInterfaceExternalPairUpper eta cap b v then
        coordinateMass
          (tilingAwayPointMass
            (cap := (PositiveInterfaceExternalPairFiber eta).coordinateCap cap)
            t eta.1.1.start eta.1.1.retained
            (supportComplementDistinguished t eta.1.1.start
              eta.1.1.retained eta.1.2))
          ((PositiveInterfaceExternalPairFiber eta).upper cap) b v else 0) ≤
      positiveInterfaceRatioConstant *
        ∑ v : Fin ((PositiveInterfaceExternalPairFiber eta).upper cap b),
          if positiveInterfaceExternalPairLower eta cap b v then
            coordinateMass
              (tilingAwayPointMass
                (cap := (PositiveInterfaceExternalPairFiber eta).coordinateCap
                  cap) t eta.1.1.start eta.1.1.retained
                (supportComplementDistinguished t eta.1.1.start
                  eta.1.1.retained eta.1.2))
              ((PositiveInterfaceExternalPairFiber eta).upper cap) b v else
            0 := by
  let data := PositiveInterfaceExternalPairFiber eta
  let D := supportComplementDistinguished t eta.1.1.start
    eta.1.1.retained eta.1.2
  let i := Fintype.card
    (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1)
  have hiPos : 0 < i := arith.external_pos.trans_le
    (positiveInterfaceExternalPairCoordinateCount_ge_externalThreshold eta
      cap b)
  have hupperUpper : ∀ v ∈ acceptedPhysicalDeficitFailureWindow
      m width i (shell + 1), v < data.upper cap b := by
    intro v hv
    have hvlt := (mem_acceptedPhysicalDeficitFailureWindow.mp hv).1
    change v < max eta.1.1.retainedCount (m + shellWidth48 m) + 1
    omega
  have hlowerUpper : ∀ v ∈ acceptedPhysicalDeficitFailureWindow
      m width i shell, v < data.upper cap b := by
    intro v hv
    have hvlt := (mem_acceptedPhysicalDeficitFailureWindow.mp hv).1
    change v < max eta.1.1.retainedCount (m + shellWidth48 m) + 1
    omega
  have hupperCap : ∀ v ∈ acceptedPhysicalDeficitFailureWindow
      m width i (shell + 1), v ≤ data.coordinateCap cap := by
    intro v hv
    have hvlt := (mem_acceptedPhysicalDeficitFailureWindow.mp hv).1
    change v ≤ max eta.1.1.retainedCount (m + shellWidth48 m) + cap
    omega
  have hlowerCap : ∀ v ∈ acceptedPhysicalDeficitFailureWindow
      m width i shell, v ≤ data.coordinateCap cap := by
    intro v hv
    have hvlt := (mem_acceptedPhysicalDeficitFailureWindow.mp hv).1
    change v ≤ max eta.1.1.retainedCount (m + shellWidth48 m) + cap
    omega
  unfold positiveInterfaceExternalPairUpper
  unfold positiveInterfaceExternalPairLower
  convert
    (tilingAway_coordinateMass_physicalUpperInterBase_le_acceptedLower_of_windowRatio
      t eta.1.1.start eta.1.1.retained D (data.upper cap) b
        (positiveInterfaceExternalPairBaseWindow eta cap b) hiPos
        (arith.window_ratio b) hupperUpper hlowerUpper hupperCap hlowerCap) using 1 <;>
    rfl

/-- A full-support subscreen pays the cardinality of the actual endpoint-rank
index inside the total-dependent weighted tail. -/
theorem fullSupportScreen_rankMultiplicity_le_weightedTail
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    {State : Coordinate → Type*} [∀ c, Fintype (State c)]
    (weight : ∀ c, State c → ℝ)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (threshold : ℕ → ℕ) (j bound : ℕ)
    (screen : (∀ c, State c) → Prop) [DecidablePred screen]
    (hweight : ∀ c v, 0 ≤ weight c v)
    (hscreen : ∀ ell, screen ell →
      randomTotalThresholdedUpperTail upper lower threshold shellGrowth48 j bound ell ∧
        pairSupport upper lower ell = Finset.univ) :
    ((2 * Fintype.card Coordinate + 1 : ℕ) : ℝ) *
        (∑ ell : ∀ c, State c,
          if screen ell then productPointMass weight ell else 0) ≤
      ∑ ell : ∀ c, State c,
        if randomTotalThresholdedUpperTail upper lower threshold shellGrowth48 j bound ell
        then ((2 * (pairSupport upper lower ell).card + 1 : ℕ) : ℝ) *
          productPointMass weight ell
        else 0 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ell _hell
  by_cases hs : screen ell
  · have htail := (hscreen ell hs).1
    have hsupport := (hscreen ell hs).2
    rw [if_pos hs, if_pos htail, hsupport, Finset.card_univ]
  · rw [if_neg hs]
    simp only [mul_zero]
    by_cases htail : randomTotalThresholdedUpperTail upper lower threshold shellGrowth48 j
        bound ell
    · rw [if_pos htail]
      exact mul_nonneg (Nat.cast_nonneg _)
        (Finset.prod_nonneg fun c _ ↦ hweight c (ell c))
    · rw [if_neg htail]

end

end Erdos1165.HLOZPositiveInterfacePairWeightedScreen
