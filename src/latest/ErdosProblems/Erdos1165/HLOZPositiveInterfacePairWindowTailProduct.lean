/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairActualDeltaCapBound
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairWindowTail

/-!
# Finite-product payment for a failed positive-interface window ratio
-/

open scoped BigOperators

namespace Erdos1165.HLOZPositiveInterfacePairWindowTailProduct

open FiniteDominoProductLaw
open HeterogeneousProductTail
open HLOZFiniteProductCoordinateUnion
open HLOZNegativeBinomialTruncation
open HLOZPositiveInterfacePairSupportFiber
open HLOZPositiveInterfacePairWeightedScreen
open HLOZPositiveInterfacePhysicalWindowRatio
open HLOZPositiveInterfacePairWindowTail
open HLOZProposition48Candidates
open HLOZSourceOrientedThetaExternalProduct
open HLOZSourceOrientedThetaProduct
open LazyDecomposition
open ScreeningInstantiation
open SmallWindow
open TilingCappedMarginalization
open TilingOrientedSupportAwayCoordinates
open TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The two adjacent physical rows viewed as one coordinate event. -/
def positiveInterfacePairWindow (m width i shell : ℕ) : Finset ℕ :=
  acceptedPhysicalDeficitFailureWindow m width i shell ∪
    acceptedPhysicalDeficitFailureWindow m width i (shell + 1)

/-- The normalized offending-coordinate mass is at most twice its raw
negative-binomial window mass.  The factor two is exactly the finite-
truncation normalization loss. -/
theorem sum_positiveInterfacePairWindow_coordinateMass_le_two_mul_windowMass
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold (shellWidth48 m) shell)
    (cap : ℕ) (b : PositiveInterfaceExternalPairCoordinate eta) :
    (∑ v : Fin ((PositiveInterfaceExternalPairFiber eta).upper cap b),
      if (v : ℕ) ∈ positiveInterfacePairWindow m (shellWidth48 m)
          (Fintype.card
            (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1)) shell
      then
        coordinateMass
          (tilingAwayPointMass
            (cap := (PositiveInterfaceExternalPairFiber eta).coordinateCap cap)
            t eta.1.1.start eta.1.1.retained
            (supportComplementDistinguished t eta.1.1.start
              eta.1.1.retained eta.1.2))
          ((PositiveInterfaceExternalPairFiber eta).upper cap) b v
      else 0) ≤
        2 * windowMass
          (Fintype.card
            (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
          (positiveInterfacePairWindow m (shellWidth48 m)
            (Fintype.card
              (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
            shell) := by
  classical
  let data := PositiveInterfaceExternalPairFiber eta
  let D := supportComplementDistinguished t eta.1.1.start
    eta.1.1.retained eta.1.2
  let pairFintype : Fintype (PositiveInterfaceExternalPairCoordinate eta) :=
    instFintypeTilingAwayDomino t eta.1.1.start eta.1.1.retained D
  let pointMass := tilingAwayPointMass (cap := data.coordinateCap cap) t
    eta.1.1.start eta.1.1.retained D
  let upper := data.upper cap
  let bad := fun c (v : Fin (upper c)) ↦
    (v : ℕ) ∈ positiveInterfacePairWindow m (shellWidth48 m)
      (Fintype.card
        (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained c.1)) shell
  let cost := fun c : PositiveInterfaceExternalPairCoordinate eta ↦
    windowMass
      (Fintype.card
        (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained c.1))
      (positiveInterfacePairWindow m (shellWidth48 m)
        (Fintype.card
          (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained c.1)) shell)
  have hpoint : ∀ c v, 0 ≤ pointMass c v := by
    intro c v
    simpa only [pointMass, D] using
      (externalTheta_pointMass_nonneg data cap c (v : ℕ))
  have hden : ∀ c, (1 / 2 : ℝ) ≤
      ∑ v : Fin (upper c), pointMass c v := by
    intro c
    apply half_le_sum_tilingAwayPointMass t eta.1.1.start eta.1.1.retained D
      c (upper c) (data.upper_pos cap c)
    · dsimp only [upper, data, PositiveInterfaceExternalPairFiber,
        TilingOrientedExternalAllCreationStoppedCoordinate.concreteFiber]
      omega
    · exact card_tilingCoordinatesAt_pos t eta.1.1.start eta.1.1.retained c.1
    · have hcard := card_tilingCoordinatesAt_le_retainedCount_succ t
        eta.1.1.start eta.1.1.retained c.1
      dsimp only [upper, data, PositiveInterfaceExternalPairFiber,
        TilingOrientedExternalAllCreationStoppedCoordinate.concreteFiber]
        at hcard ⊢
      omega
  have hbadRaw : ∀ c, (∑ v : Fin (upper c),
      if bad c v then pointMass c v else 0) ≤ cost c := by
    intro c
    have hwindowUpper : ∀ v ∈ positiveInterfacePairWindow m
        (shellWidth48 m)
        (Fintype.card
          (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained c.1)) shell,
        v < upper c := by
      intro v hv
      unfold positiveInterfacePairWindow at hv
      rw [Finset.mem_union] at hv
      have hvlt :
          Fintype.card
              (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained c.1) + v <
            m := by
        rcases hv with hv | hv
        · exact (mem_acceptedPhysicalDeficitFailureWindow.mp hv).1
        · exact (mem_acceptedPhysicalDeficitFailureWindow.mp hv).1
      dsimp only [upper, data, PositiveInterfaceExternalPairFiber,
        TilingOrientedExternalAllCreationStoppedCoordinate.concreteFiber]
      omega
    have hwindowCap : ∀ v ∈ positiveInterfacePairWindow m
        (shellWidth48 m)
        (Fintype.card
          (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained c.1)) shell,
        v ≤ data.coordinateCap cap := by
      intro v hv
      unfold positiveInterfacePairWindow at hv
      rw [Finset.mem_union] at hv
      have hvlt :
          Fintype.card
              (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained c.1) + v <
            m := by
        rcases hv with hv | hv
        · exact (mem_acceptedPhysicalDeficitFailureWindow.mp hv).1
        · exact (mem_acceptedPhysicalDeficitFailureWindow.mp hv).1
      dsimp only [data, PositiveInterfaceExternalPairFiber,
        TilingOrientedExternalAllCreationStoppedCoordinate.concreteFiber]
      omega
    have heq := sum_tilingAwayPointMass_window t eta.1.1.start
      eta.1.1.retained D c (upper c)
      (positiveInterfacePairWindow m (shellWidth48 m)
        (Fintype.card
          (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained c.1)) shell)
      hwindowUpper hwindowCap
      (card_tilingCoordinatesAt_pos t eta.1.1.start eta.1.1.retained c.1)
    simpa only [bad, pointMass, cost] using heq.le
  have hnormalized := sum_bad_coordinateMass_le_two_mul pointMass upper bad
    cost hpoint hden hbadRaw b
  exact hnormalized

/-- A failed ratio makes the normalized mass of the offending coordinate
exponentially small. -/
theorem sum_positiveInterfacePairWindow_coordinateMass_le
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold (shellWidth48 m) shell)
    (cap : ℕ) (b : PositiveInterfaceExternalPairCoordinate eta)
    (harithmetic : HLOZShellZeroReplacementWindows.ShellZeroWindowArithmeticAt m)
    (hwidthFour : 4 ≤ shellWidth48 m)
    (hthick : m / 2 ≤ Fintype.card
      (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
    (him : Fintype.card
      (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1) ≤ m)
    (hfit : (shell + 2) * shellWidth48 m ≤ m)
    (hwidthDeviation :
      24 * (shellWidth48 m : ℝ) ≤ geometricDeviation m)
    (hdeviationLevel : geometricDeviation m ≤ (m : ℝ))
    (hbad : ¬ windowMass
          (Fintype.card
            (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
          (acceptedPhysicalDeficitFailureWindow m (shellWidth48 m)
            (Fintype.card
              (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
            (shell + 1)) ≤
        positiveInterfaceRatioConstant * windowMass
          (Fintype.card
            (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
          (acceptedPhysicalDeficitFailureWindow m (shellWidth48 m)
            (Fintype.card
              (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
            shell)) :
    (∑ v : Fin ((PositiveInterfaceExternalPairFiber eta).upper cap b),
      if (v : ℕ) ∈ positiveInterfacePairWindow m (shellWidth48 m)
          (Fintype.card
            (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1)) shell
      then
        coordinateMass
          (tilingAwayPointMass
            (cap := (PositiveInterfaceExternalPairFiber eta).coordinateCap cap)
            t eta.1.1.start eta.1.1.retained
            (supportComplementDistinguished t eta.1.1.start
              eta.1.1.retained eta.1.2))
          ((PositiveInterfaceExternalPairFiber eta).upper cap) b v
      else 0) ≤
        2 * Real.exp (-17 * balanceRateScale m) := by
  calc
    _ ≤ 2 * windowMass
        (Fintype.card
          (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
        (positiveInterfacePairWindow m (shellWidth48 m)
          (Fintype.card
            (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
          shell) :=
      sum_positiveInterfacePairWindow_coordinateMass_le_two_mul_windowMass
        eta cap b
    _ ≤ 2 * Real.exp (-17 * balanceRateScale m) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact acceptedPhysicalPairWindowMass_le_of_not_windowRatio
        harithmetic hwidthFour hthick him hfit hwidthDeviation
          hdeviationLevel hbad

private theorem screenMass_mono
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (pointMass : Coordinate → ℕ → ℝ) (upper : Coordinate → ℕ)
    (screen₁ screen₂ : TruncatedTotals upper → Prop)
    (hpoint : ∀ c v, 0 ≤ pointMass c v)
    (hsub : ∀ ell, screen₁ ell → screen₂ ell) :
    @screenMass Coordinate _ _ pointMass upper screen₁ (Classical.decPred _) ≤
      @screenMass Coordinate _ _ pointMass upper screen₂
        (Classical.decPred _) := by
  classical
  unfold screenMass
  apply Finset.sum_le_sum
  intro ell _hell
  by_cases h₁ : screen₁ ell
  · rw [if_pos h₁, if_pos (hsub ell h₁)]
  · rw [if_neg h₁]
    by_cases h₂ : screen₂ ell
    · rw [if_pos h₂]
      exact normalizedJointMass_nonneg_of_pointMass_nonneg
        pointMass upper hpoint ell
    · rw [if_neg h₂]

/-- The full source screen is a subscreen of the offending-coordinate tail,
so the same normalized exponential bound applies to it. -/
theorem positiveInterfaceExternalPairSourceScreenMass_le_of_not_windowRatio
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold (shellWidth48 m) shell)
    (cap : ℕ) (threshold : ℕ → ℕ) (bound : ℕ)
    (b : PositiveInterfaceExternalPairCoordinate eta)
    (harithmetic : HLOZShellZeroReplacementWindows.ShellZeroWindowArithmeticAt m)
    (hwidthFour : 4 ≤ shellWidth48 m)
    (hthick : m / 2 ≤ Fintype.card
      (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
    (him : Fintype.card
      (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1) ≤ m)
    (hfit : (shell + 2) * shellWidth48 m ≤ m)
    (hwidthDeviation :
      24 * (shellWidth48 m : ℝ) ≤ geometricDeviation m)
    (hdeviationLevel : geometricDeviation m ≤ (m : ℝ))
    (hbad : ¬ windowMass
          (Fintype.card
            (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
          (acceptedPhysicalDeficitFailureWindow m (shellWidth48 m)
            (Fintype.card
              (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
            (shell + 1)) ≤
        positiveInterfaceRatioConstant * windowMass
          (Fintype.card
            (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
          (acceptedPhysicalDeficitFailureWindow m (shellWidth48 m)
            (Fintype.card
              (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
            shell)) :
    positiveInterfaceExternalPairSourceScreenMass eta cap threshold bound ≤
      2 * Real.exp (-17 * balanceRateScale m) := by
  classical
  let data := PositiveInterfaceExternalPairFiber eta
  let D := supportComplementDistinguished t eta.1.1.start
    eta.1.1.retained eta.1.2
  let pairFintype : Fintype (PositiveInterfaceExternalPairCoordinate eta) :=
    instFintypeTilingAwayDomino t eta.1.1.start eta.1.1.retained D
  let pointMass := tilingAwayPointMass (cap := data.coordinateCap cap) t
    eta.1.1.start eta.1.1.retained D
  let upper := data.upper cap
  let bad : TruncatedTotals upper → Prop := fun ell ↦
    (ell b : ℕ) ∈ positiveInterfacePairWindow m (shellWidth48 m)
      (Fintype.card
        (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1)) shell
  let badDec : DecidablePred bad := fun ell ↦
    Finset.decidableMem (ell b : ℕ)
      (positiveInterfacePairWindow m (shellWidth48 m)
        (Fintype.card
          (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1)) shell)
  have hpoint : ∀ c v, 0 ≤ pointMass c v := by
    intro c v
    simpa only [pointMass, D] using
      (externalTheta_pointMass_nonneg data cap c (v : ℕ))
  have hsub : ∀ ell,
      positiveInterfaceExternalPairSourceScreen eta cap threshold bound ell →
        bad ell := by
    intro ell hs
    have hbSupport : b ∈ pairSupport
        (positiveInterfaceExternalPairUpper eta cap)
        (positiveInterfaceExternalPairLower eta cap) ell := by
      rw [hs.2.2]
      exact Finset.mem_univ b
    simp only [HeterogeneousProductTail.pairSupport, Finset.mem_filter,
      Finset.mem_univ, true_and] at hbSupport
    unfold bad positiveInterfacePairWindow
    rw [Finset.mem_union]
    rcases hbSupport with hbUpper | hbLower
    · exact Or.inr hbUpper.1
    · exact Or.inl hbLower
  have hmono :
      positiveInterfaceExternalPairSourceScreenMass eta cap threshold bound ≤
        @screenMass (PositiveInterfaceExternalPairCoordinate eta) pairFintype
          (fun a b ↦ Subtype.instDecidableEq a b)
          pointMass upper bad badDec := by
    unfold positiveInterfaceExternalPairSourceScreenMass
    change
      @screenMass (PositiveInterfaceExternalPairCoordinate eta) pairFintype
          (fun a b ↦ Subtype.instDecidableEq a b)
          pointMass upper
          (positiveInterfaceExternalPairSourceScreen eta cap threshold bound)
          (Classical.decPred _) ≤
        @screenMass (PositiveInterfaceExternalPairCoordinate eta) pairFintype
          (fun a b ↦ Subtype.instDecidableEq a b)
          pointMass upper bad badDec
    have hdec : badDec = Classical.decPred bad := Subsingleton.elim _ _
    rw [hdec]
    exact screenMass_mono pointMass upper
      (positiveInterfaceExternalPairSourceScreen eta cap threshold bound)
      bad hpoint hsub
  have hsingle :
      @screenMass (PositiveInterfaceExternalPairCoordinate eta) pairFintype
          (fun a b ↦ Subtype.instDecidableEq a b)
          pointMass upper bad badDec =
        ∑ v : Fin (upper b),
          if (v : ℕ) ∈ positiveInterfacePairWindow m (shellWidth48 m)
              (Fintype.card
                (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1))
              shell
          then coordinateMass pointMass upper b v else 0 := by
    have hsum : ∀ c, (∑ v : Fin (upper c),
        coordinateMass pointMass upper c v) = 1 := by
      intro c
      change (∑ v : Fin (data.upper cap c),
        coordinateMass
          (tilingAwayPointMass (cap := data.coordinateCap cap) t
            eta.1.1.start eta.1.1.retained
            (supportComplementDistinguished t eta.1.1.start
              eta.1.1.retained eta.1.2))
          (data.upper cap) c v) = 1
      exact externalTheta_coordinate_sum_eq_one data cap c
    have hraw := screenMass_single_coordinate_eq pointMass upper
      (fun _ v ↦ (v : ℕ) ∈ positiveInterfacePairWindow m (shellWidth48 m)
        (Fintype.card
          (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1)) shell)
      hsum b
    simpa only [bad, badDec] using hraw
  rw [hsingle] at hmono
  exact hmono.trans
    (sum_positiveInterfacePairWindow_coordinateMass_le eta cap b harithmetic
      hwidthFour hthick him hfit hwidthDeviation hdeviationLevel hbad)

end

end Erdos1165.HLOZPositiveInterfacePairWindowTailProduct
