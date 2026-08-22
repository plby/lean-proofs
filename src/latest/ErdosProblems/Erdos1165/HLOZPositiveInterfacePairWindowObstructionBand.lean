/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZConcreteFullBetaProductData
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairWindowObstructionSummation
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairZeroPrefixOrigin

/-!
# Concrete band payment for positive-prefix bad-window histories

The raw arithmetic obstruction is first separated from the already-paid
zero-prefix branch.  Every remaining bad adjacent-window witness satisfies
the cap-independent conditions of the bounded-overlap summation.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZPositiveInterfacePairWindowObstructionBand

open ExternalProposition44
open HLOZConcreteFullBetaProductData
open HLOZCandidateLocalBroadThetaProduct
open HLOZCandidateLocalLazyCap
open HLOZFullBetaRegimeSplit
open HLOZGapRandomClockScreen
open HLOZPathEvents
open HLOZPositiveInterfacePairActualDeltaWalkCap
open HLOZPositiveInterfacePairBalancedSeries
open HLOZPositiveInterfacePairSupportFiber
open HLOZPositiveInterfacePairSupportSelector
open HLOZPositiveInterfacePairWindowObstructionSummation
open HLOZPositiveInterfacePairZeroPrefixOrigin
open HLOZPositiveInterfacePhysicalWindowRatio
open HLOZPositiveInterfaceSupportSelector
open HLOZProposition48Candidates
open HLOZRawFullGapProductPromotion
open HLOZRawShellCreationBridge
open HLOZSourceCorrectFullGapClosure
open HLOZSourceCorrectFilteredTransitions
open HLOZSourceOrientedThetaCreationSlots
open HLOZSourceOrientedThetaBalance
open HLOZSourceOrientedExternalLocalTime
open HLOZTilingEndpointBandExtraction
open HLOZTilingGapRandomClockScreen
open HLOZUpperEstimates
open LazyDecomposition
open PathInsertion
open PreStoppingFiber
open ScreeningInstantiation
open SmallWindow
open SpatialInsertionFiber
open TilingLazyDecomposition
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingExternalPhaseSplit
open TilingOrientedRetainedDominoEndpoint
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedInsertedLocalTime
open TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

attribute [local instance] Classical.propDecidable

/-- Uniform scalar facts used by the high/low physical-window split. -/
structure PositiveInterfacePairWindowScaleArithmetic (m : ℕ) : Prop where
  shell_arithmetic :
    HLOZShellZeroReplacementWindows.ShellZeroWindowArithmeticAt m
  width_four : 4 ≤ shellWidth48 m
  width_deviation : 24 * (shellWidth48 m : ℝ) ≤ geometricDeviation m
  deviation_level : geometricDeviation m ≤ (m : ℝ)
  broad_fit : 4 * candidateLocalBroadWidth48 m ≤ m
  broad_tenth : ((4 * candidateLocalBroadWidth48 m : ℕ) : ℝ) ≤
    (m : ℝ) / 10
  thick_nonneg : 0 ≤ hlozThickThresholdReal44 m
  thick_half : m / 2 ≤ hlozThickLevel44 m
  low_dom : ((4 * candidateLocalBroadWidth48 m : ℕ) : ℝ) +
      thetaLowDeviation m ≤
    (16 / 15 : ℝ) * (m : ℝ) ^ (4 / 5 : ℝ)
  theta_level : thetaLowDeviation m ≤ (m : ℝ)

/-- All scalar inputs for the concrete high/low split hold eventually. -/
theorem eventually_positiveInterfacePairWindowScaleArithmetic :
    ∀ᶠ m : ℕ in atTop, PositiveInterfacePairWindowScaleArithmetic m := by
  have hbroadLinear := eventually_const_mul_nat_rpow_le
    (80 : ℝ) (7 / 10 : ℝ) 1 (by norm_num)
  have hbroadFourFifths := eventually_const_mul_nat_rpow_le
    (16 : ℝ) (7 / 10 : ℝ) (4 / 5 : ℝ) (by norm_num)
  have hthetaFourFifths := eventually_const_mul_nat_rpow_le
    (18 : ℝ) (3 / 4 : ℝ) (4 / 5 : ℝ) (by norm_num)
  have hthickLinear := eventually_const_mul_nat_rpow_le
    (16 / 7 : ℝ) (4 / 5 : ℝ) 1 (by norm_num)
  filter_upwards
      [HLOZShellZeroReplacementWindows.eventually_shellZeroWindowArithmeticAt,
        eventually_four_le_shellWidth48,
        HLOZPositiveInterfacePairWindowTail.eventually_twentyFour_shellWidth48_le_geometricDeviation,
        eventually_geometricDeviation_le_half,
        eventually_theta_low_arithmetic, hbroadLinear,
        hbroadFourFifths, hthetaFourFifths, hthickLinear,
        eventually_ge_atTop (2 : ℕ)]
      with m hshell hfour hwidthDeviation hdeviation htheta hlinear
        hbroadPower hthetaPower hthickLinear hm
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hpNonneg : 0 ≤ (m : ℝ) ^ (7 / 10 : ℝ) :=
    Real.rpow_nonneg (Nat.cast_nonneg m) _
  have hpOne : 1 ≤ (m : ℝ) ^ (7 / 10 : ℝ) :=
    Real.one_le_rpow hmR (by norm_num)
  have hbroadLt : (candidateLocalBroadWidth48 m : ℝ) <
      (m : ℝ) ^ (7 / 10 : ℝ) + 1 := by
    exact Nat.ceil_lt_add_one hpNonneg
  have hbroadTwo : (candidateLocalBroadWidth48 m : ℝ) ≤
      2 * (m : ℝ) ^ (7 / 10 : ℝ) := by linarith
  have hforty : ((40 * candidateLocalBroadWidth48 m : ℕ) : ℝ) ≤
      (m : ℝ) := by
    push_cast
    calc
      40 * (candidateLocalBroadWidth48 m : ℝ) ≤
          80 * (m : ℝ) ^ (7 / 10 : ℝ) := by nlinarith
      _ ≤ (m : ℝ) := by simpa only [Real.rpow_one] using hlinear
  have hbroadFit : 4 * candidateLocalBroadWidth48 m ≤ m := by
    have hfortyNat : 40 * candidateLocalBroadWidth48 m ≤ m := by
      exact_mod_cast hforty
    omega
  have hbroadTenth : ((4 * candidateLocalBroadWidth48 m : ℕ) : ℝ) ≤
      (m : ℝ) / 10 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 10)]
    calc
      ((4 * candidateLocalBroadWidth48 m : ℕ) : ℝ) * 10 =
          ((40 * candidateLocalBroadWidth48 m : ℕ) : ℝ) := by
            push_cast
            ring
      _ ≤ (m : ℝ) := hforty
  have hbroadHalf : ((4 * candidateLocalBroadWidth48 m : ℕ) : ℝ) ≤
      (1 / 2 : ℝ) * (m : ℝ) ^ (4 / 5 : ℝ) := by
    push_cast
    have hpower : 16 * (m : ℝ) ^ (7 / 10 : ℝ) ≤
        (m : ℝ) ^ (4 / 5 : ℝ) := hbroadPower
    nlinarith
  have hthetaHalf : thetaLowDeviation m ≤
      (1 / 2 : ℝ) * (m : ℝ) ^ (4 / 5 : ℝ) := by
    unfold thetaLowDeviation
    nlinarith
  refine
    { shell_arithmetic := hshell
      width_four := hfour
      width_deviation := hwidthDeviation
      deviation_level := hdeviation.trans (half_le_self (Nat.cast_nonneg m))
      broad_fit := hbroadFit
      broad_tenth := hbroadTenth
      thick_nonneg := htheta.1
      thick_half := ?_
      low_dom := ?_
      theta_level := htheta.2.2.trans (half_le_self (Nat.cast_nonneg m)) }
  · have hthresholdHalf : (m : ℝ) / 2 ≤ hlozThickThresholdReal44 m := by
      unfold hlozThickThresholdReal44
      have hp : 0 ≤ (m : ℝ) ^ (4 / 5 : ℝ) :=
        Real.rpow_nonneg (Nat.cast_nonneg m) _
      have hpower : (m : ℝ) ^ (4 / 5 : ℝ) ≤ (7 / 16 : ℝ) * m := by
        have hlinear' : (16 / 7 : ℝ) * (m : ℝ) ^ (4 / 5 : ℝ) ≤ m := by
          simpa only [Real.rpow_one] using hthickLinear
        calc
          (m : ℝ) ^ (4 / 5 : ℝ) =
              (7 / 16 : ℝ) * ((16 / 7 : ℝ) *
                (m : ℝ) ^ (4 / 5 : ℝ)) := by ring
          _ ≤ (7 / 16 : ℝ) * m := by gcongr
      calc
        (m : ℝ) / 2 = (15 / 16 : ℝ) * m - (7 / 16 : ℝ) * m := by ring
        _ ≤ (15 / 16 : ℝ) * m - (m : ℝ) ^ (4 / 5 : ℝ) :=
          sub_le_sub_left hpower _
    have hhalfCast : ((m / 2 : ℕ) : ℝ) ≤ (m : ℝ) / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      exact_mod_cast Nat.div_mul_le_self m 2
    have hfloor := Nat.lt_floor_add_one (hlozThickThresholdReal44 m)
    exact_mod_cast (hhalfCast.trans_lt (hthresholdHalf.trans_lt hfloor)).le
  · calc
    ((4 * candidateLocalBroadWidth48 m : ℕ) : ℝ) +
        thetaLowDeviation m ≤
      (m : ℝ) ^ (4 / 5 : ℝ) := by linarith
    _ ≤ (16 / 15 : ℝ) * (m : ℝ) ^ (4 / 5 : ℝ) := by
      have : 0 ≤ (m : ℝ) ^ (4 / 5 : ℝ) :=
        Real.rpow_nonneg (Nat.cast_nonneg m) _
      nlinarith

private theorem deleteTilingBlocks_length_le (t : DominoTiling) (x : Point) :
    ∀ bs : List PathInsertion.Block,
      (deleteTilingBlocks t x bs).length ≤ bs.length := by
  intro bs
  induction bs generalizing x with
  | nil => rfl
  | cons a as ih =>
      simp only [deleteTilingBlocks]
      split
      · exact (ih x).trans (Nat.le_succ _)
      · simp only [List.length_cons]
        exact Nat.succ_le_succ (ih (blockEnd x a))

/-- The retained external word at a physical clock has no more blocks than
that clock has increments. -/
theorem fixedOrientedTypedExternalWordCode_retainedCount_le
    (t : DominoTiling) (o : Orientation) (s : WalkPath) (n : ℕ) :
    (fixedOrientedTypedExternalWordCode t o n s).retainedCount ≤ n := by
  unfold fixedOrientedTypedExternalWordCode
  dsimp only
  refine (deleteTilingBlocks_length_le t _ _).trans ?_
  calc
    (pairDirectionList (orientedIncrementPrefixList o n s)).length ≤
        (orientedIncrementPrefixList o n s).length := by
      rw [pairDirectionList_length]
      omega
    _ ≤ n := by
      cases o <;> simp [orientedIncrementPrefixList, incrementPrefixList]

private theorem creationTimeNat_pos_of_reaches
    {m k : ℕ} {s : WalkPath} (hm : 1 < m) (hk : 0 < k)
    (hreach : ReachesThreshold s m k) :
    0 < creationTimeNat m k s := by
  have hcreation : ThresholdCreation s m k (creationTimeNat m k s) := by
    simpa only [creationTimeNat, hreach, dif_pos] using
      thresholdCreation_natFind hreach
  by_contra hn
  have hzero : creationTimeNat m k s = 0 := Nat.eq_zero_of_not_pos hn
  have hsite := position_mem_thresholdSites_of_creation hk hcreation
  have hlevel := (mem_thresholdSites s _ m _).mp hsite |>.2
  have hlocal : localTime s 0 (s 0) = 1 := by
    simp [localTime, localTimePrefix, pathPrefix]
  rw [hzero, hlocal] at hlevel
  omega

/-- Exact positive-interface support coordinates are strictly below the
current favorite level. -/
theorem positiveInterfaceExternalPairCoordinateCount_lt_level
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (hm : 1 < m) (hk : 0 < k)
    (b : PositiveInterfaceExternalPairCoordinate eta) :
    Fintype.card
      (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1) < m := by
  classical
  have hbS : b.1.1 ∈ eta.1.2 :=
    (away_mem_support_iff t eta.1.1.start eta.1.1.retained eta.1.2
      b.1).1 b.2
  rcases eta.2 with ⟨s, hs⟩
  rw [orientedExternalAllCreationSupportTraceAtom_eq] at hs
  let n := creationTimeNat m k s
  have hbPairDominant : b.1.1 ∈ PositiveInterfacePairSupportAt t o m
      externalThreshold width shell s n := by
    change b.1.1 ∈ PositiveInterfacePairSupportAt t o m externalThreshold
      width shell s n
    dsimp only [n]
    rw [hs.2.2.2]
    exact hbS
  have hbPair : b.1.1 ∈ orientedPositiveInterfacePairSupportAt t o m
      externalThreshold width shell s n :=
    HLOZDominantPositiveInterfaceSupportSelector.orientedDominantPositiveInterfacePairSupportAt_subset_raw
      t o m externalThreshold width shell s n hbPairDominant
  have hbSupport := orientedPositiveInterfacePairSupportAt_subset t o m
    externalThreshold width shell s n hbPair
  unfold orientedPositiveInterfaceSupportAt at hbSupport
  rcases mem_orientedPositiveInterfaceCodeSupport_iff.mp hbSupport with
    ⟨hbRepresented, _hthick, hbBelow⟩
  have hnpos : 0 < n :=
    creationTimeNat_pos_of_reaches hm hk hs.2.1
  have hbBase : IsTilingBase t b.1.1 :=
    isTilingBase_of_tilingBase_eq_self t b.1.1
      (tilingExternalDomino_is_base t
        (fixedOrientedTypedExternalWordCode t o n s).start
        (fixedOrientedTypedExternalWordCode t o n s).retained
        ⟨b.1.1, hbRepresented⟩)
  have hendpointNot : orientedDominoEndpoint t o b.1.1 ∉
      thresholdSites s n m := by
    intro hendpoint
    apply hbBelow
    apply Finset.mem_image.mpr
    refine ⟨orientedDominoEndpoint t o b.1.1, hendpoint, ?_⟩
    exact tilingBase_orientedDominoEndpoint t o b.1.1 hbBase
  have hlocal : localTime s n (orientedDominoEndpoint t o b.1.1) < m := by
    rw [← not_le, ← mem_thresholdSites_iff s n m _ (by omega)]
    exact hendpointNot
  have hcount := orientedThetaCodeExternalCount_fixed_eq_source
    t o s n hs.1 hnpos b.1.1 hbRepresented
  have hcountEta : orientedThetaCodeExternalCount t eta.1.1 b.1.1 =
      tilingSourceExternalBaseLocalTime t o s n
        (orientedDominoEndpoint t o b.1.1) := by
    simpa only [n, hs.2.2.1] using hcount
  rw [orientedThetaCodeExternalCount, dif_pos b.1.2] at hcountEta
  have hcardLe : Fintype.card
        (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1) ≤
      localTime s n (orientedDominoEndpoint t o b.1.1) := by
    calc
      _ = pathPhaseFilteredExternalLocalTime t o false s n
          (orientedDominoEndpoint t o b.1.1) := by
        simpa only [pathPhaseFilteredExternalLocalTime,
          externalVertexPhaseOfBool, tilingSourceExternalBaseLocalTime,
          prefixTilingSourceExternalBaseLocalTime] using hcountEta
      _ ≤ localTime s n (orientedDominoEndpoint t o b.1.1) :=
        pathPhaseFilteredExternalLocalTime_le_localTime t o false s n _
  exact hcardLe.trans_lt hlocal

/-- One fixed-shell bad-window obstruction with the zero-length external word
removed. -/
def bandPositiveInterfacePairPositiveWindowRatioObstructionAtShell
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (o : Orientation) (m : ℕ)
    (band : RandomClockBand) (shell : ℕ) :
    Set WalkPath :=
  positiveInterfaceCreationNoNextProfileEvent m band.oldRank ∩
    bandPositiveInterfaceUnbalancedPairRemainderEvent data t m band ∩
      {s | s ∈ orientedBandPositiveInterfaceFailureEvent t o m band ∧
        ∃ eta : PositiveInterfaceExternalPairSupportedIndex t
            o m band.oldRank 1
              (shellWidth48 m) shell,
          ∃ cap : ℕ,
            eta.1.1 = fixedOrientedTypedExternalWordCode t o
                (creationTimeNat m band.oldRank s) s ∧
              s ∈ positiveInterfaceExternalPairSourceCap eta cap
                (geometricShellThreshold
                  (HLOZDominantPositiveInterfaceBandRecurrence.normalizedPositiveInitialBudget48 m)
                  shellGrowth48)
                (levelCutoffTime upperTailDelta m) ∧
              0 < eta.1.1.initial.1.length + 2 * eta.1.1.retainedCount +
                    eta.1.1.tail.1.length ∧
              ∃ b : PositiveInterfaceExternalPairCoordinate eta,
                ¬windowMass
                    (Fintype.card (TilingCoordinatesAt t eta.1.1.start
                      eta.1.1.retained b.1))
                    (acceptedPhysicalDeficitFailureWindow m (shellWidth48 m)
                      (Fintype.card (TilingCoordinatesAt t eta.1.1.start
                        eta.1.1.retained b.1)) (shell + 1)) ≤
                  positiveInterfaceRatioConstant * windowMass
                    (Fintype.card (TilingCoordinatesAt t eta.1.1.start
                      eta.1.1.retained b.1))
                    (acceptedPhysicalDeficitFailureWindow m (shellWidth48 m)
                      (Fintype.card (TilingCoordinatesAt t eta.1.1.start
                        eta.1.1.retained b.1)) shell)}

/-- High-count bad-window histories, away from the already-paid Proposition
4.4 candidate overflow. -/
def bandPositiveInterfacePairHighWindowRatioObstructionAtShell
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (o : Orientation) (m : ℕ)
    (band : RandomClockBand) (shell : ℕ) :
    Set WalkPath :=
  (bandPositiveInterfacePairPositiveWindowRatioObstructionAtShell
      data t o m band shell ∩
    (orientedThetaCandidateOverflow44 t o m)ᶜ) ∩
      {s | ∃ eta : PositiveInterfaceExternalPairSupportedIndex t
            o m band.oldRank 1
              (shellWidth48 m) shell,
          ∃ cap : ℕ,
            eta.1.1 = fixedOrientedTypedExternalWordCode t o
                (creationTimeNat m band.oldRank s) s ∧
              s ∈ positiveInterfaceExternalPairSourceCap eta cap
                (geometricShellThreshold
                  (HLOZDominantPositiveInterfaceBandRecurrence.normalizedPositiveInitialBudget48 m)
                  shellGrowth48)
                (levelCutoffTime upperTailDelta m) ∧
              0 < eta.1.1.initial.1.length + 2 * eta.1.1.retainedCount +
                    eta.1.1.tail.1.length ∧
              ∃ b : PositiveInterfaceExternalPairCoordinate eta,
                ¬windowMass
                    (Fintype.card (TilingCoordinatesAt t eta.1.1.start
                      eta.1.1.retained b.1))
                    (acceptedPhysicalDeficitFailureWindow m (shellWidth48 m)
                      (Fintype.card (TilingCoordinatesAt t eta.1.1.start
                        eta.1.1.retained b.1)) (shell + 1)) ≤
                  positiveInterfaceRatioConstant * windowMass
                    (Fintype.card (TilingCoordinatesAt t eta.1.1.start
                      eta.1.1.retained b.1))
                    (acceptedPhysicalDeficitFailureWindow m (shellWidth48 m)
                      (Fintype.card (TilingCoordinatesAt t eta.1.1.start
                        eta.1.1.retained b.1)) shell) ∧
                hlozThickLevel44 m ≤ Fintype.card
                  (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1)}

/-- Low-count bad-window histories. -/
def bandPositiveInterfacePairLowWindowRatioObstructionAtShell
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (o : Orientation) (m : ℕ)
    (band : RandomClockBand) (shell : ℕ) :
    Set WalkPath :=
  bandPositiveInterfacePairPositiveWindowRatioObstructionAtShell
      data t o m band shell ∩
    {s | ∃ eta : PositiveInterfaceExternalPairSupportedIndex t
          o m band.oldRank 1
            (shellWidth48 m) shell,
        ∃ cap : ℕ,
          eta.1.1 = fixedOrientedTypedExternalWordCode t o
              (creationTimeNat m band.oldRank s) s ∧
            s ∈ positiveInterfaceExternalPairSourceCap eta cap
              (geometricShellThreshold
                (HLOZDominantPositiveInterfaceBandRecurrence.normalizedPositiveInitialBudget48 m)
                shellGrowth48)
              (levelCutoffTime upperTailDelta m) ∧
            0 < eta.1.1.initial.1.length + 2 * eta.1.1.retainedCount +
                  eta.1.1.tail.1.length ∧
            ∃ b : PositiveInterfaceExternalPairCoordinate eta,
              ¬windowMass
                  (Fintype.card (TilingCoordinatesAt t eta.1.1.start
                    eta.1.1.retained b.1))
                  (acceptedPhysicalDeficitFailureWindow m (shellWidth48 m)
                    (Fintype.card (TilingCoordinatesAt t eta.1.1.start
                      eta.1.1.retained b.1)) (shell + 1)) ≤
                positiveInterfaceRatioConstant * windowMass
                  (Fintype.card (TilingCoordinatesAt t eta.1.1.start
                    eta.1.1.retained b.1))
                  (acceptedPhysicalDeficitFailureWindow m (shellWidth48 m)
                    (Fintype.card (TilingCoordinatesAt t eta.1.1.start
                      eta.1.1.retained b.1)) shell) ∧
              Fintype.card
                  (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1) <
                hlozThickLevel44 m}

/-- The physical bad-window event splits by external count, with only the
high side requiring the Proposition 4.4 overflow exception. -/
theorem
    bandPositiveInterfacePairPositiveWindowAtShell_subset_overflow_union_high_union_low
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (o : Orientation) (m : ℕ)
    (band : RandomClockBand) (shell : ℕ) :
    bandPositiveInterfacePairPositiveWindowRatioObstructionAtShell
        data t o m band shell ⊆
      orientedThetaCandidateOverflow44 t o m ∪
        (bandPositiveInterfacePairHighWindowRatioObstructionAtShell
            data t o m band shell ∪
          bandPositiveInterfacePairLowWindowRatioObstructionAtShell
            data t o m band shell) := by
  intro s hs
  rcases hs with ⟨⟨hprofile, hunbalanced⟩,
    horientedFailure, eta, cap, hcode, hcap, hfixedPos, b, hbad⟩
  have hsOriginal : s ∈
      bandPositiveInterfacePairPositiveWindowRatioObstructionAtShell
        data t o m band shell :=
    ⟨⟨hprofile, hunbalanced⟩, horientedFailure, eta, cap, hcode, hcap,
      hfixedPos, b, hbad⟩
  by_cases hoverflow : s ∈ orientedThetaCandidateOverflow44
      t o m
  · exact Or.inl hoverflow
  · right
    by_cases hhigh : hlozThickLevel44 m ≤ Fintype.card
        (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1)
    · left
      exact ⟨⟨hsOriginal, hoverflow⟩, eta, cap, hcode, hcap, hfixedPos,
        b, hbad, hhigh⟩
    · right
      exact ⟨hsOriginal, eta, cap, hcode, hcap, hfixedPos, b, hbad,
        Nat.lt_of_not_ge hhigh⟩

/-- Finite union of the positive-prefix bad-window shell obstructions. -/
def orientedBandPositiveInterfacePairPositiveWindowRatioObstructionEvent
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (o : Orientation) (m : ℕ)
    (band : RandomClockBand) : Set WalkPath :=
  Screening.someCandidateBad (Finset.range (shellCount48 m band.beta - 1))
    (bandPositiveInterfacePairPositiveWindowRatioObstructionAtShell
      data t o m band)

/-- Finite union of the high-count endpoint-candidate shell obstructions. -/
def orientedBandPositiveInterfacePairHighWindowRatioObstructionEvent
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (o : Orientation) (m : ℕ)
    (band : RandomClockBand) : Set WalkPath :=
  Screening.someCandidateBad (Finset.range (shellCount48 m band.beta - 1))
    (bandPositiveInterfacePairHighWindowRatioObstructionAtShell
      data t o m band)

/-- Finite union of the low-count square-root-tail shell obstructions. -/
def orientedBandPositiveInterfacePairLowWindowRatioObstructionEvent
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (o : Orientation) (m : ℕ)
    (band : RandomClockBand) : Set WalkPath :=
  Screening.someCandidateBad (Finset.range (shellCount48 m band.beta - 1))
    (bandPositiveInterfacePairLowWindowRatioObstructionAtShell
      data t o m band)

def bandPositiveInterfacePairPositiveWindowRatioObstructionEvent
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (band : RandomClockBand) : Set WalkPath :=
  orientedBandPositiveInterfacePairPositiveWindowRatioObstructionEvent
      data t .even m band ∪
    orientedBandPositiveInterfacePairPositiveWindowRatioObstructionEvent
      data t .shifted m band

def bandPositiveInterfacePairHighWindowRatioObstructionEvent
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (band : RandomClockBand) : Set WalkPath :=
  orientedBandPositiveInterfacePairHighWindowRatioObstructionEvent
      data t .even m band ∪
    orientedBandPositiveInterfacePairHighWindowRatioObstructionEvent
      data t .shifted m band

def bandPositiveInterfacePairLowWindowRatioObstructionEvent
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (band : RandomClockBand) : Set WalkPath :=
  orientedBandPositiveInterfacePairLowWindowRatioObstructionEvent
      data t .even m band ∪
    orientedBandPositiveInterfacePairLowWindowRatioObstructionEvent
      data t .shifted m band

def bothOrientationThetaCandidateOverflow44
    (t : DominoTiling) (m : ℕ) : Set WalkPath :=
  orientedThetaCandidateOverflow44 t .even m ∪
    orientedThetaCandidateOverflow44 t .shifted m

/-- The entire positive-window obstruction has one global overflow branch
and the two count-range shell unions. -/
theorem
    bandPositiveInterfacePairPositiveWindow_subset_overflow_union_high_union_low
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (band : RandomClockBand) :
      bandPositiveInterfacePairPositiveWindowRatioObstructionEvent
        data t m band ⊆
      bothOrientationThetaCandidateOverflow44 t m ∪
        (bandPositiveInterfacePairHighWindowRatioObstructionEvent
            data t m band ∪
          bandPositiveInterfacePairLowWindowRatioObstructionEvent
            data t m band) := by
  intro s hs
  rcases hs with hs | hs
  · rcases hs with ⟨shell, hshell, hs⟩
    rcases bandPositiveInterfacePairPositiveWindowAtShell_subset_overflow_union_high_union_low
        data t .even m band shell hs with hoverflow | hhigh | hlow
    · exact Or.inl (Or.inl hoverflow)
    · exact Or.inr (Or.inl (Or.inl ⟨shell, hshell, hhigh⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨shell, hshell, hlow⟩))
  · rcases hs with ⟨shell, hshell, hs⟩
    rcases bandPositiveInterfacePairPositiveWindowAtShell_subset_overflow_union_high_union_low
        data t .shifted m band shell hs with hoverflow | hhigh | hlow
    · exact Or.inl (Or.inr hoverflow)
    · exact Or.inr (Or.inl (Or.inr ⟨shell, hshell, hhigh⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨shell, hshell, hlow⟩))

/-- The high-count part of one fixed shell uses the endpoint-normalized
Proposition 4.4 candidate budget rather than the physical time cutoff. -/
theorem simpleRandomWalk_bandPositiveInterfacePairHighWindowAtShell_le
    {t : DominoTiling} {o : Orientation} {m : ℕ} {band : RandomClockBand}
    (hband : band ∈ sourceProductEndpointBands m
      (sourceCandidateLazyCap48 m)
      (concreteFullBetaProductData.externalThreshold m))
    (hm : 1 < m)
    (harithmetic : HLOZShellZeroReplacementWindows.ShellZeroWindowArithmeticAt m)
    (hwidthFour : 4 ≤ shellWidth48 m)
    (hwidthDeviation : 24 * (shellWidth48 m : ℝ) ≤ geometricDeviation m)
    (hdeviationLevel : geometricDeviation m ≤ (m : ℝ))
    (hthickHalf : m / 2 ≤ hlozThickLevel44 m)
    {shell : ℕ} (hshell : shell ∈
      Finset.range (shellCount48 m band.beta - 1))
    (hbroad : 4 * candidateLocalBroadWidth48 m ≤ m) :
    simpleRandomWalk
        (bandPositiveInterfacePairHighWindowRatioObstructionAtShell
          concreteFullBetaProductData t o m band shell) ≤
      ENNReal.ofReal (2 * Real.exp (-17 * balanceRateScale m)) *
        (3 : ℝ≥0∞) * (2 * hlozSiteBudget44 m : ℕ) := by
  refine simpleRandomWalk_candidateBadWindowEvent_le
    (t := t) (o := o) (m := m) (k := band.oldRank)
    (externalThreshold := 1) (shell := shell)
    (B := hlozSiteBudget44 m) hm band.oldRank_pos
    (geometricShellThreshold
      (HLOZDominantPositiveInterfaceBandRecurrence.normalizedPositiveInitialBudget48 m)
      shellGrowth48)
    (levelCutoffTime upperTailDelta m)
    (bandPositiveInterfacePairHighWindowRatioObstructionAtShell
      concreteFullBetaProductData t o m band shell)
    harithmetic hwidthFour hwidthDeviation hdeviationLevel ?_
  intro s hs
  rcases hs with ⟨⟨horiginal, hoverflow⟩,
    eta, cap, hcode, hcap, hfixedPos, b, hbad, hhigh⟩
  rcases horiginal with ⟨⟨hprofile, hunbalanced⟩,
    _horientedFailure, _hwitness⟩
  refine ⟨eta, cap, b, ?_, hcap⟩
  have hclock : creationTimeNat m band.oldRank s ≤
      levelCutoffTime upperTailDelta m :=
    bandPositiveInterfaceFailureEvent_subset_earlyCreationStage
      concreteFullBetaProductData t m band hunbalanced.1
  have hclockCut : creationTimeNat m band.oldRank s ≤ hlozCutoff44 m := by
    simpa only [
      HLOZLowGapProductEndgame.levelCutoffTime_upperTailDelta_eq_hlozCutoff44]
      using hclock
  have hvalid : s ∈ validStepWalk := hcap.1
  have hreach : ReachesThreshold s m band.oldRank := by
    have hmpos : 0 < m := by omega
    rw [positiveInterfaceCreationNoNextProfileEvent, if_pos hmpos] at hprofile
    rcases hprofile with ⟨n, hcreation, _hnext⟩
    exact ⟨n, hcreation.1⟩
  have hcreation : 0 < creationTimeNat m band.oldRank s :=
    creationTimeNat_pos_of_reaches hm band.oldRank_pos hreach
  have hcandidate : orientedDominoEndpoint t o b.1.1 ∈
      orientedThetaCodeEndpointCandidateSites44 t o m
        eta.1.1 := by
    unfold orientedThetaCodeEndpointCandidateSites44
    rw [Finset.mem_image]
    refine ⟨b.1.1, ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨b.1.2, ?_⟩
    rw [orientedThetaCodeExternalCount, dif_pos b.1.2]
    exact hhigh
  have hcandidateCard :
      (orientedThetaCodeEndpointCandidateSites44 t o m
        eta.1.1).card ≤ hlozSiteBudget44 m := by
    rw [hcode]
    exact orientedThetaCreationEndpointCandidateSites44_card_le
      hvalid hcreation hclockCut hoverflow
  have hthick : hlozThickLevel44 m ≤ Fintype.card
      (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1) := by
    exact hhigh
  have him : Fintype.card
      (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1) ≤ m :=
    (positiveInterfaceExternalPairCoordinateCount_lt_level eta hm
      band.oldRank_pos b).le
  have hfit : (shell + 2) * shellWidth48 m ≤ m :=
    (positiveInterface_shell_loss_le (by omega)
      (sourceProductEndpointBand_betaLower hband)
      (sourceProductEndpointBand_betaUpperRange hband) hshell).trans hbroad
  exact ⟨hcandidate, hcandidateCard, hfixedPos,
    hthickHalf.trans hthick, him, hfit, hbad⟩

/-- The low-count part of one fixed shell receives the stronger square-root
exponential coordinate tail. -/
theorem simpleRandomWalk_bandPositiveInterfacePairLowWindowAtShell_le
    {t : DominoTiling} {o : Orientation} {m : ℕ} {band : RandomClockBand}
    (hband : band ∈ sourceProductEndpointBands m
      (sourceCandidateLazyCap48 m)
      (concreteFullBetaProductData.externalThreshold m))
    (hm : 1 < m)
    (hwidthPos : 0 < shellWidth48 m)
    {shell : ℕ} (hshell : shell ∈
      Finset.range (shellCount48 m band.beta - 1))
    (hbroad : 4 * candidateLocalBroadWidth48 m ≤ m)
    (hcombinedWidth : ((((shell + 2) * shellWidth48 m : ℕ) : ℝ)) ≤
      (m : ℝ) / 10)
    (hthreshold0 : 0 ≤ hlozThickThresholdReal44 m)
    (hdom : ((((shell + 2) * shellWidth48 m : ℕ) : ℝ)) +
        thetaLowDeviation m ≤
      (16 / 15 : ℝ) * (m : ℝ) ^ (4 / 5 : ℝ))
    (htheta : thetaLowDeviation m ≤
      (m + (shell + 2) * shellWidth48 m : ℕ)) :
    simpleRandomWalk
        (bandPositiveInterfacePairLowWindowRatioObstructionAtShell
          concreteFullBetaProductData t o m band shell) ≤
      ENNReal.ofReal (2 * Real.exp (-17 * thetaLowRateScale m)) *
        (3 : ℝ≥0∞) *
          (2 * (levelCutoffTime upperTailDelta m + 1) : ℕ) := by
  refine simpleRandomWalk_lowBadWindowEvent_le
    (t := t) (o := o) (m := m) (k := band.oldRank)
    (externalThreshold := 1) (shell := shell)
    (R := levelCutoffTime upperTailDelta m) hm band.oldRank_pos
    (geometricShellThreshold
      (HLOZDominantPositiveInterfaceBandRecurrence.normalizedPositiveInitialBudget48 m)
      shellGrowth48)
    (levelCutoffTime upperTailDelta m)
    (bandPositiveInterfacePairLowWindowRatioObstructionAtShell
      concreteFullBetaProductData t o m band shell)
    hwidthPos hcombinedWidth hthreshold0 hdom htheta ?_
  intro s hs
  rcases hs with ⟨horiginal,
    eta, cap, _hcodeCopy, hcap, hfixedPos, b, hbad, hlow⟩
  rcases horiginal with ⟨⟨_hprofile, hunbalanced⟩,
    _horientedFailure, _hwitness⟩
  refine ⟨eta, cap, b, ?_, hcap⟩
  have hclock : creationTimeNat m band.oldRank s ≤
      levelCutoffTime upperTailDelta m :=
    bandPositiveInterfaceFailureEvent_subset_earlyCreationStage
      concreteFullBetaProductData t m band hunbalanced.1
  have hretained : eta.1.1.retainedCount ≤
      levelCutoffTime upperTailDelta m := by
    rw [_hcodeCopy]
    exact (fixedOrientedTypedExternalWordCode_retainedCount_le
      t o s (creationTimeNat m band.oldRank s)).trans hclock
  have hfit : (shell + 2) * shellWidth48 m ≤ m :=
    (positiveInterface_shell_loss_le (by omega)
      (sourceProductEndpointBand_betaLower hband)
      (sourceProductEndpointBand_betaUpperRange hband) hshell).trans hbroad
  exact ⟨hretained, hfixedPos, hlow, hfit⟩

/-- Sum of the high-count endpoint-candidate estimates over all displayed
positive shells. -/
theorem simpleRandomWalk_bandPositiveInterfacePairHighWindow_le
    {t : DominoTiling} {m : ℕ} {band : RandomClockBand}
    (hband : band ∈ sourceProductEndpointBands m
      (sourceCandidateLazyCap48 m)
      (concreteFullBetaProductData.externalThreshold m))
    (hm : 1 < m)
    (harithmetic : HLOZShellZeroReplacementWindows.ShellZeroWindowArithmeticAt m)
    (hwidthFour : 4 ≤ shellWidth48 m)
    (hwidthDeviation : 24 * (shellWidth48 m : ℝ) ≤ geometricDeviation m)
    (hdeviationLevel : geometricDeviation m ≤ (m : ℝ))
    (hthickHalf : m / 2 ≤ hlozThickLevel44 m)
    (hbroad : 4 * candidateLocalBroadWidth48 m ≤ m) :
    simpleRandomWalk
        (bandPositiveInterfacePairHighWindowRatioObstructionEvent
          concreteFullBetaProductData t m band) ≤
      (shellCount48 m band.beta : ℕ) *
        (ENNReal.ofReal (2 * Real.exp (-17 * balanceRateScale m)) *
          (3 : ℝ≥0∞) * (2 * hlozSiteBudget44 m : ℕ)) * 2 := by
  let cost : ℝ≥0∞ := ENNReal.ofReal
      (2 * Real.exp (-17 * balanceRateScale m)) *
    (3 : ℝ≥0∞) * (2 * hlozSiteBudget44 m : ℕ)
  have horiented : ∀ o : Orientation,
      simpleRandomWalk
          (orientedBandPositiveInterfacePairHighWindowRatioObstructionEvent
            concreteFullBetaProductData t o m band) ≤
        (shellCount48 m band.beta : ℕ) * cost := by
    intro o
    calc
      simpleRandomWalk
          (orientedBandPositiveInterfacePairHighWindowRatioObstructionEvent
            concreteFullBetaProductData t o m band) ≤
        ∑ shell ∈ Finset.range (shellCount48 m band.beta - 1),
          simpleRandomWalk
            (bandPositiveInterfacePairHighWindowRatioObstructionAtShell
              concreteFullBetaProductData t o m band shell) :=
        Screening.measure_someCandidateBad_le_sum simpleRandomWalk _ _
      _ ≤ ∑ _shell ∈ Finset.range (shellCount48 m band.beta - 1),
          cost := by
        apply Finset.sum_le_sum
        intro shell hshell
        exact simpleRandomWalk_bandPositiveInterfacePairHighWindowAtShell_le
          hband hm harithmetic hwidthFour hwidthDeviation hdeviationLevel
            hthickHalf hshell hbroad
      _ ≤ (shellCount48 m band.beta : ℕ) * cost := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        gcongr
        omega
  calc
    simpleRandomWalk
        (bandPositiveInterfacePairHighWindowRatioObstructionEvent
          concreteFullBetaProductData t m band) ≤
      simpleRandomWalk
          (orientedBandPositiveInterfacePairHighWindowRatioObstructionEvent
            concreteFullBetaProductData t .even m band) +
        simpleRandomWalk
          (orientedBandPositiveInterfacePairHighWindowRatioObstructionEvent
            concreteFullBetaProductData t .shifted m band) := measure_union_le _ _
    _ ≤ (shellCount48 m band.beta : ℕ) * cost +
        (shellCount48 m band.beta : ℕ) * cost :=
      add_le_add (horiented .even) (horiented .shifted)
    _ = (shellCount48 m band.beta : ℕ) * cost * 2 := by ring
    _ = _ := rfl

/-- Sum of the low-count square-root-tail estimates over all displayed
positive shells. -/
theorem simpleRandomWalk_bandPositiveInterfacePairLowWindow_le
    {t : DominoTiling} {m : ℕ} {band : RandomClockBand}
    (hband : band ∈ sourceProductEndpointBands m
      (sourceCandidateLazyCap48 m)
      (concreteFullBetaProductData.externalThreshold m))
    (hm : 1 < m)
    (hwidthPos : 0 < shellWidth48 m)
    (hbroad : 4 * candidateLocalBroadWidth48 m ≤ m)
    (hcombinedWidth : ((4 * candidateLocalBroadWidth48 m : ℕ) : ℝ) ≤
      (m : ℝ) / 10)
    (hthreshold0 : 0 ≤ hlozThickThresholdReal44 m)
    (hdom : ((4 * candidateLocalBroadWidth48 m : ℕ) : ℝ) +
        thetaLowDeviation m ≤
      (16 / 15 : ℝ) * (m : ℝ) ^ (4 / 5 : ℝ))
    (htheta : thetaLowDeviation m ≤ (m : ℝ)) :
    simpleRandomWalk
        (bandPositiveInterfacePairLowWindowRatioObstructionEvent
          concreteFullBetaProductData t m band) ≤
      (shellCount48 m band.beta : ℕ) *
        (ENNReal.ofReal (2 * Real.exp (-17 * thetaLowRateScale m)) *
          (3 : ℝ≥0∞) *
            (2 * (levelCutoffTime upperTailDelta m + 1) : ℕ)) * 2 := by
  let cost : ℝ≥0∞ := ENNReal.ofReal
      (2 * Real.exp (-17 * thetaLowRateScale m)) *
    (3 : ℝ≥0∞) * (2 * (levelCutoffTime upperTailDelta m + 1) : ℕ)
  have horiented : ∀ o : Orientation,
      simpleRandomWalk
          (orientedBandPositiveInterfacePairLowWindowRatioObstructionEvent
            concreteFullBetaProductData t o m band) ≤
        (shellCount48 m band.beta : ℕ) * cost := by
    intro o
    calc
      simpleRandomWalk
          (orientedBandPositiveInterfacePairLowWindowRatioObstructionEvent
            concreteFullBetaProductData t o m band) ≤
        ∑ shell ∈ Finset.range (shellCount48 m band.beta - 1),
          simpleRandomWalk
            (bandPositiveInterfacePairLowWindowRatioObstructionAtShell
              concreteFullBetaProductData t o m band shell) :=
        Screening.measure_someCandidateBad_le_sum simpleRandomWalk _ _
      _ ≤ ∑ _shell ∈ Finset.range (shellCount48 m band.beta - 1),
          cost := by
        apply Finset.sum_le_sum
        intro shell hshell
        have hshellLoss : (shell + 2) * shellWidth48 m ≤
            4 * candidateLocalBroadWidth48 m :=
          positiveInterface_shell_loss_le (by omega)
            (sourceProductEndpointBand_betaLower hband)
            (sourceProductEndpointBand_betaUpperRange hband) hshell
        have hshellLossReal :
            ((((shell + 2) * shellWidth48 m : ℕ) : ℝ)) ≤
              ((4 * candidateLocalBroadWidth48 m : ℕ) : ℝ) := by
          exact_mod_cast hshellLoss
        apply simpleRandomWalk_bandPositiveInterfacePairLowWindowAtShell_le
          hband hm hwidthPos hshell hbroad
        · exact hshellLossReal.trans hcombinedWidth
        · exact hthreshold0
        · linarith
        · refine htheta.trans ?_
          exact_mod_cast Nat.le_add_right m
            ((shell + 2) * shellWidth48 m)
      _ ≤ (shellCount48 m band.beta : ℕ) * cost := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        gcongr
        omega
  calc
    simpleRandomWalk
        (bandPositiveInterfacePairLowWindowRatioObstructionEvent
          concreteFullBetaProductData t m band) ≤
      simpleRandomWalk
          (orientedBandPositiveInterfacePairLowWindowRatioObstructionEvent
            concreteFullBetaProductData t .even m band) +
        simpleRandomWalk
          (orientedBandPositiveInterfacePairLowWindowRatioObstructionEvent
            concreteFullBetaProductData t .shifted m band) := measure_union_le _ _
    _ ≤ (shellCount48 m band.beta : ℕ) * cost +
        (shellCount48 m band.beta : ℕ) * cost :=
      add_le_add (horiented .even) (horiented .shifted)
    _ = (shellCount48 m band.beta : ℕ) * cost * 2 := by ring
    _ = _ := rfl

/-- Correct high/low payment for the complete positive-window obstruction:
one global Proposition 4.4 overflow, a high-count candidate-budget term, and
a low-count square-root-tail term. -/
theorem simpleRandomWalk_bandPositiveInterfacePairPositiveWindow_split_le
    {t : DominoTiling} {m : ℕ} {band : RandomClockBand}
    (hband : band ∈ sourceProductEndpointBands m
      (sourceCandidateLazyCap48 m)
      (concreteFullBetaProductData.externalThreshold m))
    (hm : 1 < m)
    (harithmetic : HLOZShellZeroReplacementWindows.ShellZeroWindowArithmeticAt m)
    (hwidthFour : 4 ≤ shellWidth48 m)
    (hwidthDeviation : 24 * (shellWidth48 m : ℝ) ≤ geometricDeviation m)
    (hdeviationLevel : geometricDeviation m ≤ (m : ℝ))
    (hthickHalf : m / 2 ≤ hlozThickLevel44 m)
    (hbroad : 4 * candidateLocalBroadWidth48 m ≤ m)
    (hcombinedWidth : ((4 * candidateLocalBroadWidth48 m : ℕ) : ℝ) ≤
      (m : ℝ) / 10)
    (hthreshold0 : 0 ≤ hlozThickThresholdReal44 m)
    (hdom : ((4 * candidateLocalBroadWidth48 m : ℕ) : ℝ) +
        thetaLowDeviation m ≤
      (16 / 15 : ℝ) * (m : ℝ) ^ (4 / 5 : ℝ))
    (htheta : thetaLowDeviation m ≤ (m : ℝ)) :
    simpleRandomWalk
        (bandPositiveInterfacePairPositiveWindowRatioObstructionEvent
          concreteFullBetaProductData t m band) ≤
      simpleRandomWalk (bothOrientationThetaCandidateOverflow44 t m) +
        ((shellCount48 m band.beta : ℕ) *
            (ENNReal.ofReal (2 * Real.exp (-17 * balanceRateScale m)) *
              (3 : ℝ≥0∞) * (2 * hlozSiteBudget44 m : ℕ)) * 2 +
          (shellCount48 m band.beta : ℕ) *
            (ENNReal.ofReal (2 * Real.exp (-17 * thetaLowRateScale m)) *
              (3 : ℝ≥0∞) *
                (2 * (levelCutoffTime upperTailDelta m + 1) : ℕ)) * 2) := by
  have hhigh := simpleRandomWalk_bandPositiveInterfacePairHighWindow_le
    (t := t) hband hm harithmetic hwidthFour hwidthDeviation hdeviationLevel
      hthickHalf hbroad
  have hlow := simpleRandomWalk_bandPositiveInterfacePairLowWindow_le
    (t := t) hband hm (by omega) hbroad hcombinedWidth hthreshold0 hdom htheta
  calc
    simpleRandomWalk
        (bandPositiveInterfacePairPositiveWindowRatioObstructionEvent
          concreteFullBetaProductData t m band) ≤
      simpleRandomWalk
        (bothOrientationThetaCandidateOverflow44 t m ∪
          (bandPositiveInterfacePairHighWindowRatioObstructionEvent
              concreteFullBetaProductData t m band ∪
            bandPositiveInterfacePairLowWindowRatioObstructionEvent
              concreteFullBetaProductData t m band)) :=
        measure_mono
          (bandPositiveInterfacePairPositiveWindow_subset_overflow_union_high_union_low
            concreteFullBetaProductData t m band)
    _ ≤ simpleRandomWalk
          (bothOrientationThetaCandidateOverflow44 t m) +
        simpleRandomWalk
          (bandPositiveInterfacePairHighWindowRatioObstructionEvent
              concreteFullBetaProductData t m band ∪
            bandPositiveInterfacePairLowWindowRatioObstructionEvent
              concreteFullBetaProductData t m band) := measure_union_le _ _
    _ ≤ simpleRandomWalk
          (bothOrientationThetaCandidateOverflow44 t m) +
        (simpleRandomWalk
            (bandPositiveInterfacePairHighWindowRatioObstructionEvent
              concreteFullBetaProductData t m band) +
          simpleRandomWalk
            (bandPositiveInterfacePairLowWindowRatioObstructionEvent
              concreteFullBetaProductData t m band)) := by
        gcongr
        exact measure_union_le _ _
    _ ≤ _ := by
      exact add_le_add le_rfl (add_le_add hhigh hlow)

private theorem positiveInterfacePairHighWindowRawCost_eq
    (m : ℕ) :
    ENNReal.ofReal (2 * Real.exp (-17 * balanceRateScale m)) *
        (3 : ℝ≥0∞) * (2 * hlozSiteBudget44 m : ℕ) =
      6 * ((hlozSiteBudget44 m : ℝ≥0∞) * thetaHighOneSlotCost m) := by
  unfold thetaHighOneSlotCost
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_ofNat]
  push_cast
  ring

private theorem positiveInterfacePairLowWindowRawCost_eq
    (m : ℕ) :
    ENNReal.ofReal (2 * Real.exp (-17 * thetaLowRateScale m)) *
        (3 : ℝ≥0∞) *
          (2 * (levelCutoffTime upperTailDelta m + 1) : ℕ) =
      12 * (((hlozCutoff44 m + 1 : ℕ) : ℝ≥0∞) *
        thetaLowOneSlotCost m) := by
  rw [HLOZLowGapProductEndgame.levelCutoffTime_upperTailDelta_eq_hlozCutoff44]
  unfold thetaLowOneSlotCost
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_ofNat]
  push_cast
  ring

/-- The corrected high/low window estimate is a fixed multiple of the
oriented-Theta cost, with only one factor of the level coming from the
number of positive shells. -/
theorem simpleRandomWalk_bandPositiveInterfacePairPositiveWindow_le_cost
    {t : DominoTiling} {m : ℕ} {band : RandomClockBand}
    (hband : band ∈ sourceProductEndpointBands m
      (sourceCandidateLazyCap48 m)
      (concreteFullBetaProductData.externalThreshold m))
    (hm : 1 < m)
    (hscale : PositiveInterfacePairWindowScaleArithmetic m)
    (hcandidate : simpleRandomWalk
        (bothOrientationThetaCandidateOverflow44 t m) ≤
      2 * hlozFailureRate44 m) :
    simpleRandomWalk
        (bandPositiveInterfacePairPositiveWindowRatioObstructionEvent
          concreteFullBetaProductData t m band) ≤
      38 * (m : ℝ≥0∞) * orientedThetaCost m := by
  have hsplit :=
    simpleRandomWalk_bandPositiveInterfacePairPositiveWindow_split_le
      (t := t) hband hm hscale.shell_arithmetic hscale.width_four
        hscale.width_deviation hscale.deviation_level hscale.thick_half
        hscale.broad_fit
        hscale.broad_tenth hscale.thick_nonneg hscale.low_dom
        hscale.theta_level
  rw [positiveInterfacePairHighWindowRawCost_eq,
    positiveInterfacePairLowWindowRawCost_eq] at hsplit
  have hshellNat : shellCount48 m band.beta ≤ m :=
    HLOZSharpPositiveShellNumerics.shellCount48_le_level_of_beta_le_sevenTenths
      (by omega) (sourceProductEndpointBand_betaUpperRange hband)
  have hshell : (shellCount48 m band.beta : ℝ≥0∞) ≤ (m : ℝ≥0∞) := by
    exact_mod_cast hshellNat
  have hfailure : hlozFailureRate44 m ≤ orientedThetaCost m := by
    unfold orientedThetaCost
    exact (le_add_of_nonneg_right zero_le).trans
      (le_add_of_nonneg_right zero_le)
  have hhigh :
      (hlozSiteBudget44 m : ℝ≥0∞) * thetaHighOneSlotCost m ≤
        orientedThetaCost m := by
    unfold orientedThetaCost
    exact (le_add_of_nonneg_left zero_le).trans
      (le_add_of_nonneg_right zero_le)
  have hlow :
      ((hlozCutoff44 m + 1 : ℕ) : ℝ≥0∞) * thetaLowOneSlotCost m ≤
        orientedThetaCost m := by
    unfold orientedThetaCost
    exact le_add_of_nonneg_left zero_le
  have hmOne : (1 : ℝ≥0∞) ≤ (m : ℝ≥0∞) := by
    exact_mod_cast (show 1 ≤ m by omega)
  calc
    simpleRandomWalk
        (bandPositiveInterfacePairPositiveWindowRatioObstructionEvent
          concreteFullBetaProductData t m band) ≤
      simpleRandomWalk
          (bothOrientationThetaCandidateOverflow44 t m) +
        ((shellCount48 m band.beta : ℕ) *
            (6 * ((hlozSiteBudget44 m : ℝ≥0∞) * thetaHighOneSlotCost m)) * 2 +
          (shellCount48 m band.beta : ℕ) *
            (12 * (((hlozCutoff44 m + 1 : ℕ) : ℝ≥0∞) *
              thetaLowOneSlotCost m)) * 2) := hsplit
    _ ≤ 2 * orientedThetaCost m +
        ((m : ℝ≥0∞) * (6 * orientedThetaCost m) * 2 +
          (m : ℝ≥0∞) * (12 * orientedThetaCost m) * 2) := by
      gcongr
      exact hcandidate.trans (by gcongr)
    _ ≤ 2 * (m : ℝ≥0∞) * orientedThetaCost m +
        ((m : ℝ≥0∞) * (6 * orientedThetaCost m) * 2 +
          (m : ℝ≥0∞) * (12 * orientedThetaCost m) * 2) := by
      gcongr
      calc
        (2 : ℝ≥0∞) = 2 * 1 := by simp
        _ ≤ 2 * (m : ℝ≥0∞) := by gcongr
    _ = 38 * (m : ℝ≥0∞) * orientedThetaCost m := by ring

/-- Uniformly over every endpoint band at level `m`, the complete
positive-prefix bad-window obstruction has the target logarithmic-square
probability once `m` is large enough. -/
theorem eventually_all_bandPositiveInterfacePairPositiveWindow_le_exp
    (t : DominoTiling) :
    ∀ᶠ m : ℕ in atTop, ∀ band ∈ sourceProductEndpointBands m
        (sourceCandidateLazyCap48 m)
        (concreteFullBetaProductData.externalThreshold m),
      simpleRandomWalk
          (bandPositiveInterfacePairPositiveWindowRatioObstructionEvent
            concreteFullBetaProductData t m band) ≤
        ENNReal.ofReal (Real.exp (-Real.log (m : ℝ) ^ 2)) := by
  filter_upwards
      [eventually_positiveInterfacePairWindowScaleArithmetic,
        eventually_ge_atTop (2 : ℕ),
        eventually_orientedThetaCandidateOverflow_lt_failureRate t .even,
        eventually_orientedThetaCandidateOverflow_lt_failureRate t .shifted,
        eventually_orientedThetaCost_le_exp 4,
        eventually_level_mul_exp_neg_two_log_sq_le_exp_neg
          (c := 2) (by norm_num),
        HLOZGapBetaNumerics.eventually_nat_mul_exp_neg_two_log_sq_le_exp_neg
          38 (c := 1) (by norm_num)]
      with m hscale hm heven hshifted hcost hlevel hfixed
  intro band hband
  have hcandidate : simpleRandomWalk
        (bothOrientationThetaCandidateOverflow44 t m) ≤
      2 * hlozFailureRate44 m := by
    calc
      simpleRandomWalk (bothOrientationThetaCandidateOverflow44 t m) ≤
          simpleRandomWalk (orientedThetaCandidateOverflow44 t .even m) +
            simpleRandomWalk
              (orientedThetaCandidateOverflow44 t .shifted m) :=
        measure_union_le _ _
      _ ≤ hlozFailureRate44 m + hlozFailureRate44 m :=
        add_le_add heven.le hshifted.le
      _ = 2 * hlozFailureRate44 m := by ring
  have hmeasure :=
    simpleRandomWalk_bandPositiveInterfacePairPositiveWindow_le_cost
      hband (by omega) hscale hcandidate
  calc
    simpleRandomWalk
        (bandPositiveInterfacePairPositiveWindowRatioObstructionEvent
          concreteFullBetaProductData t m band) ≤
      38 * (m : ℝ≥0∞) * orientedThetaCost m := hmeasure
    _ ≤ 38 * (m : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-4 * Real.log (m : ℝ) ^ 2)) := by
      gcongr
    _ ≤ 38 * ENNReal.ofReal
        (Real.exp (-2 * Real.log (m : ℝ) ^ 2)) := by
      rw [mul_assoc]
      gcongr
      convert hlevel using 1 <;> congr 1 <;> ring
    _ ≤ ENNReal.ofReal (Real.exp (-Real.log (m : ℝ) ^ 2)) := by
      convert hfixed using 1 <;> norm_num <;> congr 1 <;> ring

/-- Rankwise finite union of the concrete positive-prefix bad-window
obstructions. -/
def positiveInterfacePairPositiveWindowObstructionUnionAtRank
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ) : Set WalkPath :=
  Screening.someCandidateBad
    (sourceProductEndpointBandsAtRank m (sourceCandidateLazyCap48 m)
      (data.externalThreshold m) rank)
    (bandPositiveInterfacePairPositiveWindowRatioObstructionEvent data t m)

/-- Rankwise finite union of the structural non-dominant endpoint branch. -/
def positiveInterfacePairNonDominantObstructionUnionAtRank
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ) : Set WalkPath :=
  Screening.someCandidateBad
    (sourceProductEndpointBandsAtRank m (sourceCandidateLazyCap48 m)
      (data.externalThreshold m) rank)
    (bandPositiveInterfacePairNonDominantObstructionEvent data t m)

/-- The normalized exact-pair support contains only the canonically dominant
endpoint of each domino, so the residual non-dominant branch is empty. -/
theorem bandPositiveInterfacePairNonDominantObstructionEvent_eq_empty
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (m : ℕ) (band : RandomClockBand) :
    bandPositiveInterfacePairNonDominantObstructionEvent data t m band = ∅ := by
  ext s
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hs
  rcases hs with ⟨_hprofileAndUnbalanced, hwitness⟩
  obtain ⟨o, ho⟩ := hwitness
  have _horientedFailure := ho.1
  obtain ⟨_shell, hshellRest⟩ := ho.2
  have _hshell := hshellRest.1
  obtain ⟨eta, heta⟩ := hshellRest.2
  obtain ⟨_cap, hrest⟩ := heta
  have _hcode := hrest.1
  have _hcap := hrest.2.1
  have hb := hrest.2.2
  obtain ⟨b, hnondominant⟩ := hb
  apply hnondominant
  exact positiveInterfaceExternalPairCoordinate_dominant eta b

theorem positiveInterfacePairNonDominantObstructionUnionAtRank_eq_empty
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ) :
    positiveInterfacePairNonDominantObstructionUnionAtRank data t rank m = ∅ := by
  ext s
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨band, _hband, hs⟩
  rw [bandPositiveInterfacePairNonDominantObstructionEvent_eq_empty] at hs
  exact hs

/-- The finite endpoint-band multiplicity costs only half of the available
logarithmic-square exponent. -/
theorem
    eventually_simpleRandomWalk_positiveInterfacePairPositiveWindowObstructionUnionAtRank_le_exp
    (t : DominoTiling) (rank : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk
          (positiveInterfacePairPositiveWindowObstructionUnionAtRank
            concreteFullBetaProductData t rank m) ≤
        ENNReal.ofReal
          (Real.exp (-(1 / 2 : ℝ) * Real.log (m : ℝ) ^ 2)) := by
  have heach := eventually_all_bandPositiveInterfacePairPositiveWindow_le_exp t
  have habsorb :=
    HLOZGapBetaNumerics.eventually_nat_mul_exp_neg_two_log_sq_le_exp_neg
      (Nat.card CanonicalEndpointLowGapBandTag)
      (c := 1 / 2) (by norm_num)
  filter_upwards [heach, habsorb] with m heachM habsorbM
  let q : ℝ≥0∞ :=
    ENNReal.ofReal (Real.exp (-Real.log (m : ℝ) ^ 2))
  calc
    simpleRandomWalk
        (positiveInterfacePairPositiveWindowObstructionUnionAtRank
          concreteFullBetaProductData t rank m) ≤
      ∑ band ∈ sourceProductEndpointBandsAtRank m
          (sourceCandidateLazyCap48 m)
          (concreteFullBetaProductData.externalThreshold m) rank,
        simpleRandomWalk
          (bandPositiveInterfacePairPositiveWindowRatioObstructionEvent
            concreteFullBetaProductData t m band) := by
      exact Screening.measure_someCandidateBad_le_sum simpleRandomWalk _ _
    _ ≤ ∑ _band ∈ sourceProductEndpointBandsAtRank m
          (sourceCandidateLazyCap48 m)
          (concreteFullBetaProductData.externalThreshold m) rank, q := by
      apply Finset.sum_le_sum
      intro band hband
      exact heachM band (Finset.mem_filter.mp hband).1
    _ ≤ ∑ _band ∈ sourceProductEndpointBands m
          (sourceCandidateLazyCap48 m)
          (concreteFullBetaProductData.externalThreshold m), q := by
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = ((sourceProductEndpointBands m (sourceCandidateLazyCap48 m)
          (concreteFullBetaProductData.externalThreshold m)).card : ℝ≥0∞) *
        q := by simp
    _ ≤ (Nat.card CanonicalEndpointLowGapBandTag : ℝ≥0∞) * q := by
      gcongr
      exact_mod_cast sourceProductEndpointBands_card_le m
        (sourceCandidateLazyCap48 m)
        (concreteFullBetaProductData.externalThreshold m)
    _ ≤ ENNReal.ofReal
        (Real.exp (-(1 / 2 : ℝ) * Real.log (m : ℝ) ^ 2)) := by
      dsimp only [q]
      convert habsorbM using 1 <;> norm_num <;> congr 1 <;> ring

theorem
    simpleRandomWalk_positiveInterfacePairPositiveWindowObstructionUnionAtRank_series_ne_top
    (t : DominoTiling) (rank : ℕ) :
    ∑' m, simpleRandomWalk
        (positiveInterfacePairPositiveWindowObstructionUnionAtRank
          concreteFullBetaProductData t rank m) ≠ ∞ :=
  measure_series_ne_top_of_eventually_exp_neg_log_sq_bound simpleRandomWalk _
    (by norm_num : (0 : ℝ) < 1 / 2)
    (eventually_simpleRandomWalk_positiveInterfacePairPositiveWindowObstructionUnionAtRank_le_exp
      t rank)

/-- After separating the already-paid empty external word, every arithmetic
obstruction is either a positive-prefix bad window or the structural
non-dominant endpoint branch. -/
theorem
    bandPositiveInterfacePairArithmeticObstruction_subset_zero_union_positiveWindow_union_nonDominant
    {data : FullBetaSourceCorrectAllTilingProductData}
    {t : DominoTiling} {m : ℕ} {band : RandomClockBand}
    (hm : 1 < m)
    (hthreshold : 0 < band.externalThreshold)
    (hwidth : 4 ≤ shellWidth48 m) :
    bandPositiveInterfacePairArithmeticObstructionEvent data t m band ⊆
      bandPositiveInterfaceZeroPrefixEvent data t m band ∪
        (bandPositiveInterfacePairPositiveWindowRatioObstructionEvent
            data t m band ∪
          bandPositiveInterfacePairNonDominantObstructionEvent
            data t m band) := by
  classical
  rintro s ⟨hprofileAndUnbalanced, hobstruction⟩
  rcases hprofileAndUnbalanced with ⟨hprofile, hunbalanced⟩
  obtain ⟨o, ho⟩ := hobstruction
  have horientedFailure := ho.1
  obtain ⟨shell, hshellRest⟩ := ho.2
  have hshell := hshellRest.1
  obtain ⟨eta, heta⟩ := hshellRest.2
  obtain ⟨cap, hrest⟩ := heta
  have hcode := hrest.1
  have hcap := hrest.2.1
  have hnotArithmetic := hrest.2.2
  by_cases hzero : eta.1.1.initial.1.length +
      2 * eta.1.1.retainedCount + eta.1.1.tail.1.length = 0
  · left
    refine ⟨hprofile, o, horientedFailure, ?_⟩
    change
      (fixedOrientedTypedExternalWordCode t o
            (creationTimeNat m band.oldRank s) s).initial.1.length +
          2 * (fixedOrientedTypedExternalWordCode t o
            (creationTimeNat m band.oldRank s) s).retainedCount +
          (fixedOrientedTypedExternalWordCode t o
            (creationTimeNat m band.oldRank s) s).tail.1.length = 0
    rw [← hcode]
    exact hzero
  · right
    have hpositive : 0 < eta.1.1.initial.1.length +
        2 * eta.1.1.retainedCount + eta.1.1.tail.1.length :=
      Nat.pos_of_ne_zero hzero
    by_cases hratio : ∀ b : PositiveInterfaceExternalPairCoordinate eta,
        windowMass
            (Fintype.card (TilingCoordinatesAt t eta.1.1.start
              eta.1.1.retained b.1))
            (acceptedPhysicalDeficitFailureWindow m (shellWidth48 m)
              (Fintype.card (TilingCoordinatesAt t eta.1.1.start
                eta.1.1.retained b.1)) (shell + 1)) ≤
          positiveInterfaceRatioConstant * windowMass
            (Fintype.card (TilingCoordinatesAt t eta.1.1.start
              eta.1.1.retained b.1))
            (acceptedPhysicalDeficitFailureWindow m (shellWidth48 m)
              (Fintype.card (TilingCoordinatesAt t eta.1.1.start
                eta.1.1.retained b.1)) shell)
    · by_cases hboundary : ∀ b : PositiveInterfaceExternalPairCoordinate eta,
          prefixedTilingFixedBoundaryDominoMax eta.1.1.initial.1
                eta.1.1.start eta.1.1.retained
                (positiveInterfaceExternalPairTerminal eta) b.1 <
              Fintype.card (TilingCoordinatesAt t eta.1.1.start
                  eta.1.1.retained b.1) +
                max 1 (shell * shellWidth48 m)
      · exact (hnotArithmetic
          { external_pos := by omega
            width_ge_four := hwidth
            window_ratio := hratio
            boundary_lt := hboundary }).elim
      · right
        push_neg at hboundary
        rcases hboundary with ⟨b, hb⟩
        apply bandPositiveInterfacePairBoundaryObstruction_subset_nonDominant
          hm
        exact ⟨⟨hprofile, hunbalanced⟩, o, horientedFailure, shell, hshell,
          eta, cap, hcode, hcap, b, not_lt_of_ge hb⟩
    · left
      push_neg at hratio
      rcases hratio with ⟨b, hb⟩
      have hatShell : s ∈
          bandPositiveInterfacePairPositiveWindowRatioObstructionAtShell
            data t o m band shell :=
        ⟨⟨hprofile, hunbalanced⟩, horientedFailure, eta, cap, hcode, hcap,
          hpositive, b, not_le_of_gt hb⟩
      cases o with
      | even => exact Or.inl ⟨shell, hshell, hatShell⟩
      | shifted => exact Or.inr ⟨shell, hshell, hatShell⟩

/-- Rankwise form of the concrete arithmetic split. -/
theorem
    positiveInterfacePairArithmeticObstructionUnionAtRank_subset_zero_union_positiveWindow_union_nonDominant
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ)
    (hm : 1 < m) (hthreshold : 0 < data.externalThreshold m)
    (hwidth : 4 ≤ shellWidth48 m) :
    positiveInterfacePairArithmeticObstructionUnionAtRank data t rank m ⊆
      positiveInterfaceZeroPrefixPaymentUnionAtRank data t rank m ∪
        (positiveInterfacePairPositiveWindowObstructionUnionAtRank
            data t rank m ∪
          positiveInterfacePairNonDominantObstructionUnionAtRank
            data t rank m) := by
  rintro s ⟨band, hbandRank, hs⟩
  have hband : band ∈ sourceProductEndpointBands m
      (sourceCandidateLazyCap48 m) (data.externalThreshold m) :=
    (Finset.mem_filter.mp hbandRank).1
  have hbandThreshold : band.externalThreshold = data.externalThreshold m :=
    canonicalEndpointLowGapBand_externalThreshold
      (mem_sourceProductEndpointBands_iff.mp hband).1
  rcases
      bandPositiveInterfacePairArithmeticObstruction_subset_zero_union_positiveWindow_union_nonDominant
        (data := data) (t := t) (band := band) hm
          (hbandThreshold.symm ▸ hthreshold) hwidth hs with
    hzero | hwindow | hnonDominant
  · exact Or.inl ⟨band, hbandRank, hzero⟩
  · exact Or.inr (Or.inl ⟨band, hbandRank, hwindow⟩)
  · exact Or.inr (Or.inr ⟨band, hbandRank, hnonDominant⟩)

/-- After normalization, every profiled unbalanced history is paid either by
the empty external word or by the positive-window estimate. -/
theorem
    positiveInterfaceProfiledUnbalancedPairRemainderUnionAtRank_subset_zero_union_positiveWindow
    (data : FullBetaSourceCorrectAllTilingProductData)
    (t : DominoTiling) (rank m : ℕ)
    (hm : 1 < m) (hthreshold : 0 < data.externalThreshold m)
    (hwidth : 4 ≤ shellWidth48 m) :
    positiveInterfaceProfiledUnbalancedPairRemainderUnionAtRank
        data t rank m ⊆
      positiveInterfaceZeroPrefixPaymentUnionAtRank data t rank m ∪
        positiveInterfacePairPositiveWindowObstructionUnionAtRank
          data t rank m := by
  intro s hs
  rcases
      positiveInterfaceProfiledUnbalancedPairRemainderUnionAtRank_subset_split
        data t rank m hm hthreshold hs with hzero | harithmetic
  · exact Or.inl hzero
  · rcases
        positiveInterfacePairArithmeticObstructionUnionAtRank_subset_zero_union_positiveWindow_union_nonDominant
          data t rank m hm hthreshold hwidth harithmetic with
      hzero | hwindow | hnondominant
    · exact Or.inl hzero
    · exact Or.inr hwindow
    · rw [positiveInterfacePairNonDominantObstructionUnionAtRank_eq_empty]
        at hnondominant
      exact hnondominant.elim

/-- The complete profiled unbalanced exact-pair remainder is summable at
each old-favorite rank. -/
theorem
    simpleRandomWalk_positiveInterfaceProfiledUnbalancedPairRemainderUnionAtRank_series_ne_top
    (t : DominoTiling) (rank : ℕ) :
    ∑' m, simpleRandomWalk
        (positiveInterfaceProfiledUnbalancedPairRemainderUnionAtRank
          concreteFullBetaProductData t rank m) ≠ ∞ := by
  have habsorb :=
    HLOZGapBetaNumerics.eventually_nat_mul_exp_neg_two_log_sq_le_exp_neg
      2 (c := 1 / 4000) (by norm_num)
  have hbound : ∀ᶠ m : ℕ in atTop,
      simpleRandomWalk
          (positiveInterfaceProfiledUnbalancedPairRemainderUnionAtRank
            concreteFullBetaProductData t rank m) ≤
        ENNReal.ofReal
          (Real.exp (-(1 / 4000 : ℝ) * Real.log (m : ℝ) ^ 2)) := by
    filter_upwards
        [concreteFullBetaProductData.threshold_pos,
          eventually_ge_atTop (2 : ℕ), eventually_four_le_shellWidth48,
          eventually_simpleRandomWalk_positiveInterfaceZeroPrefixPaymentUnionAtRank_le_exp
            concreteFullBetaProductData t rank,
          eventually_simpleRandomWalk_positiveInterfacePairPositiveWindowObstructionUnionAtRank_le_exp
            t rank,
          habsorb]
        with m hthreshold hm hwidth hzero hwindow habsorbM
    have hwindowSlow :
        ENNReal.ofReal
            (Real.exp (-(1 / 2 : ℝ) * Real.log (m : ℝ) ^ 2)) ≤
          ENNReal.ofReal
            (Real.exp (-(1 / 2000 : ℝ) * Real.log (m : ℝ) ^ 2)) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (Real.log (m : ℝ))]
    calc
      simpleRandomWalk
          (positiveInterfaceProfiledUnbalancedPairRemainderUnionAtRank
            concreteFullBetaProductData t rank m) ≤
        simpleRandomWalk
            (positiveInterfaceZeroPrefixPaymentUnionAtRank
              concreteFullBetaProductData t rank m) +
          simpleRandomWalk
            (positiveInterfacePairPositiveWindowObstructionUnionAtRank
              concreteFullBetaProductData t rank m) :=
        (measure_mono
          (positiveInterfaceProfiledUnbalancedPairRemainderUnionAtRank_subset_zero_union_positiveWindow
            concreteFullBetaProductData t rank m (by omega) hthreshold
              hwidth)).trans (measure_union_le _ _)
      _ ≤ ENNReal.ofReal
              (Real.exp (-(1 / 2000 : ℝ) * Real.log (m : ℝ) ^ 2)) +
            ENNReal.ofReal
              (Real.exp (-(1 / 2000 : ℝ) * Real.log (m : ℝ) ^ 2)) :=
        add_le_add hzero (hwindow.trans hwindowSlow)
      _ = (2 : ℝ≥0∞) * ENNReal.ofReal
            (Real.exp (-(2 * (1 / 4000 : ℝ)) *
              Real.log (m : ℝ) ^ 2)) := by
        congr 1
        ring
      _ ≤ ENNReal.ofReal
            (Real.exp (-(1 / 4000 : ℝ) * Real.log (m : ℝ) ^ 2)) :=
        habsorbM
  exact measure_series_ne_top_of_eventually_exp_neg_log_sq_bound
    simpleRandomWalk _ (by norm_num : (0 : ℝ) < 1 / 4000) hbound

end

end Erdos1165.HLOZPositiveInterfacePairWindowObstructionBand
