/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingShellZeroActualDeltaReplacementAtomRecovery
import ErdosProblems.Erdos1165.TilingShellZeroSourceScreenForward

/-!
# Exact factorization of one honest actual-delta replacement clock

The replacement predicate is the literal common source selector conjoined
with one fixed-delta away screen.  Its reverse factorization is nontrivial:
the selected source reconstruction supplies the old creation clock, and the
fixed-delta screen deterministically reconstructs acceptance at rank
`k + delta`.
-/

namespace Erdos1165.TilingShellZeroDeltaReplacementFactorization

open FiniteDominoProductLaw HLOZPathEvents HLOZProposition48Candidates
open HLOZShellZeroCentralCount HLOZShellZeroExternalWindow
open HLOZShellZeroReplacementWindows LazyDecomposition
open PathInsertion PreStoppingFiber SpatialInsertionFiber StoppedInsertion
open TilingCappedMarginalization TilingConditionalCappedMarginalization
open TilingLazyDecomposition TilingOrientedShellZeroSourcePartition
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedFavoriteTraceSupport TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingShellZeroActualDeltaPartition
open TilingShellZeroActualDeltaReplacementAtomRecovery
open TilingShellZeroEndpointIncrementScreen
open TilingShellZeroDeltaAcceptedCreationEndpoint
open TilingShellZeroExternalStaticSupportData
open TilingShellZeroExternalStaticSupportPartition
open TilingShellZeroFactoredCapScreen
open TilingShellZeroSourcePartition TilingShellZeroSourceScreenForward
open TilingShellZeroSupportedSourceStaticFacts
open TilingSpatialInsertionFiber VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The terminal boundary is coordinate-independent; this zero-coordinate
representative makes the fixed-delta screen a function of the carrier only. -/
def staticTerminal {t : DominoTiling}
    (z : OrientedTilingTypedExternalWordCode t) : Option Point :=
  prefixedTilingInsertionTerminal z.initial t z.start z.retained
    (fun _ ↦ 0) z.tail

def replacementStoppingTime {t : DominoTiling}
    (z : OrientedTilingTypedExternalWordCode t)
    (m k cap : ℕ) {total central : ℕ}
    (delta : ReplacementEndpointIncrement total central) : StepPath → ℕ :=
  truncatedLevelTime m (k + (delta : ℕ))
    (externalCoordinateCutoff z (coordinateCap z m cap))

def replacementScreen
    {t : DominoTiling} {o : Orientation}
    {m k low externalLow externalHigh total : ℕ}
    (eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m) low
      externalLow externalHigh total)
    (cap central : ℕ) (delta : ReplacementEndpointIncrement total central)
    (ell : TruncatedTotals (upper eta.1.1 eta.1.2 m)) : Prop :=
  prefixedShellZeroReplacementScreenAtIncrement
    (cap := coordinateCap eta.1.1 m cap) (m := m) (w := shellWidth48 m)
    eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
    (staticTerminal eta.1.1) (staticD eta.1.1 eta.1.2)
    (upper eta.1.1 eta.1.2 m) central delta ell

/-- The literal fixed-delta predicate.  Acceptance is deliberately not
built into this definition; it is derived below from the source selector and
the replacement screen. -/
def replacementPredicate
    {t : DominoTiling} {o : Orientation}
    {m k low externalLow externalHigh total : ℕ}
    (eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m) low
      externalLow externalHigh total)
    (cap central : ℕ) (delta : ReplacementEndpointIncrement total central)
    (q : TilingCappedCoordinates eta.1.1.retainedCount
      (coordinateCap eta.1.1 m cap)) : Prop :=
  selected t o m k low externalLow externalHigh total cap eta.1.1 eta.1.2
      ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
        (staticD eta.1.1 eta.1.2) q).1) ∧
    TilingAwayTotalsScreen t eta.1.1.start eta.1.1.retained
      (staticD eta.1.1 eta.1.2) (upper eta.1.1 eta.1.2 m)
      (replacementScreen eta cap central delta)
      ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
        (staticD eta.1.1 eta.1.2) q).2)

private theorem replacement_prefix_pos
    {t : DominoTiling} {o : Orientation}
    {m k low externalLow externalHigh total cap central : ℕ}
    (eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m) low
      externalLow externalHigh total)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternal : ShellZeroExternalWindowArithmeticAt m externalLow externalHigh)
    (hcentral : central < total)
    (delta : ReplacementEndpointIncrement total central)
    (q : TilingCappedCoordinates eta.1.1.retainedCount
      (coordinateCap eta.1.1 m cap))
    (ell : TruncatedTotals (upper eta.1.1 eta.1.2 m))
    (hscreen : replacementScreen eta cap central delta ell)
    (htotal : ∀ b,
      tilingDominoTotal t eta.1.1.start eta.1.1.retained
        (fun j ↦ (q j : ℕ)) b.1 = (ell b : ℕ)) :
    0 < (prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
      eta.1.1.start eta.1.1.retained (fun j ↦ (q j : ℕ))
        eta.1.1.tail.1).length := by
  classical
  rcases hscreen.1 with ⟨A, hA, hclass⟩
  have hAcard : A.card = central := (Finset.mem_powersetCard.mp hA).2
  have hm : 1 < m := by
    rcases harithmetic with ⟨hw, hwm, _⟩
    omega
  have hexists : ∃ b : TilingAwayDomino t eta.1.1.start eta.1.1.retained
      (staticD eta.1.1 eta.1.2), b ∉ A := by
    by_contra hn
    push_neg at hn
    let hrepresented := sourceStaticSupport_subset_externalDominoBases eta
    let e := supportAwayEquiv t eta.1.1.start eta.1.1.retained eta.1.2
      hrepresented
    let f : {y : Point // y ∈ eta.1.2} →
        TilingAwayDomino t eta.1.1.start eta.1.1.retained
          (staticD eta.1.1 eta.1.2) := fun y ↦ e.symm y
    have hf : Function.Injective f := by
      simpa only [f, staticD] using e.symm.injective
    let B := (Finset.univ : Finset {y : Point // y ∈ eta.1.2}).image f
    have hBA : B ⊆ A := by
      intro b hb
      rcases Finset.mem_image.mp hb with ⟨y, _hy, rfl⟩
      exact hn _
    have hBcard : B.card = total := by
      dsimp only [B]
      rw [Finset.card_image_of_injective _ hf, Finset.card_univ,
        Fintype.card_coe, card_staticSupport eta]
    have hle := Finset.card_le_card hBA
    rw [hBcard, hAcard] at hle
    omega
  rcases hexists with ⟨b, hb⟩
  have hrep := (hclass b).2 hb
  have hvpos : 0 < (ell b : ℕ) := by
    have htranslate :=
      ((coordinateSupportData t o m k (shellWidth48 m) low externalLow
        externalHigh total cap eta hm).toWindowData hexternal).translate b
    simp only [tilingShellZeroReplacementCoordinate,
      mem_shellZeroReplacementFailureWindow] at hrep
    omega
  have hdominoPos : 0 < tilingDominoTotal t eta.1.1.start
      eta.1.1.retained (fun j ↦ (q j : ℕ)) b.1 := by
    rw [htotal b]
    exact hvpos
  change 0 < (prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
    (trajectory (extendPrefix (directionVectorOfList eta.1.1.initial.1))
      eta.1.1.initial.1.length) eta.1.1.retained
      (fun j ↦ (q j : ℕ)) eta.1.1.tail.1).length
  rw [prefixedTilingInsertionPrefixList_length]
  by_contra hn
  have hsum : ∑ j, (q j : ℕ) = 0 := by omega
  have hqzero : ∀ j, (q j : ℕ) = 0 := by
    intro j
    have hle : (q j : ℕ) ≤ ∑ c, (q c : ℕ) :=
      Finset.single_le_sum (f := fun c ↦ (q c : ℕ))
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    omega
  have hzero : tilingDominoTotal t eta.1.1.start eta.1.1.retained
      (fun j ↦ (q j : ℕ)) b.1 = 0 := by
    unfold tilingDominoTotal
    simp only [hqzero, Finset.sum_const_zero]
  omega

/-- The fixed-delta screen and common source selector force acceptance at
the honest replacement rank. -/
theorem replacement_accepted
    {t : DominoTiling} {o : Orientation}
    {m k low externalLow externalHigh total cap central : ℕ}
    (eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m) low
      externalLow externalHigh total)
    (hm : 1 < m) (hk : 0 < k) (hlow : low < m)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternal : ShellZeroExternalWindowArithmeticAt m externalLow externalHigh)
    (hcentral : central < total)
    (delta : ReplacementEndpointIncrement total central)
    (qReplacement : TilingCappedCoordinates eta.1.1.retainedCount
      (coordinateCap eta.1.1 m cap))
    (hq : replacementPredicate eta cap central delta qReplacement) :
    PrefixedTilingStoppingAccepted
      (replacementStoppingTime eta.1.1 m k cap delta)
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
      (fun j ↦ (qReplacement j : ℕ)) eta.1.1.tail.1 := by
  classical
  rcases hq.1 with ⟨aSource, hsource⟩
  let qSource := (splitTilingCoordinatesEquiv t eta.1.1.start
    eta.1.1.retained (staticD eta.1.1 eta.1.2)).symm
      ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
        (staticD eta.1.1 eta.1.2) qReplacement).1, aSource)
  have hsourceForward := source_forward eta hm hk hexternal qSource hsource
  rcases hsourceForward.2 with ⟨ellSource, hellSource, htotalSourceAway⟩
  rcases hq.2 with ⟨ellReplacement, hellReplacement,
    htotalReplacementAway⟩
  have hdist : (splitTilingCoordinatesEquiv t eta.1.1.start
      eta.1.1.retained (staticD eta.1.1 eta.1.2) qSource).1 =
    (splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
      (staticD eta.1.1 eta.1.2) qReplacement).1 := by
    simp only [qSource, Equiv.apply_symm_apply]
  have hterminal : prefixedTilingInsertionTerminal eta.1.1.initial t
      eta.1.1.start eta.1.1.retained (fun j ↦ (qSource j : ℕ))
        eta.1.1.tail = staticTerminal eta.1.1 := by
    apply prefixedTilingInsertionTerminal_eq_of_coordinates
      eta.1.1.initial t eta.1.1.start eta.1.1.retained
      (fun j ↦ (qSource j : ℕ)) (fun _ ↦ 0) eta.1.1.tail rfl
  have hbase : ∀ b : TilingAwayDomino t eta.1.1.start eta.1.1.retained
      (staticD eta.1.1 eta.1.2),
    prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
        eta.1.1.retained
        (prefixedTilingInsertionTerminal eta.1.1.initial t eta.1.1.start
          eta.1.1.retained (fun j ↦ (qSource j : ℕ)) eta.1.1.tail) b.1.1 =
      Fintype.card (TilingCoordinatesAt t eta.1.1.start
        eta.1.1.retained b.1) := by
    intro b
    exact boundaryLocalTime_eq_coordinateCard eta hm hk
      (fun j ↦ (qSource j : ℕ)) b.1
      ((away_mem_support_iff t eta.1.1.start eta.1.1.retained
        eta.1.2 b.1).1 b.2)
  have hsourceCoordinate : ∀ b,
      tilingShellZeroSourceCoordinate
        (cap := coordinateCap eta.1.1 m cap) (m := m)
        (w := shellWidth48 m) t eta.1.1.start eta.1.1.retained
        (staticD eta.1.1 eta.1.2) (upper eta.1.1 eta.1.2 m)
        b (ellSource b) := by
    intro b
    exact hellSource b
  have htotalSource : ∀ b,
      tilingDominoTotal t eta.1.1.start eta.1.1.retained
        (fun j ↦ (qSource j : ℕ)) b.1 = (ellSource b : ℕ) := by
    intro b
    calc
      _ = tilingAwayTotal t eta.1.1.start eta.1.1.retained
          (staticD eta.1.1 eta.1.2)
          ((splitTilingCoordinatesEquiv t eta.1.1.start
            eta.1.1.retained (staticD eta.1.1 eta.1.2) qSource).2) b :=
        (tilingAwayTotal_split_eq_dominoTotal t eta.1.1.start
          eta.1.1.retained (staticD eta.1.1 eta.1.2) qSource b).symm
      _ = _ := htotalSourceAway b
  have htotalReplacement : ∀ b,
      tilingDominoTotal t eta.1.1.start eta.1.1.retained
        (fun j ↦ (qReplacement j : ℕ)) b.1 = (ellReplacement b : ℕ) := by
    intro b
    calc
      _ = tilingAwayTotal t eta.1.1.start eta.1.1.retained
          (staticD eta.1.1 eta.1.2)
          ((splitTilingCoordinatesEquiv t eta.1.1.start
            eta.1.1.retained (staticD eta.1.1 eta.1.2) qReplacement).2) b :=
        (tilingAwayTotal_split_eq_dominoTotal t eta.1.1.start
          eta.1.1.retained (staticD eta.1.1 eta.1.2) qReplacement b).symm
      _ = _ := htotalReplacementAway b
  have hsourcePos : 0 < (prefixedTilingInsertionPrefixList
      eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
      (fun j ↦ (qSource j : ℕ)) eta.1.1.tail.1).length := by
    rw [← source_creation_time_eq eta.1.1 qSource hsource.2]
    exact creationTimeNat_pos_of_mem_sourceStaticSupportAtom hm hsource.1
  have hreplacementPos := replacement_prefix_pos eta harithmetic hexternal hcentral
    delta qReplacement ellReplacement hellReplacement htotalReplacement
  have hsourceD :
      let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
        eta.1.1.start eta.1.1.retained (fun j ↦ (qSource j : ℕ))
          eta.1.1.tail.1
      let s := trajectory (extendPrefix (directionVectorOfList v))
      tilingDEtaAt t m k (shellWidth48 m) low s v.length := by
    have hevent := hsource.1.1.1.1
    have hD := hevent.2.1
    have htime := source_creation_time_eq eta.1.1 qSource hsource.2
    rw [htime] at hD
    exact hD
  have hsourceVTwo :
      let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
        eta.1.1.start eta.1.1.retained (fun j ↦ (qSource j : ℕ))
          eta.1.1.tail.1
      let s := trajectory (extendPrefix (directionVectorOfList v))
      ∀ b ∈ eta.1.2,
        tilingVTwoAt t (shellZeroSourceTotalWindow m (shellWidth48 m))
          s v.length b := by
    dsimp only
    intro b hb
    have hsupp := hsource.1.2
    change sourceStaticSupport t o m k (shellWidth48 m)
      (canonicalPath eta.1.1 (fun j ↦ (qSource j : ℕ))) = eta.1.2 at hsupp
    have htime := source_creation_time_eq eta.1.1 qSource hsource.2
    rw [sourceStaticSupport, htime] at hsupp
    have horiented : b ∈ orientedTilingVTwoBases t o
        (shellZeroSourceTotalWindow m (shellWidth48 m))
        (canonicalPath eta.1.1 (fun j ↦ (qSource j : ℕ)))
        (prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
          eta.1.1.start eta.1.1.retained (fun j ↦ (qSource j : ℕ))
            eta.1.1.tail.1).length := by rw [hsupp]; exact hb
    exact (Finset.mem_filter.mp
      ((mem_orientedTilingVTwoBases_iff t o _ _ _ b).mp horiented).1).2
  have hterminalVOne :
      let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
        eta.1.1.start eta.1.1.retained (fun j ↦ (qSource j : ℕ))
          eta.1.1.tail.1
      let s := trajectory (extendPrefix (directionVectorOfList v))
      tilingVOneAt t m s v.length (tilingBase t (s v.length)) :=
    TilingShellZeroDEtaTerminal.tilingVOneAt_terminalBase_of_tilingDEtaAt
      hlow hsourceD
  apply prefixedTilingStoppingAccepted_at_actualEndpointIncrement_staticSupport
    eta.1.1.initial t eta.1.1.start eta.1.1.retained eta.1.1.tail eta.1.2
    (upper eta.1.1 eta.1.2 m) k delta
    (externalCoordinateCutoff eta.1.1 (coordinateCap eta.1.1 m cap)) central
    (by omega) hk qSource qReplacement ellSource ellReplacement rfl hdist
    (by simpa only [staticD, supportComplementDistinguished] using hbase)
    (by simpa only [staticD, supportComplementDistinguished] using
      boundary_dominance_of_source eta hm hk qSource hsource.1 hsource.2)
    (by simpa only [staticD, supportComplementDistinguished] using
      hsourceCoordinate)
    (by simpa only [replacementScreen, staticD,
      supportComplementDistinguished, hterminal] using hellReplacement)
    (by simpa only [staticD, supportComplementDistinguished] using htotalSource)
    (by simpa only [staticD, supportComplementDistinguished] using
      htotalReplacement)
    hsourceVTwo hterminalVOne
    hsourcePos hreplacementPos
    (insertion_lt_cutoff eta.1.1 m cap qSource)
    (insertion_lt_cutoff eta.1.1 m cap qReplacement) hsource.2

/-- Exact factorization of the fixed-delta replacement predicate. -/
theorem replacement_factorization
    {t : DominoTiling} {o : Orientation}
    {m k low externalLow externalHigh total cap central : ℕ}
    (eta : SupportedSourceStaticSupportIndex t o m k (shellWidth48 m) low
      externalLow externalHigh total)
    (hm : 1 < m) (hk : 0 < k) (hlow : low < m)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternal : ShellZeroExternalWindowArithmeticAt m externalLow externalHigh)
    (hcentral : central < total)
    (delta : ReplacementEndpointIncrement total central)
    (q : TilingCappedCoordinates eta.1.1.retainedCount
      (coordinateCap eta.1.1 m cap)) :
    replacementPredicate eta cap central delta q ∧
        PrefixedTilingStoppingAccepted
          (replacementStoppingTime eta.1.1 m k cap delta)
          eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
            (fun j ↦ (q j : ℕ)) eta.1.1.tail.1 ↔
      selected t o m k low externalLow externalHigh total cap
          eta.1.1 eta.1.2
          ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
            (staticD eta.1.1 eta.1.2) q).1) ∧
        TilingAwayTotalsScreen t eta.1.1.start eta.1.1.retained
          (staticD eta.1.1 eta.1.2) (upper eta.1.1 eta.1.2 m)
          (replacementScreen eta cap central delta)
          ((splitTilingCoordinatesEquiv t eta.1.1.start eta.1.1.retained
            (staticD eta.1.1 eta.1.2) q).2) := by
  constructor
  · exact fun h ↦ h.1
  · intro h
    exact ⟨h, replacement_accepted eta hm hk hlow harithmetic hexternal
      hcentral delta q h⟩

end

end Erdos1165.TilingShellZeroDeltaReplacementFactorization
