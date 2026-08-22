/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPrefixedAllCreationCanonicalRefinement
import ErdosProblems.Erdos1165.TilingOrientedShellSupportSelector
import ErdosProblems.Erdos1165.TilingPrefixedFavoriteTraceSupport

/-!
# Prefix-correct geometry for the canonical Proposition 4.9 source

The low candidate family is the fixed first-strip support
`V₂(I₁)` at the old creation clock.  On every exact supported atom this file
constructs, without a probability premise, the literal away coordinate of a
chosen candidate and identifies its fixed dominant endpoint.  The terminal
used in the reconstructed broad/narrow windows is independent of the logical
coordinate cap.
-/

open Set

namespace Erdos1165.HLOZPrefixedCanonicalSourceLowRecovery

open FiniteDominoProductLaw
open HLOZPathEvents HLOZPrefixedAllCreationCanonicalRefinement
open HLOZPrefixedTilingConditionalCoordinateReconstruction
open HLOZProposition48Candidates HLOZShellZeroReplacementWindows
open HLOZThetaSourceBalance
open LazyDecomposition PathInsertion PreStoppingFiber SpatialInsertionFiber
open StoppedInsertion VariableStoppedFiber
open PreStoppingSpatialLaw
open TilingCappedMarginalization TilingConditionalCappedMarginalization
open TilingInsertedLocalTime
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedPrefixedSupportBridge
open TilingOrientedShellSupportSelector
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedFavoriteTraceSupport
open TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingLazyDecomposition
open TilingShellZeroAllCreationTraceBridge
open TilingSpatialInsertionFiber VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

abbrev SourceSupportAt (t : DominoTiling) (o : Orientation) (m : ℕ) :=
  orientedShellZeroSourceSupportAt t o m

abbrev SourceSupportedIndex (t : DominoTiling) (o : Orientation)
    (m k : ℕ) :=
  OrientedAllCreationSupportedAtomIndex t o m k (SourceSupportAt t o m)

abbrev SourceSupportData (t : DominoTiling) (o : Orientation)
    (m k : ℕ) :=
  orientedShellZeroSourceSupportSelectorData t o m k

abbrev SourceFiber {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k) :=
  (orientedAllCreationConcreteFamily t o m k (SourceSupportAt t o m)
    (SourceSupportData t o m k)).fiber eta

/-- The physical endpoint after the retained insertion suffix.  Its value is
independent of the displayed insertion totals, so zero totals give a
canonical cap-independent representative. -/
def sourceTerminal {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k) : Option Point :=
  prefixedTilingInsertionTerminal eta.1.1.external.initial t
    eta.1.1.external.start eta.1.1.external.retained (fun _ ↦ 0)
    eta.1.1.external.tail

theorem sourceTerminal_eq_coordinates
    {t : DominoTiling} {o : Orientation} {m k cap : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount cap) :
    prefixedTilingInsertionTerminal eta.1.1.external.initial t
        eta.1.1.external.start eta.1.1.external.retained
        (fun j ↦ (q j : ℕ)) eta.1.1.external.tail =
      sourceTerminal eta := by
  apply prefixedTilingInsertionTerminal_eq_of_coordinates
  rfl

/-- The represented away coordinate corresponding to a literal source
candidate in the exact atom. -/
def sourceChosen
    {t : DominoTiling} {o : Orientation} {m k : ℕ} (cap : ℕ)
    (eta : SourceSupportedIndex t o m k) (candidate : Point)
    (hcandidate : candidate ∈ eta.1.2) :
    TilingAwayDomino t ((SourceFiber eta).start cap)
      ((SourceFiber eta).retained cap) ((SourceFiber eta).distinguished cap) :=
  supportAwayChosen t eta.1.1.external.start eta.1.1.external.retained
    eta.1.2 (SourceFiber eta).support_represented candidate hcandidate

@[simp] theorem sourceChosen_base
    {t : DominoTiling} {o : Orientation} {m k : ℕ} (cap : ℕ)
    (eta : SourceSupportedIndex t o m k) (candidate : Point)
    (hcandidate : candidate ∈ eta.1.2) :
    (sourceChosen cap eta candidate hcandidate).1.1 = candidate := rfl

private theorem canonical_start
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k) :
    trajectory
        (extendPrefix (directionVectorOfList eta.1.1.external.initial.1))
        eta.1.1.external.initial.1.length =
      eta.1.1.external.start := rfl

/-- On an exact oriented source atom the selected `V₂(I₁)` candidate is
base-dominant already in the fixed physical prefix.  Adding a common lazy
total to both endpoints cannot alter that choice. -/
theorem sourceChosen_fixedDominant
    {t : DominoTiling} {o : Orientation} {m k : ℕ} (cap : ℕ)
    (eta : SourceSupportedIndex t o m k) (candidate : Point)
    (hcandidate : candidate ∈ eta.1.2) :
    prefixedTilingFixedDominantEndpoint
        ((SourceFiber eta).initial cap) ((SourceFiber eta).start cap)
        ((SourceFiber eta).retained cap) (sourceTerminal eta)
        (sourceChosen cap eta candidate hcandidate).1 = candidate := by
  classical
  rcases eta.2 with ⟨s, hs⟩
  let n := creationTimeNat m k s
  obtain ⟨q, hq⟩ :=
    exists_prefixedTilingInsertionPrefixList_eq_incrementPrefixList
      t o n s eta.1.1.external
        (congrArg OrientedAllCreationTraceCode.external hs.1.2.2)
  let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
    eta.1.1.external.start eta.1.1.external.retained q
    eta.1.1.external.tail.1
  have hvlen : v.length = n := by
    rw [show v = incrementPrefixList n (stepsOfWalk s) from hq]
    simp [incrementPrefixList]
  have hvalid : s ∈ validStepWalk := hs.1.1
  have hcanonical : pathPrefix
      (trajectory (extendPrefix (directionVectorOfList v))) n =
        pathPrefix s n := by
    exact pathPrefix_canonical_eq_of_prefixedInsertionPrefix_eq s
      eta.1.1.external.initial.1 eta.1.1.external.start
      eta.1.1.external.retained q eta.1.1.external.tail.1 hvalid hq
  have hsupport : orientedTilingVTwoBases t o
      (shellZeroSourceTotalWindow m (shellWidth48 m)) s n = eta.1.2 := by
    change SourceSupportAt t o m s n = eta.1.2
    exact hs.2
  have hcandVTwo : candidate ∈ orientedTilingVTwoBases t o
      (shellZeroSourceTotalWindow m (shellWidth48 m)) s n := by
    rw [hsupport]
    exact hcandidate
  have hcandBase :=
    ((mem_orientedTilingVTwoBases_iff t o _ s n candidate).mp
      hcandVTwo).1
  have hcandData := Finset.mem_filter.mp hcandBase
  have hdominant : localTime s n (tilingPartner t candidate) ≤
      localTime s n candidate := hcandData.2.1
  let terminal := prefixedTilingInsertionTerminal eta.1.1.external.initial t
    eta.1.1.external.start eta.1.1.external.retained q
    eta.1.1.external.tail
  let b : TilingExternalDomino t eta.1.1.external.start
      eta.1.1.external.retained :=
    (sourceChosen cap eta candidate hcandidate).1
  have hbbase : b.1 = candidate := by
    exact sourceChosen_base cap eta candidate hcandidate
  have hpath : finitePathList (pathPrefix s n) =
      prefixedTilingPrefixPointPath eta.1.1.external.initial.1
        eta.1.1.external.start
        (tilingInsertGapVector t eta.1.1.external.start
          eta.1.1.external.retained q) terminal := by
    rw [← hcanonical, ← hvlen]
    exact finitePathList_prefixedTilingInsertionPrefix
      eta.1.1.external.initial t eta.1.1.external.start
      eta.1.1.external.retained q eta.1.1.external.tail (canonical_start eta)
  have hbaseLocal :
      localTime s n candidate =
        prefixedTilingFixedBoundaryLocalTime
            eta.1.1.external.initial.1 eta.1.1.external.start
            eta.1.1.external.retained terminal candidate +
          tilingDominoTotal t eta.1.1.external.start
            eta.1.1.external.retained q b := by
    rw [localTime_eq_listLocalTime, hpath,
      prefixedTilingInsertedPrefix_localTime_at_dominoPoint
        eta.1.1.external.initial.1 t eta.1.1.external.start
        eta.1.1.external.retained q terminal b candidate]
    rw [← hbbase]
    exact tilingExternalDomino_isBase t eta.1.1.external.start
      eta.1.1.external.retained b
  have hpartnerLocal :
      localTime s n (tilingPartner t candidate) =
        prefixedTilingFixedBoundaryLocalTime
            eta.1.1.external.initial.1 eta.1.1.external.start
            eta.1.1.external.retained terminal (tilingPartner t candidate) +
          tilingDominoTotal t eta.1.1.external.start
            eta.1.1.external.retained q b := by
    rw [localTime_eq_listLocalTime, hpath,
      prefixedTilingInsertedPrefix_localTime_at_dominoPoint
        eta.1.1.external.initial.1 t eta.1.1.external.start
        eta.1.1.external.retained q terminal b
          (tilingPartner t candidate)]
    rw [← hbbase]
    exact tilingPartner_ofExternalDomino_has_base t
      eta.1.1.external.start eta.1.1.external.retained b
  have hfixed : prefixedTilingFixedBoundaryLocalTime
        eta.1.1.external.initial.1 eta.1.1.external.start
        eta.1.1.external.retained terminal (tilingPartner t candidate) ≤
      prefixedTilingFixedBoundaryLocalTime
        eta.1.1.external.initial.1 eta.1.1.external.start
        eta.1.1.external.retained terminal candidate := by
    rw [hbaseLocal, hpartnerLocal] at hdominant
    omega
  have hterminal : terminal = sourceTerminal eta := by
    apply prefixedTilingInsertionTerminal_eq_of_coordinates
    exact canonical_start eta
  change prefixedTilingFixedDominantEndpoint
      eta.1.1.external.initial.1 eta.1.1.external.start
      eta.1.1.external.retained (sourceTerminal eta) b = candidate
  unfold prefixedTilingFixedDominantEndpoint
  rw [← hterminal, if_pos (by simpa only [hbbase] using hfixed), hbbase]

/-- Prefix-correct canonical parameters before the consumer supplies the
source `D_η`/Theta thresholds and the mesh narrow window. -/
noncomputable def sourceParameters
    {t : DominoTiling} {o : Orientation} {m k cap : ℕ}
    (eta : SourceSupportedIndex t o m k) (candidate : Point)
    (hcandidate : candidate ∈ eta.1.2)
    (low externalLow externalHigh : ℕ) (narrowWindow : Finset ℕ) :
    Parameters (SourceFiber eta) cap candidate where
  terminal := sourceTerminal eta
  low := low
  externalLow := externalLow
  externalHigh := externalHigh
  broadWindow := shellZeroSourceTotalWindow m (shellWidth48 m)
  chosen := sourceChosen cap eta candidate hcandidate
  candidate_eq := sourceChosen_fixedDominant cap eta candidate hcandidate
  narrowWindow := narrowWindow

end

end Erdos1165.HLOZPrefixedCanonicalSourceLowRecovery
