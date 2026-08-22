/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCheckerOriginSafeProp49PathCoverage
import ErdosProblems.Erdos1165.HLOZPrefixedAllCreationDistinguishedRestriction

/-!
# Checker origin safety on the distinguished carrier

When the shifted physical-origin domino is not an exposed source coordinate,
its insertion coordinates belong to the distinguished carrier.  Conditioning
that carrier on origin safety leaves the normalized away-coordinate
Proposition 4.9 ratio unchanged.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZCheckerOriginSafeDistinguishedProp49Family

open FiniteDominoProductLaw
open HLOZCheckerOriginSafeProp49Family
open HLOZCheckerOriginSafeProp49PathCoverage
open HLOZCheckerPrefixedCylinderTransport
open HLOZFilteredOrientedAllCreationStoppedCandidateFamily
open HLOZPathEvents HLOZStoppedHistoryCandidateFuture
open HLOZMeshCandidatePolynomialNumerics
open HLOZOrientedAllCreationStoppedCandidateFamily
open HLOZPrefixedAllCreationCanonicalRefinement
open HLOZPrefixedAllCreationDistinguishedRestriction
open HLOZPrefixedCanonicalSourceAtomRecovery
open HLOZPrefixedCanonicalSourceLowRecovery
open HLOZPrefixedCanonicalSourceProp49Data
open HLOZPrefixedCanonicalSourceProp49PathCoverage
open HLOZPrefixedCanonicalSourceProp49Refinement
open HLOZPrefixedProp49CandidateWindowRatio HLOZProposition48Candidates
open HLOZShellZeroExternalWindow HLOZShellZeroReplacementWindows
open HLOZTypedStoppedCandidateObservability
open HLOZTypedStoppedCandidateConditionalProduct
open LazyDecomposition PreStoppingFiber PreStoppingSpatialLaw
open SpatialInsertionFiber StoppedInsertion TilingCappedMarginalization
open TilingDistinguishedTraceInvariant TilingInsertedLocalTime
open TilingLazyDecomposition
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedFavoriteTraceSupport
open TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Origin safety evaluated on the canonical insertion word for one capped
coordinate vector. -/
def canonicalTargetOriginSafe
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k) (e : Direction) (cap : ℕ)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      ((SourceFiber eta).coordinateCap cap)) : Prop :=
  listLocalTime
      (prefixedTilingPrefixPointPath ((SourceFiber eta).initial cap)
        ((SourceFiber eta).start cap)
        (tilingInsertGapVector t ((SourceFiber eta).start cap)
          ((SourceFiber eta).retained cap) (fun j ↦ (q j : ℕ)))
        (sourceTerminal eta))
      (0 - directionVector e) + 1 < m

/-- The induced condition on a distinguished-coordinate assignment.  It is
stated by existence of one completion; outside the source support all
completions have the same shifted-origin local time. -/
def distinguishedTargetOriginSafe
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k) (e : Direction) (cap : ℕ)
    (d : TilingDistinguishedCoordinates
      (cap := (SourceFiber eta).coordinateCap cap) t
      ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
      ((SourceFiber eta).distinguished cap)) : Prop :=
  ∃ q : TilingCappedCoordinates eta.1.1.external.retainedCount
      ((SourceFiber eta).coordinateCap cap),
    (splitTilingCoordinatesEquiv t ((SourceFiber eta).start cap)
      ((SourceFiber eta).retained cap) ((SourceFiber eta).distinguished cap)
      q).1 = d ∧ canonicalTargetOriginSafe eta e cap q

theorem canonicalTargetOriginLocalTime_eq_of_distinguished_eq
    {t : DominoTiling} {o : Orientation} {m k cap : ℕ}
    (eta : SourceSupportedIndex t o m k) (e : Direction)
    (horigin : targetOriginBase t e ∉ eta.1.2)
    (q q' : TilingCappedCoordinates eta.1.1.external.retainedCount
      ((SourceFiber eta).coordinateCap cap))
    (hdist : (splitTilingCoordinatesEquiv t ((SourceFiber eta).start cap)
        ((SourceFiber eta).retained cap) ((SourceFiber eta).distinguished cap)
        q).1 =
      (splitTilingCoordinatesEquiv t ((SourceFiber eta).start cap)
        ((SourceFiber eta).retained cap) ((SourceFiber eta).distinguished cap)
        q').1) :
    listLocalTime
        (prefixedTilingPrefixPointPath ((SourceFiber eta).initial cap)
          ((SourceFiber eta).start cap)
          (tilingInsertGapVector t ((SourceFiber eta).start cap)
            ((SourceFiber eta).retained cap) (fun j ↦ (q j : ℕ)))
          (sourceTerminal eta))
        (0 - directionVector e) =
      listLocalTime
        (prefixedTilingPrefixPointPath ((SourceFiber eta).initial cap)
          ((SourceFiber eta).start cap)
          (tilingInsertGapVector t ((SourceFiber eta).start cap)
            ((SourceFiber eta).retained cap) (fun j ↦ (q' j : ℕ)))
          (sourceTerminal eta))
        (0 - directionVector e) := by
  classical
  by_cases hrepresented : targetOriginBase t e ∈
      tilingExternalDominoBases t ((SourceFiber eta).start cap)
        ((SourceFiber eta).retained cap)
  · apply prefixedTilingPrefixLocalTime_eq_of_distinguished_eq
      ((SourceFiber eta).initial cap) t ((SourceFiber eta).start cap)
      ((SourceFiber eta).retained cap) (sourceTerminal eta)
      ((SourceFiber eta).distinguished cap) q q' hdist
    change targetOriginBase t e ∈
      supportComplementDistinguished t ((SourceFiber eta).start cap)
        ((SourceFiber eta).retained cap) eta.1.2
    exact Finset.mem_sdiff.mpr ⟨hrepresented, horigin⟩
  · rw [prefixedTilingInsertedPrefix_localTime_of_base_not_mem
        ((SourceFiber eta).initial cap) t ((SourceFiber eta).start cap)
        ((SourceFiber eta).retained cap) (fun j ↦ (q j : ℕ))
        (sourceTerminal eta) (0 - directionVector e),
      prefixedTilingInsertedPrefix_localTime_of_base_not_mem
        ((SourceFiber eta).initial cap) t ((SourceFiber eta).start cap)
        ((SourceFiber eta).retained cap) (fun j ↦ (q' j : ℕ))
        (sourceTerminal eta) (0 - directionVector e)]
    · simpa only [targetOriginBase] using hrepresented
    · simpa only [targetOriginBase] using hrepresented

theorem canonicalTargetOriginSafe_of_distinguishedTargetOriginSafe
    {t : DominoTiling} {o : Orientation} {m k cap : ℕ}
    (eta : SourceSupportedIndex t o m k) (e : Direction)
    (horigin : targetOriginBase t e ∉ eta.1.2)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      ((SourceFiber eta).coordinateCap cap))
    (hsafe : distinguishedTargetOriginSafe eta e cap
      ((splitTilingCoordinatesEquiv t ((SourceFiber eta).start cap)
        ((SourceFiber eta).retained cap) ((SourceFiber eta).distinguished cap)
        q).1)) :
    canonicalTargetOriginSafe eta e cap q := by
  rcases hsafe with ⟨q', hdist, hsafe'⟩
  unfold canonicalTargetOriginSafe at hsafe' ⊢
  rw [canonicalTargetOriginLocalTime_eq_of_distinguished_eq eta e horigin
    q q' hdist.symm]
  exact hsafe'

theorem distinguishedTargetOriginSafe_of_canonical
    {t : DominoTiling} {o : Orientation} {m k cap : ℕ}
    (eta : SourceSupportedIndex t o m k) (e : Direction)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      ((SourceFiber eta).coordinateCap cap))
    (hsafe : canonicalTargetOriginSafe eta e cap q) :
    distinguishedTargetOriginSafe eta e cap
      ((splitTilingCoordinatesEquiv t ((SourceFiber eta).start cap)
        ((SourceFiber eta).retained cap) ((SourceFiber eta).distinguished cap)
        q).1) :=
  ⟨q, rfl, hsafe⟩

private theorem zero_not_mem_sourceWindow
    {m : ℕ} (_hm : 1 < m) :
    0 ∉ shellZeroSourceTotalWindow m (shellWidth48 m) := by
  simp only [mem_shellZeroSourceTotalWindow]
  omega

/-- The ordinary canonical source refinement on the bare reaching stage.
This is the carrier to which the distinguished origin condition is applied. -/
noncomputable def sourceThresholdRefinement
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    OrientedAllCreationConditionalRefinementData (SourceFiber eta)
      (historyPiece t o m k (SourceSupportAt t o m)
        (thresholdReachStage m k) (some eta))
      (historyPiece t o m k (SourceSupportAt t o m)
          (thresholdReachStage m k) (some eta) ∩
        sourceProp49Near eta a candidate hcandidate low)
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a) := by
  let cert := sourceRecoveryCertificate eta candidate hcandidate low
    (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)
    (prop49NarrowTotalWindow m a) hm hk (zero_not_mem_sourceWindow hm)
  apply cert.refinement
  · intro s hs
    exact ⟨hs.1.2.1, hs⟩
  · intro cap
    exact good.acceptedRatioData a candidate hcandidate low hm hk hwindow
      harithmetic hexternalArithmetic cap
  · exact monotone_sourceProp49ScreenedFiber eta a candidate hcandidate low
  · intro s hs
    exact hs.2.2

private abbrev ordinaryRefinement
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :=
  sourceThresholdRefinement eta a candidate hcandidate low good hm hk hwindow
    harithmetic hexternalArithmetic

/-- Broad predicate with origin safety imposed only on the distinguished
projection. -/
noncomputable def sourceDistinguishedOriginSafeBasePredicate
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (e : Direction) (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (cap : ℕ) :=
  restrictPredicate (SourceFiber eta) (distinguishedTargetOriginSafe eta e)
    (ordinaryRefinement eta a candidate hcandidate low good hm hk hwindow
      harithmetic hexternalArithmetic).basePredicate cap

/-- Narrow predicate with the same distinguished-origin condition. -/
noncomputable def sourceDistinguishedOriginSafeScreenedPredicate
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (e : Direction) (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (cap : ℕ) :=
  restrictPredicate (SourceFiber eta) (distinguishedTargetOriginSafe eta e)
    (ordinaryRefinement eta a candidate hcandidate low good hm hk hwindow
      harithmetic hexternalArithmetic).screenedPredicate cap

def sourceDistinguishedOriginSafeBaseFiber
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (e : Direction) (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (cap : ℕ) : Set WalkPath :=
  walkLift (prefixedTilingPreStoppingFiberEvent
    ((SourceFiber eta).stoppingTime cap) ((SourceFiber eta).initial cap) t
    ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
    ((SourceFiber eta).coordinateCap cap) ((SourceFiber eta).tail cap)
    (sourceDistinguishedOriginSafeBasePredicate eta a candidate hcandidate
      low good e hm hk hwindow harithmetic hexternalArithmetic cap))

def sourceDistinguishedOriginSafeScreenedFiber
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (e : Direction) (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (cap : ℕ) : Set WalkPath :=
  walkLift (prefixedTilingPreStoppingFiberEvent
    ((SourceFiber eta).stoppingTime cap) ((SourceFiber eta).initial cap) t
    ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
    ((SourceFiber eta).coordinateCap cap) ((SourceFiber eta).tail cap)
    (sourceDistinguishedOriginSafeScreenedPredicate eta a candidate hcandidate
      low good e hm hk hwindow harithmetic hexternalArithmetic cap))

def sourceDistinguishedOriginSafeNear
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (e : Direction) (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) : Set WalkPath :=
  ⋃ cap, sourceDistinguishedOriginSafeScreenedFiber eta a candidate
    hcandidate low good e hm hk hwindow harithmetic hexternalArithmetic cap

/-- On an accepted stopped cylinder, the canonical list formulation of
origin safety is exactly the path-space condition at the creation clock. -/
theorem canonicalTargetOriginSafe_iff_of_mem_stopped
    {t : DominoTiling} {o : Orientation} {m k cap : ℕ}
    (eta : SourceSupportedIndex t o m k) (e : Direction)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      ((SourceFiber eta).coordinateCap cap))
    (haccepted : PrefixedTilingStoppingAccepted
      ((SourceFiber eta).stoppingTime cap) ((SourceFiber eta).initial cap) t
      ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
      (fun j ↦ (q j : ℕ)) ((SourceFiber eta).tail cap))
    {s : WalkPath} (hvalid : s ∈ validStepWalk)
    (hword : stepsOfWalk s ∈ prefixedTilingStoppedInsertionAtom
      ((SourceFiber eta).stoppingTime cap) ((SourceFiber eta).initial cap) t
      ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
      (fun j ↦ (q j : ℕ)) ((SourceFiber eta).tail cap)) :
    canonicalTargetOriginSafe eta e cap q ↔ s ∈ targetOriginSafe m k e := by
  let v := prefixedTilingInsertionPrefixList
    ((SourceFiber eta).initial cap) t ((SourceFiber eta).start cap)
    ((SourceFiber eta).retained cap) (fun j ↦ (q j : ℕ))
    ((SourceFiber eta).tail cap)
  let sq := trajectory (extendPrefix (directionVectorOfList v))
  have hp' := pathPrefix_eq_canonical_of_mem_prefixedTilingStoppedInsertionAtom
    ((SourceFiber eta).initial cap) ((SourceFiber eta).start cap)
    ((SourceFiber eta).retained cap) (fun j ↦ (q j : ℕ))
    ((SourceFiber eta).tail cap) (stepsOfWalk s) hword
  have hp : pathPrefix s v.length = pathPrefix sq v.length := by
    change trajectory (stepsOfWalk s) = s at hvalid
    rw [hvalid] at hp'
    simpa only [v, sq] using hp'
  have hlt : v.length < orientedAllCreationCoordinateCutoff eta.1.1
      ((SourceFiber eta).coordinateCap cap) := by
    simpa only [v,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.initial,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.start,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.retained,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.tail] using
      (prefixedInsertion_lt_orientedAllCreationCoordinateCutoff eta.1.1
        ((SourceFiber eta).coordinateCap cap) q)
  have hcreationQ : ThresholdCreation sq m k v.length := by
    change truncatedLevelTime m k
        (orientedAllCreationCoordinateCutoff eta.1.1
          ((SourceFiber eta).coordinateCap cap))
        (extendPrefix (directionVectorOfList v)) = v.length at haccepted
    exact (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m k (orientedAllCreationCoordinateCutoff eta.1.1
        ((SourceFiber eta).coordinateCap cap)) v.length _ hlt).mp haccepted
  have hcreationS : ThresholdCreation s m k v.length :=
    (thresholdCreation_iff_of_pathPrefix_eq hp le_rfl).mpr hcreationQ
  have htime : creationTimeNat m k s = v.length :=
    creationTimeNat_eq_of_creation hcreationS
  have hpath : finitePathList (pathPrefix sq v.length) =
      prefixedTilingPrefixPointPath ((SourceFiber eta).initial cap)
        ((SourceFiber eta).start cap)
        (tilingInsertGapVector t ((SourceFiber eta).start cap)
          ((SourceFiber eta).retained cap) (fun j ↦ (q j : ℕ)))
        (sourceTerminal eta) := by
    rw [← sourceTerminal_eq_coordinates eta q]
    exact finitePathList_prefixedTilingInsertionPrefix
      eta.1.1.external.initial t eta.1.1.external.start
      eta.1.1.external.retained (fun j ↦ (q j : ℕ))
      eta.1.1.external.tail rfl
  change canonicalTargetOriginSafe eta e cap q ↔
    localTime s (creationTimeNat m k s) (0 - directionVector e) + 1 < m
  unfold canonicalTargetOriginSafe
  rw [htime, localTime_eq_of_pathPrefix_eq hp,
    localTime_eq_listLocalTime, hpath]

theorem sourceDistinguishedOriginSafeBaseFiber_subset_previous
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (e : Direction) (horigin : targetOriginBase t e ∉ eta.1.2)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (cap : ℕ) :
    sourceDistinguishedOriginSafeBaseFiber eta a candidate hcandidate low good
        e hm hk hwindow harithmetic hexternalArithmetic cap ⊆
      historyPiece t o m k (SourceSupportAt t o m)
        (targetOriginSafe m k e ∩ thresholdReachStage m k) (some eta) := by
  intro s hs
  rcases hs with ⟨hvalid, hevent⟩
  rcases Set.mem_iUnion.mp hevent with ⟨q, hq⟩
  have hsafeCanonical :=
    canonicalTargetOriginSafe_of_distinguishedTargetOriginSafe eta e horigin
      q.1 q.2.1.2
  have hsafe : s ∈ targetOriginSafe m k e :=
    (canonicalTargetOriginSafe_iff_of_mem_stopped eta e q.1 q.2.2 hvalid
      hq).mp hsafeCanonical
  have hordinary : s ∈ historyPiece t o m k (SourceSupportAt t o m)
      (thresholdReachStage m k) (some eta) := by
    apply (ordinaryRefinement eta a candidate hcandidate low good hm hk
      hwindow harithmetic hexternalArithmetic).base_subset_piece cap
    exact ⟨hvalid, Set.mem_iUnion.mpr ⟨⟨q.1, q.2.1.1, q.2.2⟩, hq⟩⟩
  exact ⟨⟨hsafe, hordinary.1⟩, hordinary.2⟩

private def sourceThresholdScreenedFiber
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (cap : ℕ) : Set WalkPath :=
  walkLift (prefixedTilingPreStoppingFiberEvent
    ((SourceFiber eta).stoppingTime cap) ((SourceFiber eta).initial cap) t
    ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
    ((SourceFiber eta).coordinateCap cap) ((SourceFiber eta).tail cap)
    ((ordinaryRefinement eta a candidate hcandidate low good hm hk hwindow
      harithmetic hexternalArithmetic).screenedPredicate cap))

private theorem sourceThresholdScreenedFiber_eq_sourceProp49ScreenedFiber
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (cap : ℕ) :
    sourceThresholdScreenedFiber eta a candidate hcandidate low good hm hk
        hwindow harithmetic hexternalArithmetic cap =
      sourceProp49ScreenedFiber eta a candidate hcandidate low cap := by
  rfl

theorem sourceDistinguishedOriginSafeScreenedFiber_eq
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (e : Direction) (horigin : targetOriginBase t e ∉ eta.1.2)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (cap : ℕ) :
    sourceDistinguishedOriginSafeScreenedFiber eta a candidate hcandidate low
        good e hm hk hwindow harithmetic hexternalArithmetic cap =
      sourceThresholdScreenedFiber eta a candidate hcandidate low good hm hk
          hwindow harithmetic hexternalArithmetic cap ∩
        targetOriginSafe m k e := by
  ext s
  constructor
  · intro hs
    rcases hs with ⟨hvalid, hevent⟩
    rcases Set.mem_iUnion.mp hevent with ⟨q, hq⟩
    have hsafeCanonical :=
      canonicalTargetOriginSafe_of_distinguishedTargetOriginSafe eta e
        horigin q.1 q.2.1.2
    have hsafe : s ∈ targetOriginSafe m k e :=
      (canonicalTargetOriginSafe_iff_of_mem_stopped eta e q.1 q.2.2 hvalid
        hq).mp hsafeCanonical
    refine ⟨⟨hvalid, Set.mem_iUnion.mpr ⟨⟨q.1, q.2.1.1, q.2.2⟩, hq⟩⟩,
      hsafe⟩
  · rintro ⟨hold, hsafe⟩
    rcases hold with ⟨hvalid, hevent⟩
    rcases Set.mem_iUnion.mp hevent with ⟨q, hq⟩
    have hsafeCanonical : canonicalTargetOriginSafe eta e cap q.1 :=
      (canonicalTargetOriginSafe_iff_of_mem_stopped eta e q.1 q.2.2 hvalid
        hq).mpr hsafe
    have hsafeDistinguished :=
      distinguishedTargetOriginSafe_of_canonical eta e q.1 hsafeCanonical
    exact ⟨hvalid, Set.mem_iUnion.mpr
      ⟨⟨q.1, ⟨q.2.1, hsafeDistinguished⟩, q.2.2⟩, hq⟩⟩

theorem measurableSet_sourceDistinguishedOriginSafeScreenedFiber
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (e : Direction) (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (cap : ℕ) :
    MeasurableSet (sourceDistinguishedOriginSafeScreenedFiber eta a candidate
      hcandidate low good e hm hk hwindow harithmetic hexternalArithmetic
      cap) := by
  apply measurableSet_walkLift
  exact measurableSet_prefixedTilingPreStoppingFiberEvent
    ((SourceFiber eta).isStoppingTime cap) ((SourceFiber eta).initial cap) t
    ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
    ((SourceFiber eta).coordinateCap cap) ((SourceFiber eta).tail cap)
    (sourceDistinguishedOriginSafeScreenedPredicate eta a candidate
      hcandidate low good e hm hk hwindow harithmetic hexternalArithmetic cap)

theorem measurableSet_sourceDistinguishedOriginSafeNear
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (e : Direction) (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    MeasurableSet (sourceDistinguishedOriginSafeNear eta a candidate
      hcandidate low good e hm hk hwindow harithmetic hexternalArithmetic) :=
  MeasurableSet.iUnion fun cap ↦
    measurableSet_sourceDistinguishedOriginSafeScreenedFiber eta a candidate
      hcandidate low good e hm hk hwindow harithmetic hexternalArithmetic cap

theorem monotone_sourceDistinguishedOriginSafeScreenedFiber
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (e : Direction) (horigin : targetOriginBase t e ∉ eta.1.2)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    Monotone fun cap ↦ sourceDistinguishedOriginSafeScreenedFiber eta a
      candidate hcandidate low good e hm hk hwindow harithmetic
      hexternalArithmetic cap := by
  intro cap cap' hcap s hs
  change s ∈ sourceDistinguishedOriginSafeScreenedFiber eta a candidate
    hcandidate low good e hm hk hwindow harithmetic hexternalArithmetic cap
    at hs
  change s ∈ sourceDistinguishedOriginSafeScreenedFiber eta a candidate
    hcandidate low good e hm hk hwindow harithmetic hexternalArithmetic cap'
  rw [sourceDistinguishedOriginSafeScreenedFiber_eq eta a candidate hcandidate
    low good e horigin hm hk hwindow harithmetic hexternalArithmetic cap] at hs
  rw [sourceDistinguishedOriginSafeScreenedFiber_eq eta a candidate hcandidate
    low good e horigin hm hk hwindow harithmetic hexternalArithmetic cap']
  exact ⟨(ordinaryRefinement eta a candidate hcandidate low good hm hk hwindow
    harithmetic hexternalArithmetic).monotone_screened hcap hs.1, hs.2⟩

/-- Exact source refinement for the non-exposed-origin branch.  Its product
bound is definitionally the ordinary Prop 4.9 bound; only the distinguished
carrier has been restricted. -/
noncomputable def sourceDistinguishedOriginSafeRefinement
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (e : Direction) (horigin : targetOriginBase t e ∉ eta.1.2)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    OrientedAllCreationConditionalRefinementData
      (withSelected (SourceFiber eta) (fun cap d ↦
        (SourceFiber eta).selected cap d ∧
          distinguishedTargetOriginSafe eta e cap d))
      (historyPiece t o m k (SourceSupportAt t o m)
        (targetOriginSafe m k e ∩ thresholdReachStage m k) (some eta))
      (historyPiece t o m k (SourceSupportAt t o m)
          (targetOriginSafe m k e ∩ thresholdReachStage m k) (some eta) ∩
        sourceDistinguishedOriginSafeNear eta a candidate hcandidate low good
          e hm hk hwindow harithmetic hexternalArithmetic)
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a) := by
  apply restrictRefinement (SourceFiber eta)
    (ordinaryRefinement eta a candidate hcandidate low good hm hk hwindow
      harithmetic hexternalArithmetic)
    (distinguishedTargetOriginSafe eta e)
  · exact sourceDistinguishedOriginSafeBaseFiber_subset_previous eta a
      candidate hcandidate low good e horigin hm hk hwindow harithmetic
      hexternalArithmetic
  · exact monotone_sourceDistinguishedOriginSafeScreenedFiber eta a candidate
      hcandidate low good e horigin hm hk hwindow harithmetic
      hexternalArithmetic
  · intro s hs
    exact hs.2.2

structure DistinguishedOriginSafeEligibleHistory
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (e : Direction) (eta : SourceSupportedIndex t o m k) : Prop where
  source : SourceProp49EligibleHistory eta
  origin_not_mem : targetOriginBase t e ∉ eta.1.2

noncomputable def sourceDistinguishedOriginSafeCandidateNear
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k) (a : GapScale) (low : ℕ)
    (e : Direction) (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (candidate : Point) : Set WalkPath := by
  classical
  exact if heligible : DistinguishedOriginSafeEligibleHistory e eta then
    if hcandidate : candidate ∈ eta.1.2 then
      sourceDistinguishedOriginSafeNear eta a candidate hcandidate low
        heligible.source.good e hm hk hwindow harithmetic hexternalArithmetic
    else ∅
  else ∅

theorem measurableSet_sourceDistinguishedOriginSafeCandidateNear
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k) (a : GapScale) (low : ℕ)
    (e : Direction) (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (candidate : Point) :
    MeasurableSet (sourceDistinguishedOriginSafeCandidateNear eta a low e hm
      hk hwindow harithmetic hexternalArithmetic candidate) := by
  classical
  simp only [sourceDistinguishedOriginSafeCandidateNear]
  split
  · split
    · exact measurableSet_sourceDistinguishedOriginSafeNear eta a candidate _
        low (‹DistinguishedOriginSafeEligibleHistory e eta›).source.good e hm
        hk hwindow harithmetic hexternalArithmetic
    · exact MeasurableSet.empty
  · exact MeasurableSet.empty

/-- The target stopped-history family for histories on which the shifted
origin is distinguished rather than exposed. -/
noncomputable def distinguishedOriginSafeTargetFamily
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (e : Direction)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    StoppedHistoryCandidateFamily
      (History t o m k (SourceSupportAt t o m)) Point
      (targetOriginSafe m k e ∩ thresholdReachStage m k)
      (initialBudget48 m)
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a) where
  piece := historyPiece t o m k (SourceSupportAt t o m)
    (targetOriginSafe m k e ∩ thresholdReachStage m k)
  candidates := filteredHistoryCandidates t o m k (SourceSupportAt t o m)
    (DistinguishedOriginSafeEligibleHistory e)
  near := fun h candidate ↦ match h with
    | none => ∅
    | some eta => sourceDistinguishedOriginSafeCandidateNear eta a low e hm
        hk hwindow harithmetic hexternalArithmetic candidate
  piece_pairwise := historyPiece_pairwise t o m k (SourceSupportAt t o m)
    (targetOriginSafe m k e ∩ thresholdReachStage m k)
  piece_measurable := measurableSet_historyPiece t o m k (SourceSupportAt t o m)
    (targetOriginSafe m k e ∩ thresholdReachStage m k)
    ((measurableSet_targetOriginSafe m k e).inter
      (measurableSet_thresholdReachStage m k))
    (orientedAllCreationConcreteFamily t o m k (SourceSupportAt t o m)
      (SourceSupportData t o m k))
  piece_union := iUnion_historyPiece t o m k (SourceSupportAt t o m)
    (targetOriginSafe m k e ∩ thresholdReachStage m k)
  candidate_card := by
    intro h
    cases h with
    | none => simp [filteredHistoryCandidates]
    | some eta =>
        classical
        by_cases heligible : DistinguishedOriginSafeEligibleHistory e eta
        · simpa [filteredHistoryCandidates, heligible] using
            heligible.source.card_le
        · simp [filteredHistoryCandidates, heligible]
  coordinate_ratio := by
    intro h candidate hcandidate
    cases h with
    | none => simp [filteredHistoryCandidates] at hcandidate
    | some eta =>
        have heligible := (mem_filteredHistoryCandidates_some_iff t o m k
          (SourceSupportAt t o m) (DistinguishedOriginSafeEligibleHistory e)
          eta candidate).mp hcandidate
        have href := sourceDistinguishedOriginSafeRefinement eta a candidate
          heligible.2 low heligible.1.source.good e
          heligible.1.origin_not_mem hm hk hwindow harithmetic
          hexternalArithmetic
        have hpiece := measurableSet_historyPiece t o m k
          (SourceSupportAt t o m)
          (targetOriginSafe m k e ∩ thresholdReachStage m k)
          ((measurableSet_targetOriginSafe m k e).inter
            (measurableSet_thresholdReachStage m k))
          (orientedAllCreationConcreteFamily t o m k (SourceSupportAt t o m)
            (SourceSupportData t o m k)) (some eta)
        have hnear := measurableSet_sourceDistinguishedOriginSafeCandidateNear
          eta a low e hm hk hwindow harithmetic hexternalArithmetic candidate
        apply coordinate_ratio_of_coordinateMassSpec hpiece hnear
          (prop49CandidateRatioEnvelope_ne_top _ _ _)
        simpa only [sourceDistinguishedOriginSafeCandidateNear, heligible.1,
          heligible.2, dite_true] using
          (coordinateMassSpecOfAllCreation
            (withSelected (SourceFiber eta) (fun cap d ↦
              (SourceFiber eta).selected cap d ∧
                distinguishedTargetOriginSafe eta e cap d)) href)

/-- A literal safe target path in a source-good atom belongs to the
non-exposed-origin target family. -/
theorem mem_distinguishedOriginSafeTargetFamily_of_path
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (e : Direction)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    {s : WalkPath} (hvalid : s ∈ validStepWalk)
    (hreach : s ∈ thresholdReachStage m k)
    (hsafe : s ∈ targetOriginSafe m k e)
    (hcard : (SourceSupportAt t o m s (creationTimeNat m k s)).card ≤
      initialBudget48 m)
    (htheta : orientedTilingThetaBases t o m (shellWidth48 m)
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m) s
      (creationTimeNat m k s) = ∅)
    (horigin : targetOriginBase t e ∉
      SourceSupportAt t o m s (creationTimeNat m k s))
    (candidate : Point)
    (hcandidate : candidate ∈
      SourceSupportAt t o m s (creationTimeNat m k s))
    (hnarrow : localTime s (creationTimeNat m k s) candidate ∈
      prop49NarrowTotalWindow m a) :
    s ∈ (distinguishedOriginSafeTargetFamily (t := t) (o := o) a low e hm hk
      hwindow harithmetic hexternalArithmetic).someCandidate := by
  classical
  let z := fixedOrientedAllCreationTraceCode t o
    (creationTimeNat m k s) s
  let S := SourceSupportAt t o m s (creationTimeNat m k s)
  have hsAtom : s ∈ orientedAllCreationSupportTraceAtom t o m k
      (SourceSupportAt t o m) z S :=
    ⟨⟨hvalid, hreach, rfl⟩, rfl⟩
  let eta : SourceSupportedIndex t o m k :=
    ⟨(z, S), ⟨s, hsAtom⟩⟩
  have hsourceEligible : SourceProp49EligibleHistory eta :=
    ⟨hcard, ⟨s, hsAtom, htheta⟩⟩
  have horiginEta : targetOriginBase t e ∉ eta.1.2 := horigin
  have hcandidateEta : candidate ∈ eta.1.2 := hcandidate
  have hordinary : s ∈ sourceProp49CandidateNear eta a low candidate :=
    mem_sourceProp49CandidateNear_of_exactAtom eta a candidate hcandidateEta
      low hm hk hwindow harithmetic hexternalArithmetic hsAtom htheta hnarrow
  simp only [sourceProp49CandidateNear, hcandidateEta, dite_true] at hordinary
  have hnear : s ∈ sourceDistinguishedOriginSafeCandidateNear eta a low e hm
      hk hwindow harithmetic hexternalArithmetic candidate := by
    simp only [sourceDistinguishedOriginSafeCandidateNear,
      show DistinguishedOriginSafeEligibleHistory e eta from
        ⟨hsourceEligible, horiginEta⟩,
      hcandidateEta, dite_true]
    rcases Set.mem_iUnion.mp hordinary with ⟨cap, hcap⟩
    apply Set.mem_iUnion.mpr
    refine ⟨cap, ?_⟩
    rw [sourceDistinguishedOriginSafeScreenedFiber_eq eta a candidate
      hcandidateEta low hsourceEligible.good e horiginEta hm hk hwindow
      harithmetic hexternalArithmetic cap,
      sourceThresholdScreenedFiber_eq_sourceProp49ScreenedFiber]
    exact ⟨hcap, hsafe⟩
  unfold StoppedHistoryCandidateFamily.someCandidate
  refine Set.mem_iUnion_of_mem (some eta) <|
    Set.mem_iUnion_of_mem candidate <| ?_
  let heligible : DistinguishedOriginSafeEligibleHistory e eta :=
    ⟨hsourceEligible, horiginEta⟩
  have hcandidates : candidate ∈ filteredHistoryCandidates t o m k
      (SourceSupportAt t o m) (DistinguishedOriginSafeEligibleHistory e)
      (some eta) :=
    (mem_filteredHistoryCandidates_some_iff t o m k
      (SourceSupportAt t o m) (DistinguishedOriginSafeEligibleHistory e)
      eta candidate).2 ⟨heligible, hcandidateEta⟩
  refine Set.mem_iUnion_of_mem hcandidates ?_
  exact ⟨⟨⟨hsafe, hreach⟩, hsAtom⟩, hnear⟩

noncomputable def completeOriginSafeCandidateNear
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k) (a : GapScale) (low : ℕ)
    (e : Direction) (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (candidate : Point) : Set WalkPath := by
  classical
  exact if heligible : SourceProp49EligibleHistory eta then
    if horigin : targetOriginBase t e ∈ eta.1.2 then
      sourceOriginSafeCandidateNear eta a low e candidate
    else sourceDistinguishedOriginSafeCandidateNear eta a low e hm hk hwindow
      harithmetic hexternalArithmetic candidate
  else ∅

theorem measurableSet_completeOriginSafeCandidateNear
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k) (a : GapScale) (low : ℕ)
    (e : Direction) (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (candidate : Point) :
    MeasurableSet (completeOriginSafeCandidateNear eta a low e hm hk hwindow
      harithmetic hexternalArithmetic candidate) := by
  classical
  simp only [completeOriginSafeCandidateNear]
  split
  · split
    · exact measurableSet_sourceOriginSafeCandidateNear eta a low e candidate
    · exact measurableSet_sourceDistinguishedOriginSafeCandidateNear eta a low
        e hm hk hwindow harithmetic hexternalArithmetic candidate
  · exact MeasurableSet.empty

/-- The complete target family.  Exposed-origin atoms use the one-away
origin screen; all complementary atoms use the distinguished-carrier
restriction.  The cases are disjoint, so no extra row constant is paid. -/
noncomputable def completeOriginSafeTargetFamily
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (e : Direction)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    StoppedHistoryCandidateFamily
      (History t o m k (SourceSupportAt t o m)) Point
      (targetOriginSafe m k e ∩ thresholdReachStage m k)
      (initialBudget48 m)
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a) where
  piece := historyPiece t o m k (SourceSupportAt t o m)
    (targetOriginSafe m k e ∩ thresholdReachStage m k)
  candidates := filteredHistoryCandidates t o m k (SourceSupportAt t o m)
    SourceProp49EligibleHistory
  near := fun h candidate ↦ match h with
    | none => ∅
    | some eta => completeOriginSafeCandidateNear eta a low e hm hk hwindow
        harithmetic hexternalArithmetic candidate
  piece_pairwise := historyPiece_pairwise t o m k (SourceSupportAt t o m)
    (targetOriginSafe m k e ∩ thresholdReachStage m k)
  piece_measurable := measurableSet_historyPiece t o m k
    (SourceSupportAt t o m)
    (targetOriginSafe m k e ∩ thresholdReachStage m k)
    ((measurableSet_targetOriginSafe m k e).inter
      (measurableSet_thresholdReachStage m k))
    (orientedAllCreationConcreteFamily t o m k (SourceSupportAt t o m)
      (SourceSupportData t o m k))
  piece_union := iUnion_historyPiece t o m k (SourceSupportAt t o m)
    (targetOriginSafe m k e ∩ thresholdReachStage m k)
  candidate_card := by
    intro h
    cases h with
    | none => simp [filteredHistoryCandidates]
    | some eta =>
        classical
        by_cases heligible : SourceProp49EligibleHistory eta
        · simpa [filteredHistoryCandidates, heligible] using heligible.card_le
        · simp [filteredHistoryCandidates, heligible]
  coordinate_ratio := by
    intro h candidate hcandidate
    cases h with
    | none => simp [filteredHistoryCandidates] at hcandidate
    | some eta =>
        have heligible := (mem_filteredHistoryCandidates_some_iff t o m k
          (SourceSupportAt t o m) SourceProp49EligibleHistory eta candidate).mp
          hcandidate
        by_cases horigin : targetOriginBase t e ∈ eta.1.2
        · have hcandidateExposed : candidate ∈
              (originSafeTargetFamily (t := t) (o := o) a low e hm hk hwindow
                harithmetic hwidth hexternalArithmetic).candidates (some eta) :=
            (mem_filteredHistoryCandidates_some_iff t o m k
              (SourceSupportAt t o m) (OriginSafeSourceProp49EligibleHistory e)
              eta candidate).2 ⟨⟨heligible.1, horigin⟩, heligible.2⟩
          have hratio := (originSafeTargetFamily (t := t) (o := o) a low e hm
            hk hwindow harithmetic hwidth hexternalArithmetic).coordinate_ratio
              (some eta) candidate hcandidateExposed
          change simpleRandomWalk
              (historyPiece t o m k (SourceSupportAt t o m)
                (targetOriginSafe m k e ∩ thresholdReachStage m k) (some eta) ∩
                sourceOriginSafeCandidateNear eta a low e candidate) ≤
            prop49CandidateRatioEnvelope prop49WindowRatioConstant m a *
              simpleRandomWalk (historyPiece t o m k (SourceSupportAt t o m)
                (targetOriginSafe m k e ∩ thresholdReachStage m k) (some eta))
            at hratio
          simpa [completeOriginSafeCandidateNear, heligible.1, horigin] using
            hratio
        · have hcandidateDistinguished : candidate ∈
              (distinguishedOriginSafeTargetFamily (t := t) (o := o) a low e
                hm hk hwindow harithmetic hexternalArithmetic).candidates
                (some eta) :=
            (mem_filteredHistoryCandidates_some_iff t o m k
              (SourceSupportAt t o m)
              (DistinguishedOriginSafeEligibleHistory e) eta candidate).2
              ⟨⟨heligible.1, horigin⟩, heligible.2⟩
          have hratio := (distinguishedOriginSafeTargetFamily
            (t := t) (o := o) a low e hm hk hwindow harithmetic
              hexternalArithmetic).coordinate_ratio (some eta) candidate
                hcandidateDistinguished
          change simpleRandomWalk
              (historyPiece t o m k (SourceSupportAt t o m)
                (targetOriginSafe m k e ∩ thresholdReachStage m k) (some eta) ∩
                sourceDistinguishedOriginSafeCandidateNear eta a low e hm hk
                  hwindow harithmetic hexternalArithmetic candidate) ≤
            prop49CandidateRatioEnvelope prop49WindowRatioConstant m a *
              simpleRandomWalk (historyPiece t o m k (SourceSupportAt t o m)
                (targetOriginSafe m k e ∩ thresholdReachStage m k) (some eta))
            at hratio
          simpa [completeOriginSafeCandidateNear, heligible.1, horigin] using
            hratio

theorem originSafeTargetFamily_someCandidate_subset_complete
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (e : Direction)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    (originSafeTargetFamily (t := t) (o := o) a low e hm hk hwindow
        harithmetic hwidth hexternalArithmetic).someCandidate ⊆
      (completeOriginSafeTargetFamily (t := t) (o := o) a low e hm hk hwindow
        harithmetic hwidth hexternalArithmetic).someCandidate := by
  classical
  intro s hs
  rcases Set.mem_iUnion.mp hs with ⟨h, hs⟩
  rcases Set.mem_iUnion.mp hs with ⟨candidate, hs⟩
  rcases Set.mem_iUnion.mp hs with ⟨hcandidate, hs⟩
  cases h with
  | none =>
      change candidate ∈ (∅ : Finset Point) at hcandidate
      simp at hcandidate
  | some eta =>
      have heligible := (mem_filteredHistoryCandidates_some_iff t o m k
        (SourceSupportAt t o m) (OriginSafeSourceProp49EligibleHistory e)
        eta candidate).mp hcandidate
      have hcompleteCandidate : candidate ∈ filteredHistoryCandidates t o m k
          (SourceSupportAt t o m) SourceProp49EligibleHistory (some eta) :=
        (mem_filteredHistoryCandidates_some_iff t o m k
          (SourceSupportAt t o m) SourceProp49EligibleHistory eta candidate).2
          ⟨heligible.1.source, heligible.2⟩
      unfold StoppedHistoryCandidateFamily.someCandidate
      refine Set.mem_iUnion_of_mem (some eta) <|
        Set.mem_iUnion_of_mem candidate <|
          Set.mem_iUnion_of_mem hcompleteCandidate ?_
      refine ⟨hs.1, ?_⟩
      have hnear := hs.2
      change s ∈ sourceOriginSafeCandidateNear eta a low e candidate at hnear
      change s ∈ completeOriginSafeCandidateNear eta a low e hm hk hwindow
        harithmetic hexternalArithmetic candidate
      simpa [completeOriginSafeCandidateNear, heligible.1.source,
        heligible.1.origin_mem] using hnear

theorem distinguishedOriginSafeTargetFamily_someCandidate_subset_complete
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (e : Direction)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    (distinguishedOriginSafeTargetFamily (t := t) (o := o) a low e hm hk
        hwindow harithmetic hexternalArithmetic).someCandidate ⊆
      (completeOriginSafeTargetFamily (t := t) (o := o) a low e hm hk hwindow
        harithmetic hwidth hexternalArithmetic).someCandidate := by
  classical
  intro s hs
  rcases Set.mem_iUnion.mp hs with ⟨h, hs⟩
  rcases Set.mem_iUnion.mp hs with ⟨candidate, hs⟩
  rcases Set.mem_iUnion.mp hs with ⟨hcandidate, hs⟩
  cases h with
  | none =>
      change candidate ∈ (∅ : Finset Point) at hcandidate
      simp at hcandidate
  | some eta =>
      have heligible := (mem_filteredHistoryCandidates_some_iff t o m k
        (SourceSupportAt t o m) (DistinguishedOriginSafeEligibleHistory e)
        eta candidate).mp hcandidate
      have hcompleteCandidate : candidate ∈ filteredHistoryCandidates t o m k
          (SourceSupportAt t o m) SourceProp49EligibleHistory (some eta) :=
        (mem_filteredHistoryCandidates_some_iff t o m k
          (SourceSupportAt t o m) SourceProp49EligibleHistory eta candidate).2
          ⟨heligible.1.source, heligible.2⟩
      unfold StoppedHistoryCandidateFamily.someCandidate
      refine Set.mem_iUnion_of_mem (some eta) <|
        Set.mem_iUnion_of_mem candidate <|
          Set.mem_iUnion_of_mem hcompleteCandidate ?_
      refine ⟨hs.1, ?_⟩
      have hnear := hs.2
      change s ∈ sourceDistinguishedOriginSafeCandidateNear eta a low e hm hk
        hwindow harithmetic hexternalArithmetic candidate at hnear
      change s ∈ completeOriginSafeCandidateNear eta a low e hm hk hwindow
        harithmetic hexternalArithmetic candidate
      simpa [completeOriginSafeCandidateNear, heligible.1.source,
        heligible.1.origin_not_mem] using hnear

theorem mem_completeOriginSafeTargetFamily_of_path
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (e : Direction)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    {s : WalkPath} (hvalid : s ∈ validStepWalk)
    (hreach : s ∈ thresholdReachStage m k)
    (hsafe : s ∈ targetOriginSafe m k e)
    (hcard : (SourceSupportAt t o m s (creationTimeNat m k s)).card ≤
      initialBudget48 m)
    (htheta : orientedTilingThetaBases t o m (shellWidth48 m)
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m) s
      (creationTimeNat m k s) = ∅)
    (candidate : Point)
    (hcandidate : candidate ∈
      SourceSupportAt t o m s (creationTimeNat m k s))
    (hnarrow : localTime s (creationTimeNat m k s) candidate ∈
      prop49NarrowTotalWindow m a) :
    s ∈ (completeOriginSafeTargetFamily (t := t) (o := o) a low e hm hk
      hwindow harithmetic hwidth hexternalArithmetic).someCandidate := by
  by_cases horigin : targetOriginBase t e ∈
      SourceSupportAt t o m s (creationTimeNat m k s)
  · apply originSafeTargetFamily_someCandidate_subset_complete a low e hm hk
      hwindow harithmetic hwidth hexternalArithmetic
    exact mem_originSafeTargetFamily_of_path a low e hm hk hwindow harithmetic
      hwidth hexternalArithmetic hvalid hreach hsafe hcard htheta horigin
      candidate hcandidate hnarrow
  · apply distinguishedOriginSafeTargetFamily_someCandidate_subset_complete
      a low e hm hk hwindow harithmetic hwidth hexternalArithmetic
    exact mem_distinguishedOriginSafeTargetFamily_of_path a low e hm hk hwindow
      harithmetic hexternalArithmetic hvalid hreach hsafe hcard htheta horigin
      candidate hcandidate hnarrow

theorem completeOriginSafeTargetFamily_near_measurable
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (e : Direction)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    ∀ h candidate, MeasurableSet
      ((completeOriginSafeTargetFamily (t := t) (o := o) a low e hm hk hwindow
        harithmetic hwidth hexternalArithmetic).near h candidate) := by
  intro h candidate
  cases h with
  | none => exact MeasurableSet.empty
  | some eta =>
      exact measurableSet_completeOriginSafeCandidateNear eta a low e hm hk
        hwindow harithmetic hexternalArithmetic candidate

/-- The complete fixed-first-direction checker family. -/
noncomputable def checkerCompleteOriginSafeFamily
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (e : Direction)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    StoppedHistoryCandidateFamily
      (History t o m k (SourceSupportAt t o m)) Point
      (checkerPrefixedPreimage e
        (targetOriginSafe m k e ∩ thresholdReachStage m k))
      (initialBudget48 m)
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a) :=
  checkerFixedPrefixFamily e
    (completeOriginSafeTargetFamily (t := t) (o := o) a low e hm hk hwindow
      harithmetic hwidth hexternalArithmetic)
    (completeOriginSafeTargetFamily_near_measurable a low e hm hk hwindow
      harithmetic hwidth hexternalArithmetic)

theorem checkerCompleteOriginSafeFamily_someCandidate
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (e : Direction)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    (checkerCompleteOriginSafeFamily (t := t) (o := o) a low e hm hk hwindow
      harithmetic hwidth hexternalArithmetic).someCandidate =
      checkerPrefixedPreimage e
        (completeOriginSafeTargetFamily (t := t) (o := o) a low e hm hk
          hwindow harithmetic hwidth hexternalArithmetic).someCandidate :=
  StoppedHistoryCandidateFamily.someCandidate_checkerFixedPrefixFamily e _
    (completeOriginSafeTargetFamily_near_measurable a low e hm hk hwindow
      harithmetic hwidth hexternalArithmetic)

theorem mem_checkerCompleteOriginSafeFamily_of_target_path
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (e : Direction)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hwidth : 3 ≤ shellWidth48 m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    {s : WalkPath} (hfirst : s 1 = directionVector e)
    (hvalid : oneStepRecenter s ∈ validStepWalk)
    (hreach : oneStepRecenter s ∈ thresholdReachStage m k)
    (hsafe : oneStepRecenter s ∈ targetOriginSafe m k e)
    (hcard : (SourceSupportAt t o m (oneStepRecenter s)
      (creationTimeNat m k (oneStepRecenter s))).card ≤ initialBudget48 m)
    (htheta : orientedTilingThetaBases t o m (shellWidth48 m)
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)
      (oneStepRecenter s) (creationTimeNat m k (oneStepRecenter s)) = ∅)
    (candidate : Point)
    (hcandidate : candidate ∈ SourceSupportAt t o m (oneStepRecenter s)
      (creationTimeNat m k (oneStepRecenter s)))
    (hnarrow : localTime (oneStepRecenter s)
      (creationTimeNat m k (oneStepRecenter s)) candidate ∈
        prop49NarrowTotalWindow m a) :
    s ∈ (checkerCompleteOriginSafeFamily (t := t) (o := o) a low e hm hk
      hwindow harithmetic hwidth hexternalArithmetic).someCandidate := by
  rw [checkerCompleteOriginSafeFamily_someCandidate]
  refine ⟨?_, mem_completeOriginSafeTargetFamily_of_path a low e hm hk hwindow
    harithmetic hwidth hexternalArithmetic hvalid hreach hsafe hcard htheta
    candidate hcandidate hnarrow⟩
  simpa only [firstDirectionWalk, Set.mem_ofPred_eq] using hfirst

end


end Erdos1165.HLOZCheckerOriginSafeDistinguishedProp49Family
