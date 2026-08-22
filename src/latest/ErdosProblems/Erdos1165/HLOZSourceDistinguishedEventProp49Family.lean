/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPrefixedAllCreationDistinguishedRestriction
import ErdosProblems.Erdos1165.HLOZPrefixedCanonicalSourceProp49PathCoverage
import ErdosProblems.Erdos1165.HLOZPrefixedCanonicalSourceProp49Refinement
import ErdosProblems.Erdos1165.HLOZSourceStructuralPastInvariant

/-!
# Proposition 4.9 source families restricted by a distinguished event

If a path event is constant both on distinguished source-coordinate fibres
and on stopped cylinders through the creation clock, it can be inserted in
the distinguished carrier of the canonical conditional product.  The away
coordinate ratio is unchanged.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZSourceDistinguishedEventProp49Family

open HLOZFilteredOrientedAllCreationStoppedCandidateFamily
open HLOZMeshCandidatePolynomialNumerics
open HLOZOrientedAllCreationStoppedCandidateFamily
open HLOZPathEvents HLOZPrefixedAllCreationDistinguishedRestriction
open HLOZPrefixedCanonicalSourceAtomRecovery
open HLOZPrefixedCanonicalSourceLowRecovery
open HLOZPrefixedCanonicalSourceProp49Data
open HLOZPrefixedCanonicalSourceProp49PathCoverage
open HLOZPrefixedCanonicalSourceProp49Refinement
open HLOZPrefixedProp49CandidateWindowRatio HLOZProposition48Candidates
open HLOZShellZeroExternalWindow HLOZShellZeroReplacementWindows
open HLOZSourceOrientedThetaWindowSplit
open HLOZStoppedHistoryCandidateFuture
open HLOZTypedStoppedCandidateConditionalProduct
open LazyDecomposition PathInsertion PreStoppingFiber PreStoppingSpatialLaw
open SpatialInsertionFiber StoppedInsertion
open TilingCappedMarginalization TilingConditionalCappedMarginalization
open TilingInsertedLocalTime TilingLazyDecomposition
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedFavoriteTraceSupport TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

private theorem zero_not_mem_sourceWindow
    {m : ℕ} (_hm : 1 < m) :
    0 ∉ shellZeroSourceTotalWindow m (shellWidth48 m) := by
  simp only [mem_shellZeroSourceTotalWindow]
  omega

/-- The ordinary canonical source refinement on the bare reaching stage. -/
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

/-- A distinguished assignment is safe when one accepted canonical full
coordinate vector above it lies in the requested event. -/
def distinguishedEventSafe
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k) (event : Set WalkPath)
    (cap : ℕ)
    (d : TilingDistinguishedCoordinates
      (cap := (SourceFiber eta).coordinateCap cap) t
      eta.1.1.external.start eta.1.1.external.retained
      ((SourceFiber eta).distinguished cap)) : Prop :=
  ∃ q : TilingCappedCoordinates eta.1.1.external.retainedCount
      ((SourceFiber eta).coordinateCap cap),
    (splitTilingCoordinatesEquiv t ((SourceFiber eta).start cap)
      ((SourceFiber eta).retained cap) ((SourceFiber eta).distinguished cap)
      q).1 = d ∧
    (SourceFiber eta).atomPredicate cap q ∧
    PrefixedTilingStoppingAccepted ((SourceFiber eta).stoppingTime cap)
      ((SourceFiber eta).initial cap) t ((SourceFiber eta).start cap)
      ((SourceFiber eta).retained cap) (fun j ↦ (q j : ℕ))
      ((SourceFiber eta).tail cap) ∧
    trajectory (extendPrefix (directionVectorOfList
      (prefixedTilingInsertionPrefixList ((SourceFiber eta).initial cap) t
        ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
        (fun j ↦ (q j : ℕ)) ((SourceFiber eta).tail cap)))) ∈ event

noncomputable def sourceEventBasePredicate
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (event : Set WalkPath) (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (cap : ℕ) :=
  restrictPredicate (SourceFiber eta) (distinguishedEventSafe eta event)
    (ordinaryRefinement eta a candidate hcandidate low good hm hk hwindow
      harithmetic hexternalArithmetic).basePredicate cap

noncomputable def sourceEventScreenedPredicate
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (event : Set WalkPath) (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (cap : ℕ) :=
  restrictPredicate (SourceFiber eta) (distinguishedEventSafe eta event)
    (ordinaryRefinement eta a candidate hcandidate low good hm hk hwindow
      harithmetic hexternalArithmetic).screenedPredicate cap

def sourceEventBaseFiber
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (event : Set WalkPath) (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (cap : ℕ) : Set WalkPath :=
  walkLift (prefixedTilingPreStoppingFiberEvent
    ((SourceFiber eta).stoppingTime cap) ((SourceFiber eta).initial cap) t
    ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
    ((SourceFiber eta).coordinateCap cap) ((SourceFiber eta).tail cap)
    (sourceEventBasePredicate eta a candidate hcandidate low good event hm hk
      hwindow harithmetic hexternalArithmetic cap))

def sourceEventScreenedFiber
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (event : Set WalkPath) (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (cap : ℕ) : Set WalkPath :=
  walkLift (prefixedTilingPreStoppingFiberEvent
    ((SourceFiber eta).stoppingTime cap) ((SourceFiber eta).initial cap) t
    ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
    ((SourceFiber eta).coordinateCap cap) ((SourceFiber eta).tail cap)
    (sourceEventScreenedPredicate eta a candidate hcandidate low good event hm
      hk hwindow harithmetic hexternalArithmetic cap))

def sourceEventNear
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (event : Set WalkPath) (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) : Set WalkPath :=
  ⋃ cap, sourceEventScreenedFiber eta a candidate hcandidate low good event hm
    hk hwindow harithmetic hexternalArithmetic cap

/-- Event invariance required on each distinguished source fibre. -/
def SourceEventDistinguishedInvariant
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k) (event : Set WalkPath) : Prop :=
  ∀ cap
    (q q' : TilingCappedCoordinates eta.1.1.external.retainedCount
      ((SourceFiber eta).coordinateCap cap)),
    (splitTilingCoordinatesEquiv t eta.1.1.external.start
        eta.1.1.external.retained
        (supportComplementDistinguished t eta.1.1.external.start
          eta.1.1.external.retained eta.1.2) q).1 =
      (splitTilingCoordinatesEquiv t eta.1.1.external.start
        eta.1.1.external.retained
        (supportComplementDistinguished t eta.1.1.external.start
          eta.1.1.external.retained eta.1.2) q').1 →
    (SourceFiber eta).atomPredicate cap q →
    PrefixedTilingStoppingAccepted ((SourceFiber eta).stoppingTime cap)
      ((SourceFiber eta).initial cap) t ((SourceFiber eta).start cap)
      ((SourceFiber eta).retained cap) (fun j ↦ (q j : ℕ))
      ((SourceFiber eta).tail cap) →
    (SourceFiber eta).atomPredicate cap q' →
    PrefixedTilingStoppingAccepted ((SourceFiber eta).stoppingTime cap)
      ((SourceFiber eta).initial cap) t ((SourceFiber eta).start cap)
      ((SourceFiber eta).retained cap) (fun j ↦ (q' j : ℕ))
      ((SourceFiber eta).tail cap) →
    (trajectory (extendPrefix (directionVectorOfList
        (prefixedTilingInsertionPrefixList ((SourceFiber eta).initial cap) t
          ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
          (fun j ↦ (q j : ℕ)) ((SourceFiber eta).tail cap)))) ∈ event ↔
      trajectory (extendPrefix (directionVectorOfList
        (prefixedTilingInsertionPrefixList ((SourceFiber eta).initial cap) t
          ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
          (fun j ↦ (q' j : ℕ)) ((SourceFiber eta).tail cap)))) ∈ event)

/-- Event invariance required on every stopped cylinder through the final
rank-`k` creation clock. -/
def SourceEventPrefixInvariant (m k : ℕ) (event : Set WalkPath) : Prop :=
  ∀ {s s' : WalkPath} {N : ℕ}, pathPrefix s N = pathPrefix s' N →
    ThresholdCreation s m k N → ThresholdCreation s' m k N →
    (s ∈ event ↔ s' ∈ event)

theorem canonical_mem_event_of_distinguishedEventSafe
    {t : DominoTiling} {o : Orientation} {m k cap : ℕ}
    {eta : SourceSupportedIndex t o m k} {event : Set WalkPath}
    (hinvariant : SourceEventDistinguishedInvariant eta event)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      ((SourceFiber eta).coordinateCap cap))
    (hpred : (SourceFiber eta).atomPredicate cap q)
    (haccepted : PrefixedTilingStoppingAccepted
      ((SourceFiber eta).stoppingTime cap) ((SourceFiber eta).initial cap) t
      ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
      (fun j ↦ (q j : ℕ)) ((SourceFiber eta).tail cap))
    (hsafe : distinguishedEventSafe eta event cap
      ((splitTilingCoordinatesEquiv t ((SourceFiber eta).start cap)
        ((SourceFiber eta).retained cap) ((SourceFiber eta).distinguished cap)
        q).1)) :
    trajectory (extendPrefix (directionVectorOfList
      (prefixedTilingInsertionPrefixList ((SourceFiber eta).initial cap) t
        ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
        (fun j ↦ (q j : ℕ)) ((SourceFiber eta).tail cap)))) ∈ event := by
  rcases hsafe with ⟨q', hdist, hpred', haccepted', hevent'⟩
  have hcanonical := canonical_mem_supportAtom_of_predicate_accepted
    ((SourceFiber eta).coordinateCap cap) q hpred haccepted
  have hcanonical' := canonical_mem_supportAtom_of_predicate_accepted
    ((SourceFiber eta).coordinateCap cap) q' hpred' haccepted'
  exact (hinvariant cap q q' hdist.symm hpred haccepted hpred' haccepted').mpr
    hevent'

theorem distinguishedEventSafe_of_canonical_mem_event
    {t : DominoTiling} {o : Orientation} {m k cap : ℕ}
    {eta : SourceSupportedIndex t o m k} {event : Set WalkPath}
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      ((SourceFiber eta).coordinateCap cap))
    (hpred : (SourceFiber eta).atomPredicate cap q)
    (haccepted : PrefixedTilingStoppingAccepted
      ((SourceFiber eta).stoppingTime cap) ((SourceFiber eta).initial cap) t
      ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
      (fun j ↦ (q j : ℕ)) ((SourceFiber eta).tail cap))
    (hevent : trajectory (extendPrefix (directionVectorOfList
      (prefixedTilingInsertionPrefixList ((SourceFiber eta).initial cap) t
        ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
        (fun j ↦ (q j : ℕ)) ((SourceFiber eta).tail cap)))) ∈ event) :
    distinguishedEventSafe eta event cap
      ((splitTilingCoordinatesEquiv t ((SourceFiber eta).start cap)
        ((SourceFiber eta).retained cap) ((SourceFiber eta).distinguished cap)
        q).1) :=
  ⟨q, rfl, hpred, haccepted, hevent⟩

/-- Membership in an event observable through the creation clock agrees
with membership of the canonical stopped-cylinder representative. -/
theorem event_iff_canonical_of_mem_stopped
    {t : DominoTiling} {o : Orientation} {m k cap : ℕ}
    {eta : SourceSupportedIndex t o m k} {event : Set WalkPath}
    (hk : 0 < k) (hprefix : SourceEventPrefixInvariant m k event)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      ((SourceFiber eta).coordinateCap cap))
    (haccepted : PrefixedTilingStoppingAccepted
      ((SourceFiber eta).stoppingTime cap) ((SourceFiber eta).initial cap) t
      ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
      (fun j ↦ (q j : ℕ)) ((SourceFiber eta).tail cap))
    (omega : StepPath)
    (hword : omega ∈ prefixedTilingStoppedInsertionAtom
      ((SourceFiber eta).stoppingTime cap) ((SourceFiber eta).initial cap) t
      ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
      (fun j ↦ (q j : ℕ)) ((SourceFiber eta).tail cap)) :
    trajectory omega ∈ event ↔
      trajectory (extendPrefix (directionVectorOfList
        (prefixedTilingInsertionPrefixList ((SourceFiber eta).initial cap) t
          ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
          (fun j ↦ (q j : ℕ)) ((SourceFiber eta).tail cap)))) ∈ event := by
  let v := prefixedTilingInsertionPrefixList ((SourceFiber eta).initial cap) t
    ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
    (fun j ↦ (q j : ℕ)) ((SourceFiber eta).tail cap)
  let sq := trajectory (extendPrefix (directionVectorOfList v))
  have hp : pathPrefix (trajectory omega) v.length = pathPrefix sq v.length := by
    simpa only [v, sq] using
      (pathPrefix_eq_canonical_of_mem_prefixedTilingStoppedInsertionAtom
        ((SourceFiber eta).initial cap) ((SourceFiber eta).start cap)
        ((SourceFiber eta).retained cap) (fun j ↦ (q j : ℕ))
        ((SourceFiber eta).tail cap) omega hword)
  have hlt : v.length < orientedAllCreationCoordinateCutoff eta.1.1
      ((SourceFiber eta).coordinateCap cap) := by
    simpa only [v,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.initial,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.start,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.retained,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.tail] using
      (prefixedInsertion_lt_orientedAllCreationCoordinateCutoff eta.1.1
        ((SourceFiber eta).coordinateCap cap) q)
  have hcanonical : ThresholdCreation sq m k v.length := by
    change truncatedLevelTime m k
        (orientedAllCreationCoordinateCutoff eta.1.1
          ((SourceFiber eta).coordinateCap cap))
        (extendPrefix (directionVectorOfList v)) = v.length at haccepted
    exact (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m k (orientedAllCreationCoordinateCutoff eta.1.1
        ((SourceFiber eta).coordinateCap cap)) v.length _ hlt).mp haccepted
  have hactual : ThresholdCreation (trajectory omega) m k v.length := by
    have hstop := hword.1
    change truncatedLevelTime m k
        (orientedAllCreationCoordinateCutoff eta.1.1
          ((SourceFiber eta).coordinateCap cap)) omega = v.length at hstop
    exact (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m k (orientedAllCreationCoordinateCutoff eta.1.1
        ((SourceFiber eta).coordinateCap cap)) v.length omega hlt).mp hstop
  exact hprefix hp hactual hcanonical

theorem sourceEventBaseFiber_subset_previous
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (event : Set WalkPath)
    (hinvariant : SourceEventDistinguishedInvariant eta event)
    (hprefix : SourceEventPrefixInvariant m k event)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (cap : ℕ) :
    sourceEventBaseFiber eta a candidate hcandidate low good event hm hk
        hwindow harithmetic hexternalArithmetic cap ⊆
      historyPiece t o m k (SourceSupportAt t o m) event (some eta) := by
  intro s hs
  rcases hs with ⟨hvalid, hevent⟩
  rcases Set.mem_iUnion.mp hevent with ⟨q, hq⟩
  have hpred := (ordinaryRefinement eta a candidate hcandidate low good hm hk
    hwindow harithmetic hexternalArithmetic).base_subset_atom cap q.1
      q.2.1.1
  have hcanonicalEvent := canonical_mem_event_of_distinguishedEventSafe
    hinvariant q.1 hpred q.2.2 q.2.1.2
  have hactualEvent : s ∈ event := by
    have heq := event_iff_canonical_of_mem_stopped hk hprefix q.1 q.2.2
      (stepsOfWalk s) hq
    change trajectory (stepsOfWalk s) = s at hvalid
    rw [hvalid] at heq
    exact heq.mpr hcanonicalEvent
  have hatom : s ∈ orientedAllCreationSupportTraceAtom t o m k
      (SourceSupportAt t o m) eta.1.1 eta.1.2 := by
    apply (SourceFiber eta).atom_sound cap
    exact ⟨hvalid, Set.mem_iUnion.mpr
      ⟨⟨q.1, hpred, q.2.2⟩, hq⟩⟩
  exact ⟨hactualEvent, hatom⟩

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

theorem sourceEventScreenedFiber_eq
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (event : Set WalkPath)
    (hinvariant : SourceEventDistinguishedInvariant eta event)
    (hprefix : SourceEventPrefixInvariant m k event)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (cap : ℕ) :
    sourceEventScreenedFiber eta a candidate hcandidate low good event hm hk
        hwindow harithmetic hexternalArithmetic cap =
      sourceThresholdScreenedFiber eta a candidate hcandidate low good hm hk
          hwindow harithmetic hexternalArithmetic cap ∩ event := by
  ext s
  constructor
  · intro hs
    rcases hs with ⟨hvalid, hevent⟩
    rcases Set.mem_iUnion.mp hevent with ⟨q, hq⟩
    have hbase := (ordinaryRefinement eta a candidate hcandidate low good hm hk
      hwindow harithmetic hexternalArithmetic).screened_subset_basePredicate
        cap q.1 q.2.1.1
    have hpred := (ordinaryRefinement eta a candidate hcandidate low good hm hk
      hwindow harithmetic hexternalArithmetic).base_subset_atom cap q.1 hbase
    have hcanonicalEvent := canonical_mem_event_of_distinguishedEventSafe
      hinvariant q.1 hpred q.2.2 q.2.1.2
    have hactualEvent : s ∈ event := by
      have heq := event_iff_canonical_of_mem_stopped hk hprefix q.1 q.2.2
        (stepsOfWalk s) hq
      change trajectory (stepsOfWalk s) = s at hvalid
      rw [hvalid] at heq
      exact heq.mpr hcanonicalEvent
    exact ⟨⟨hvalid, Set.mem_iUnion.mpr
      ⟨⟨q.1, q.2.1.1, q.2.2⟩, hq⟩⟩, hactualEvent⟩
  · rintro ⟨hold, heventActual⟩
    rcases hold with ⟨hvalid, hfiber⟩
    rcases Set.mem_iUnion.mp hfiber with ⟨q, hq⟩
    have hbase := (ordinaryRefinement eta a candidate hcandidate low good hm hk
      hwindow harithmetic hexternalArithmetic).screened_subset_basePredicate
        cap q.1 q.2.1
    have hpred := (ordinaryRefinement eta a candidate hcandidate low good hm hk
      hwindow harithmetic hexternalArithmetic).base_subset_atom cap q.1 hbase
    have hcanonicalEvent : trajectory (extendPrefix (directionVectorOfList
        (prefixedTilingInsertionPrefixList ((SourceFiber eta).initial cap) t
          ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
          (fun j ↦ (q.1 j : ℕ)) ((SourceFiber eta).tail cap)))) ∈ event := by
      have heq := event_iff_canonical_of_mem_stopped hk hprefix q.1 q.2.2
        (stepsOfWalk s) hq
      change trajectory (stepsOfWalk s) = s at hvalid
      rw [hvalid] at heq
      exact heq.mp heventActual
    have hsafe := distinguishedEventSafe_of_canonical_mem_event q.1 hpred
      q.2.2 hcanonicalEvent
    exact ⟨hvalid, Set.mem_iUnion.mpr
      ⟨⟨q.1, ⟨q.2.1, hsafe⟩, q.2.2⟩, hq⟩⟩

theorem measurableSet_sourceEventScreenedFiber
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (event : Set WalkPath) (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (cap : ℕ) :
    MeasurableSet (sourceEventScreenedFiber eta a candidate hcandidate low
      good event hm hk hwindow harithmetic hexternalArithmetic cap) := by
  apply measurableSet_walkLift
  exact measurableSet_prefixedTilingPreStoppingFiberEvent
    ((SourceFiber eta).isStoppingTime cap) ((SourceFiber eta).initial cap) t
    ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
    ((SourceFiber eta).coordinateCap cap) ((SourceFiber eta).tail cap)
    (sourceEventScreenedPredicate eta a candidate hcandidate low good event hm
      hk hwindow harithmetic hexternalArithmetic cap)

theorem measurableSet_sourceEventNear
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (event : Set WalkPath) (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    MeasurableSet (sourceEventNear eta a candidate hcandidate low good event hm
      hk hwindow harithmetic hexternalArithmetic) :=
  MeasurableSet.iUnion fun cap ↦
    measurableSet_sourceEventScreenedFiber eta a candidate hcandidate low
      good event hm hk hwindow harithmetic hexternalArithmetic cap

theorem monotone_sourceEventScreenedFiber
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (event : Set WalkPath)
    (hinvariant : SourceEventDistinguishedInvariant eta event)
    (hprefix : SourceEventPrefixInvariant m k event)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    Monotone fun cap ↦ sourceEventScreenedFiber eta a candidate hcandidate low
      good event hm hk hwindow harithmetic hexternalArithmetic cap := by
  intro cap cap' hcap s hs
  change s ∈ sourceEventScreenedFiber eta a candidate hcandidate low good event
    hm hk hwindow harithmetic hexternalArithmetic cap at hs
  rw [sourceEventScreenedFiber_eq eta a candidate hcandidate low good event
    hinvariant hprefix hm hk hwindow harithmetic hexternalArithmetic cap] at hs
  change s ∈ sourceEventScreenedFiber eta a candidate hcandidate low good event
    hm hk hwindow harithmetic hexternalArithmetic cap'
  rw [sourceEventScreenedFiber_eq eta a candidate hcandidate low good event
    hinvariant hprefix hm hk hwindow harithmetic hexternalArithmetic cap']
  exact ⟨(ordinaryRefinement eta a candidate hcandidate low good hm hk hwindow
    harithmetic hexternalArithmetic).monotone_screened hcap hs.1, hs.2⟩

/-- The canonical conditional refinement after restricting only its
distinguished carrier by `event`. -/
noncomputable def sourceEventRefinement
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) (good : SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (event : Set WalkPath)
    (hinvariant : SourceEventDistinguishedInvariant eta event)
    (hprefix : SourceEventPrefixInvariant m k event)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    OrientedAllCreationConditionalRefinementData
      (withSelected (SourceFiber eta) (fun cap d ↦
        (SourceFiber eta).selected cap d ∧ distinguishedEventSafe eta event cap d))
      (historyPiece t o m k (SourceSupportAt t o m) event (some eta))
      (historyPiece t o m k (SourceSupportAt t o m) event (some eta) ∩
        sourceEventNear eta a candidate hcandidate low good event hm hk hwindow
          harithmetic hexternalArithmetic)
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a) := by
  apply restrictRefinement (SourceFiber eta)
    (ordinaryRefinement eta a candidate hcandidate low good hm hk hwindow
      harithmetic hexternalArithmetic)
    (distinguishedEventSafe eta event)
  · exact sourceEventBaseFiber_subset_previous eta a candidate hcandidate low
      good event hinvariant hprefix hm hk hwindow harithmetic
      hexternalArithmetic
  · exact monotone_sourceEventScreenedFiber eta a candidate hcandidate low
      good event hinvariant hprefix hm hk hwindow harithmetic
      hexternalArithmetic
  · intro s hs
    exact hs.2.2

noncomputable def sourceEventCandidateNear
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k) (a : GapScale) (low : ℕ)
    (event : Set WalkPath) (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (candidate : Point) : Set WalkPath := by
  classical
  exact if heligible : SourceProp49EligibleHistory eta then
    if hcandidate : candidate ∈ eta.1.2 then
      sourceEventNear eta a candidate hcandidate low heligible.good event hm hk
        hwindow harithmetic hexternalArithmetic
    else ∅
  else ∅

theorem measurableSet_sourceEventCandidateNear
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k) (a : GapScale) (low : ℕ)
    (event : Set WalkPath) (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (candidate : Point) :
    MeasurableSet (sourceEventCandidateNear eta a low event hm hk hwindow
      harithmetic hexternalArithmetic candidate) := by
  classical
  simp only [sourceEventCandidateNear]
  split
  · split
    · exact measurableSet_sourceEventNear eta a candidate _ low
        (‹SourceProp49EligibleHistory eta›).good event hm hk hwindow harithmetic
        hexternalArithmetic
    · exact MeasurableSet.empty
  · exact MeasurableSet.empty

/-- The stopped candidate family whose pieces partition `event`; its
coordinate ratio is exactly the unrestricted Proposition 4.9 ratio. -/
noncomputable def sourceEventTargetFamily
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (event : Set WalkPath)
    (hevent : MeasurableSet event)
    (hinvariant : ∀ eta : SourceSupportedIndex t o m k,
      SourceEventDistinguishedInvariant eta event)
    (hprefix : SourceEventPrefixInvariant m k event)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    StoppedHistoryCandidateFamily
      (History t o m k (SourceSupportAt t o m)) Point event
      (initialBudget48 m)
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a) where
  piece := historyPiece t o m k (SourceSupportAt t o m) event
  candidates := filteredHistoryCandidates t o m k (SourceSupportAt t o m)
    SourceProp49EligibleHistory
  near := fun h candidate ↦ match h with
    | none => ∅
    | some eta => sourceEventCandidateNear eta a low event hm hk hwindow
        harithmetic hexternalArithmetic candidate
  piece_pairwise := historyPiece_pairwise t o m k (SourceSupportAt t o m) event
  piece_measurable := measurableSet_historyPiece t o m k
    (SourceSupportAt t o m) event hevent
    (orientedAllCreationConcreteFamily t o m k (SourceSupportAt t o m)
      (SourceSupportData t o m k))
  piece_union := iUnion_historyPiece t o m k (SourceSupportAt t o m) event
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
        have href := sourceEventRefinement eta a candidate heligible.2 low
          heligible.1.good event (hinvariant eta) hprefix hm hk hwindow
          harithmetic hexternalArithmetic
        have hpiece := measurableSet_historyPiece t o m k
          (SourceSupportAt t o m) event hevent
          (orientedAllCreationConcreteFamily t o m k (SourceSupportAt t o m)
            (SourceSupportData t o m k)) (some eta)
        have hnear := measurableSet_sourceEventCandidateNear eta a low event hm
          hk hwindow harithmetic hexternalArithmetic candidate
        apply coordinate_ratio_of_coordinateMassSpec hpiece hnear
          (prop49CandidateRatioEnvelope_ne_top _ _ _)
        simpa only [sourceEventCandidateNear, heligible.1, heligible.2,
          dite_true] using
          (coordinateMassSpecOfAllCreation
            (withSelected (SourceFiber eta) (fun cap d ↦
              (SourceFiber eta).selected cap d ∧
                distinguishedEventSafe eta event cap d)) href)

theorem sourceEventTargetFamily_near_measurable
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (event : Set WalkPath)
    (hevent : MeasurableSet event)
    (hinvariant : ∀ eta : SourceSupportedIndex t o m k,
      SourceEventDistinguishedInvariant eta event)
    (hprefix : SourceEventPrefixInvariant m k event)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    ∀ h candidate, MeasurableSet
      ((sourceEventTargetFamily (t := t) (o := o) a low event hevent
        hinvariant hprefix hm hk hwindow harithmetic
          hexternalArithmetic).near h candidate) := by
  intro h candidate
  cases h with
  | none => exact MeasurableSet.empty
  | some eta =>
      exact measurableSet_sourceEventCandidateNear eta a low event hm hk
        hwindow harithmetic hexternalArithmetic candidate

/-- A source-good stopped path in `event` with a narrow selected endpoint is
covered by the distinguished-event target family. -/
theorem mem_sourceEventTargetFamily_of_path
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (event : Set WalkPath)
    (hevent : MeasurableSet event)
    (hinvariant : ∀ eta : SourceSupportedIndex t o m k,
      SourceEventDistinguishedInvariant eta event)
    (hprefix : SourceEventPrefixInvariant m k event)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    {s : WalkPath} (hvalid : s ∈ validStepWalk)
    (hreach : s ∈ thresholdReachStage m k) (hsevent : s ∈ event)
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
    s ∈ (sourceEventTargetFamily (t := t) (o := o) a low event hevent
      hinvariant hprefix hm hk hwindow harithmetic
      hexternalArithmetic).someCandidate := by
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
  have hcandidateEta : candidate ∈ eta.1.2 := hcandidate
  have hordinary : s ∈ sourceProp49CandidateNear eta a low candidate :=
    mem_sourceProp49CandidateNear_of_exactAtom eta a candidate hcandidateEta
      low hm hk hwindow harithmetic hexternalArithmetic hsAtom htheta hnarrow
  simp only [sourceProp49CandidateNear, hcandidateEta, dite_true] at hordinary
  have hnear : s ∈ sourceEventCandidateNear eta a low event hm hk hwindow
      harithmetic hexternalArithmetic candidate := by
    simp only [sourceEventCandidateNear, hsourceEligible, hcandidateEta,
      dite_true]
    rcases Set.mem_iUnion.mp hordinary with ⟨cap, hcap⟩
    apply Set.mem_iUnion.mpr
    refine ⟨cap, ?_⟩
    rw [sourceEventScreenedFiber_eq eta a candidate hcandidateEta low
      hsourceEligible.good event (hinvariant eta) hprefix hm hk hwindow
      harithmetic hexternalArithmetic cap,
      sourceThresholdScreenedFiber_eq_sourceProp49ScreenedFiber]
    exact ⟨hcap, hsevent⟩
  unfold StoppedHistoryCandidateFamily.someCandidate
  refine Set.mem_iUnion_of_mem (some eta) <|
    Set.mem_iUnion_of_mem candidate <| ?_
  have hcandidates : candidate ∈ filteredHistoryCandidates t o m k
      (SourceSupportAt t o m) SourceProp49EligibleHistory (some eta) :=
    (mem_filteredHistoryCandidates_some_iff t o m k
      (SourceSupportAt t o m) SourceProp49EligibleHistory eta candidate).2
        ⟨hsourceEligible, hcandidateEta⟩
  refine Set.mem_iUnion_of_mem hcandidates ?_
  exact ⟨⟨hsevent, hsAtom⟩, hnear⟩

/-- The unrestricted canonical family, with its history type made explicit
for comparison with distinguished-event families. -/
noncomputable def sourceUnrestrictedTargetFamily
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (a : GapScale) (low : ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    StoppedHistoryCandidateFamily
      (HLOZOrientedAllCreationStoppedCandidateFamily.History t o m k
        (SourceSupportAt t o m)) Point Set.univ (initialBudget48 m)
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a) :=
  sourceProp49StoppedHistoryCandidateFamily a low Set.univ
    MeasurableSet.univ (fun _ _ ↦ subset_univ _) hm hk hwindow harithmetic
      hexternalArithmetic

/-- Intersecting the unrestricted canonical candidate union with an
invariant event is covered by the corresponding distinguished-event family.
This form lets transport modules reuse an already established ambient-row
membership proof. -/
theorem sourceProp49StoppedHistoryCandidateFamily_univ_inter_event_subset
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (event : Set WalkPath)
    (hevent : MeasurableSet event)
    (hinvariant : ∀ eta : SourceSupportedIndex t o m k,
      SourceEventDistinguishedInvariant eta event)
    (hprefix : SourceEventPrefixInvariant m k event)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    (sourceUnrestrictedTargetFamily t o m k a low hm hk hwindow harithmetic
        hexternalArithmetic).someCandidate ∩ event ⊆
      (sourceEventTargetFamily (t := t) (o := o) a low event hevent
        hinvariant hprefix hm hk hwindow harithmetic
          hexternalArithmetic).someCandidate := by
  classical
  rintro s ⟨hs, hsevent⟩
  unfold StoppedHistoryCandidateFamily.someCandidate at hs ⊢
  rcases Set.mem_iUnion.mp hs with ⟨h, hs⟩
  rcases Set.mem_iUnion.mp hs with ⟨candidate, hs⟩
  rcases Set.mem_iUnion.mp hs with ⟨hcandidate, hpiece, hnear⟩
  cases h with
  | none =>
      change candidate ∈ (∅ : Finset Point) at hcandidate
      simp at hcandidate
  | some eta =>
      have heligible := (mem_filteredHistoryCandidates_some_iff t o m k
        (SourceSupportAt t o m) SourceProp49EligibleHistory eta candidate).mp
          hcandidate
      have hcandidateEta : candidate ∈ eta.1.2 := heligible.2
      have hordinary : s ∈ sourceProp49Near eta a candidate hcandidateEta
          low := by
        change s ∈ sourceProp49CandidateNear eta a low candidate at hnear
        simpa only [sourceProp49CandidateNear, hcandidateEta, dite_true] using
          hnear
      have heventNear : s ∈ sourceEventCandidateNear eta a low event hm hk
          hwindow harithmetic hexternalArithmetic candidate := by
        simp only [sourceEventCandidateNear, heligible.1, hcandidateEta,
          dite_true]
        rcases Set.mem_iUnion.mp hordinary with ⟨cap, hcap⟩
        apply Set.mem_iUnion.mpr
        refine ⟨cap, ?_⟩
        rw [sourceEventScreenedFiber_eq eta a candidate hcandidateEta low
          heligible.1.good event (hinvariant eta) hprefix hm hk hwindow
          harithmetic hexternalArithmetic cap,
          sourceThresholdScreenedFiber_eq_sourceProp49ScreenedFiber]
        exact ⟨hcap, hsevent⟩
      refine Set.mem_iUnion_of_mem (some eta) <|
        Set.mem_iUnion_of_mem candidate <|
          Set.mem_iUnion_of_mem hcandidate ?_
      change s ∈ historyPiece t o m k (SourceSupportAt t o m) event
          (some eta) ∩
        sourceEventCandidateNear eta a low event hm hk hwindow harithmetic
          hexternalArithmetic candidate
      refine ⟨?_, heventNear⟩
      change s ∈ historyPiece t o m k (SourceSupportAt t o m) Set.univ
          (some eta) at hpiece
      exact ⟨hsevent, hpiece.2⟩

theorem sourceEventTargetFamily_someCandidate_subset_unrestricted_inter_event
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (event : Set WalkPath)
    (hevent : MeasurableSet event)
    (hinvariant : ∀ eta : SourceSupportedIndex t o m k,
      SourceEventDistinguishedInvariant eta event)
    (hprefix : SourceEventPrefixInvariant m k event)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    (sourceEventTargetFamily (t := t) (o := o) a low event hevent
        hinvariant hprefix hm hk hwindow harithmetic
          hexternalArithmetic).someCandidate ⊆
      (sourceUnrestrictedTargetFamily t o m k a low hm hk hwindow harithmetic
        hexternalArithmetic).someCandidate ∩ event := by
  classical
  intro s hs
  unfold StoppedHistoryCandidateFamily.someCandidate at hs ⊢
  rcases Set.mem_iUnion.mp hs with ⟨h, hs⟩
  rcases Set.mem_iUnion.mp hs with ⟨candidate, hs⟩
  rcases Set.mem_iUnion.mp hs with ⟨hcandidate, hpiece, hnear⟩
  cases h with
  | none =>
      change candidate ∈ (∅ : Finset Point) at hcandidate
      simp at hcandidate
  | some eta =>
      have heligible := (mem_filteredHistoryCandidates_some_iff t o m k
        (SourceSupportAt t o m) SourceProp49EligibleHistory eta candidate).mp
          hcandidate
      have hcandidateEta : candidate ∈ eta.1.2 := heligible.2
      change s ∈ sourceEventCandidateNear eta a low event hm hk hwindow
        harithmetic hexternalArithmetic candidate at hnear
      simp only [sourceEventCandidateNear, heligible.1, hcandidateEta,
        dite_true] at hnear
      rcases Set.mem_iUnion.mp hnear with ⟨cap, hcap⟩
      rw [sourceEventScreenedFiber_eq eta a candidate hcandidateEta low
        heligible.1.good event (hinvariant eta) hprefix hm hk hwindow
        harithmetic hexternalArithmetic cap,
        sourceThresholdScreenedFiber_eq_sourceProp49ScreenedFiber] at hcap
      refine ⟨?_, hcap.2⟩
      refine Set.mem_iUnion_of_mem (some eta) <|
        Set.mem_iUnion_of_mem candidate <|
          Set.mem_iUnion_of_mem hcandidate ?_
      change s ∈ historyPiece t o m k (SourceSupportAt t o m) Set.univ
          (some eta) ∩ sourceProp49CandidateNear eta a low candidate
      refine ⟨⟨Set.mem_univ s, hpiece.2⟩, ?_⟩
      simp only [sourceProp49CandidateNear, hcandidateEta, dite_true]
      exact Set.mem_iUnion_of_mem cap hcap.1

theorem sourceEventTargetFamily_someCandidate_eq
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (event : Set WalkPath)
    (hevent : MeasurableSet event)
    (hinvariant : ∀ eta : SourceSupportedIndex t o m k,
      SourceEventDistinguishedInvariant eta event)
    (hprefix : SourceEventPrefixInvariant m k event)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    (sourceEventTargetFamily (t := t) (o := o) a low event hevent
        hinvariant hprefix hm hk hwindow harithmetic
          hexternalArithmetic).someCandidate =
      (sourceUnrestrictedTargetFamily t o m k a low hm hk hwindow harithmetic
        hexternalArithmetic).someCandidate ∩ event := by
  apply Set.Subset.antisymm
  · exact sourceEventTargetFamily_someCandidate_subset_unrestricted_inter_event
      a low event hevent hinvariant hprefix hm hk hwindow harithmetic
        hexternalArithmetic
  · exact sourceProp49StoppedHistoryCandidateFamily_univ_inter_event_subset
      a low event hevent hinvariant hprefix hm hk hwindow harithmetic
        hexternalArithmetic

end

end Erdos1165.HLOZSourceDistinguishedEventProp49Family
