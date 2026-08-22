/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPrefixedCanonicalSourceProp49Data
import ErdosProblems.Erdos1165.HLOZFilteredOrientedAllCreationStoppedCandidateFamily
import ErdosProblems.Erdos1165.HLOZNoLazyInitialBudgetMixedTransitionFactors

/-!
# The concrete canonical Proposition 4.9 stopped refinement

This file combines the prefix-correct recovery certificate and the literal
negative-binomial ratio.  The candidate event is the cofinal union of the
actual narrow stopped fibres.  Cap monotonicity is proved by embedding the
complete capped insertion vector without changing any natural coordinate.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZPrefixedCanonicalSourceProp49Refinement

open FiniteDominoProductLaw HLOZPathEvents
open HLOZFilteredOrientedAllCreationStoppedCandidateFamily
open HLOZMeshCandidatePolynomialNumerics
open HLOZMeshCandidateFutureFactor
open HLOZNoLazyInitialBudgetMixedTransitionFactors
open HLOZOrientedAllCreationStoppedCandidateFamily
open HLOZPrefixedAllCreationCanonicalRefinement
open HLOZPrefixedAllCreationCanonicalDominantWindows
open HLOZPrefixedCanonicalSourceAtomRecovery
open HLOZPrefixedCanonicalSourceLowRecovery
open HLOZPrefixedCanonicalSourceProp49Data
open HLOZPrefixedProp49CandidateWindowRatio
open HLOZProposition48Candidates HLOZShellZeroExternalWindow
open HLOZShellZeroReplacementWindows
open HLOZThetaSourceBalance
open LazyDecomposition
open TilingCappedMarginalization
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedSupportAwayCoordinates
open TilingOrientedShellZeroSourcePartition
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The actual reconstructed narrow predicate on one canonical source atom. -/
noncomputable def sourceProp49ScreenedPredicate
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low cap : ℕ)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      ((SourceFiber eta).coordinateCap cap)) : Prop :=
  (SourceFiber eta).atomPredicate cap q ∧
    TilingAwayTotalsScreen t ((SourceFiber eta).start cap)
      ((SourceFiber eta).retained cap) ((SourceFiber eta).distinguished cap)
      ((SourceFiber eta).upper cap)
      (fun ell ↦ ((sourceParameters (cap := cap) eta candidate hcandidate low
        (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)
        (prop49NarrowTotalWindow m a)).toSpec).acceptedScreenedAccepts ell =
          true)
      ((splitTilingCoordinatesEquiv t ((SourceFiber eta).start cap)
        ((SourceFiber eta).retained cap)
        ((SourceFiber eta).distinguished cap) q).2)

/-- The literal narrow stopped fibre at one logical cap. -/
def sourceProp49ScreenedFiber
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low cap : ℕ) : Set WalkPath :=
  walkLift (prefixedTilingPreStoppingFiberEvent
    ((SourceFiber eta).stoppingTime cap) ((SourceFiber eta).initial cap) t
    ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
    ((SourceFiber eta).coordinateCap cap) ((SourceFiber eta).tail cap)
    (sourceProp49ScreenedPredicate eta a candidate hcandidate low cap))

/-- The candidate event used by the stopped union bound. -/
def sourceProp49Near
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) : Set WalkPath :=
  ⋃ cap, sourceProp49ScreenedFiber eta a candidate hcandidate low cap

theorem measurableSet_sourceProp49ScreenedFiber
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low cap : ℕ) :
    MeasurableSet (sourceProp49ScreenedFiber eta a candidate hcandidate
      low cap) := by
  apply measurableSet_walkLift
  exact measurableSet_prefixedTilingPreStoppingFiberEvent
    ((SourceFiber eta).isStoppingTime cap) ((SourceFiber eta).initial cap) t
    ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
    ((SourceFiber eta).coordinateCap cap) ((SourceFiber eta).tail cap)
    (sourceProp49ScreenedPredicate eta a candidate hcandidate low cap)

theorem measurableSet_sourceProp49Near
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) :
    MeasurableSet (sourceProp49Near eta a candidate hcandidate low) := by
  exact MeasurableSet.iUnion fun cap ↦
    measurableSet_sourceProp49ScreenedFiber eta a candidate hcandidate low cap

private theorem sourceCoordinateCap_mono
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k) {cap cap' : ℕ}
    (hcap : cap ≤ cap') :
    (SourceFiber eta).coordinateCap cap ≤
      (SourceFiber eta).coordinateCap cap' := by
  change max eta.1.1.external.retainedCount (m + shellWidth48 m) + cap ≤
    max eta.1.1.external.retainedCount (m + shellWidth48 m) + cap'
  omega

private theorem sourceProp49ScreenedPredicate_cast
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) {cap cap' : ℕ} (hcap : cap ≤ cap')
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      ((SourceFiber eta).coordinateCap cap))
    (haccepted : PrefixedTilingStoppingAccepted
      ((SourceFiber eta).stoppingTime cap) ((SourceFiber eta).initial cap) t
      ((SourceFiber eta).start cap) ((SourceFiber eta).retained cap)
      (fun j ↦ (q j : ℕ)) ((SourceFiber eta).tail cap))
    (hscreen : sourceProp49ScreenedPredicate
      eta a candidate hcandidate low cap q) :
    sourceProp49ScreenedPredicate eta a candidate hcandidate low cap'
      (castAllCreationCappedCoordinates eta.1.1
        (sourceCoordinateCap_mono eta hcap) q) := by
  classical
  rcases hscreen with ⟨hpred, ell, hell, htotal⟩
  refine ⟨?_, ell, ?_, ?_⟩
  · exact orientedAllCreationStoppedAtomPredicate_cast
      o m k (SourceSupportAt t o m) eta.1.2 eta.1.1
      (sourceCoordinateCap_mono eta hcap) q hpred haccepted
  · exact hell
  · intro b
    simp only [OrientedAllCreationPrefixedStoppedCoordinateSpec.start,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.retained,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.distinguished] at htotal b ⊢
    calc
      _ = tilingDominoTotal t eta.1.1.external.start
          eta.1.1.external.retained
          (fun j ↦ (castAllCreationCappedCoordinates eta.1.1
            (sourceCoordinateCap_mono eta hcap) q j : ℕ)) b.1 :=
        tilingAwayTotal_split_eq_dominoTotal _ _ _ _ _ _
      _ = tilingDominoTotal t eta.1.1.external.start
          eta.1.1.external.retained (fun j ↦ (q j : ℕ)) b.1 := by
        simp only [coe_castAllCreationCappedCoordinates]
      _ = tilingAwayTotal t eta.1.1.external.start
          eta.1.1.external.retained
          (supportComplementDistinguished t eta.1.1.external.start
            eta.1.1.external.retained eta.1.2)
          ((splitTilingCoordinatesEquiv t eta.1.1.external.start
            eta.1.1.external.retained
            (supportComplementDistinguished t eta.1.1.external.start
              eta.1.1.external.retained eta.1.2) q).2) b :=
        (tilingAwayTotal_split_eq_dominoTotal _ _ _ _ _ _).symm
      _ = ell b := htotal b

/-- The physical prefix-correct narrow stopped fibres are cofinal in the
logical coordinate cap. -/
theorem monotone_sourceProp49ScreenedFiber
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k)
    (a : GapScale) (candidate : Point) (hcandidate : candidate ∈ eta.1.2)
    (low : ℕ) :
    Monotone fun cap ↦
      sourceProp49ScreenedFiber eta a candidate hcandidate low cap := by
  intro cap cap' hcap s hs
  rcases hs with ⟨hvalid, hevent⟩
  rcases Set.mem_iUnion.mp hevent with ⟨q, hq⟩
  let q' := castAllCreationCappedCoordinates eta.1.1
    (sourceCoordinateCap_mono eta hcap) q.1
  have haccepted' := prefixedStoppingAccepted_castAllCreation
    m k eta.1.1 (sourceCoordinateCap_mono eta hcap) q.1 q.2.2
  refine ⟨hvalid, Set.mem_iUnion.mpr ⟨⟨q', ?_, haccepted'⟩, ?_⟩⟩
  · exact sourceProp49ScreenedPredicate_cast eta a candidate hcandidate
      low hcap q.1 q.2.2 q.2.1
  · rw [prefixedTilingStoppedInsertionAtom_eq_cylinder
      ((SourceFiber eta).isStoppingTime cap')
      ((SourceFiber eta).initial cap') t ((SourceFiber eta).start cap')
      ((SourceFiber eta).retained cap') (fun j ↦ (q' j : ℕ))
      ((SourceFiber eta).tail cap') haccepted']
    rw [prefixedTilingStoppedInsertionAtom_eq_cylinder
      ((SourceFiber eta).isStoppingTime cap)
      ((SourceFiber eta).initial cap) t ((SourceFiber eta).start cap)
      ((SourceFiber eta).retained cap) (fun j ↦ (q.1 j : ℕ))
      ((SourceFiber eta).tail cap) q.2.2] at hq
    simpa only [OrientedAllCreationPrefixedStoppedCoordinateSpec.initial,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.start,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.retained,
      OrientedAllCreationPrefixedStoppedCoordinateSpec.tail, q',
      coe_castAllCreationCappedCoordinates] using hq

/-! ## The fixed-first-strip filtered candidate family -/

/-- Exact source eligibility on one stopped atom.  The first-strip cardinality
bound is kept together with a literal restricted-Theta-good representative;
neither property is inferred from the other. -/
structure SourceProp49EligibleHistory
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k) : Prop where
  card_le : eta.1.2.card ≤ initialBudget48 m
  exists_good : ∃ s,
    s ∈ orientedAllCreationSupportTraceAtom t o m k (SourceSupportAt t o m)
      eta.1.1 eta.1.2 ∧
    orientedTilingThetaBases t o m (shellWidth48 m)
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m) s
      (creationTimeNat m k s) = ∅

/-- Choose the literal good representative recorded propositionally by an
eligible atom.  Classical choice is used only to package deterministic
history data; no probability assertion is introduced. -/
noncomputable def SourceProp49EligibleHistory.good
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {eta : SourceSupportedIndex t o m k}
    (h : SourceProp49EligibleHistory eta) :
    SourceThetaGoodRepresentative eta
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m) where
  path := Classical.choose h.exists_good
  mem_atom := (Classical.choose_spec h.exists_good).1
  theta_good := (Classical.choose_spec h.exists_good).2

/-- The actual narrow candidate event on an eligible source support.  Outside
the support it is empty, so it extends to the total candidate-family API. -/
noncomputable def sourceProp49CandidateNear
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k) (a : GapScale) (low : ℕ)
    (candidate : Point) : Set WalkPath := by
  classical
  exact if hcandidate : candidate ∈ eta.1.2 then
    sourceProp49Near eta a candidate hcandidate low else ∅

theorem measurableSet_sourceProp49CandidateNear
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SourceSupportedIndex t o m k) (a : GapScale) (low : ℕ)
    (candidate : Point) :
    MeasurableSet (sourceProp49CandidateNear eta a low candidate) := by
  classical
  simp only [sourceProp49CandidateNear]
  split
  · exact measurableSet_sourceProp49Near eta a candidate _ low
  · exact MeasurableSet.empty

set_option linter.unusedVariables false in
private theorem zero_not_mem_sourceWindow
    {m : ℕ} (hm : 1 < m) :
    0 ∉ shellZeroSourceTotalWindow m (shellWidth48 m) := by
  simp only [mem_shellZeroSourceTotalWindow]
  omega

/-- Canonical prefix-correct Proposition 4.9 coordinate data on all eligible
source atoms.  The only past-history premise is the exact stopped-atom
inclusion needed for conditionalization; there is no probability or
transition inequality premise. -/
noncomputable def sourceProp49FilteredCoordinateData
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (previous : Set WalkPath)
    (hprevious : MeasurableSet previous)
    (hatom_previous : ∀ eta : SourceSupportedIndex t o m k,
      SourceProp49EligibleHistory eta →
      orientedAllCreationSupportTraceAtom t o m k (SourceSupportAt t o m)
        eta.1.1 eta.1.2 ⊆ previous)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    FilteredOrientedAllCreationLowCoordinateData t o m k
      (initialBudget48 m) previous
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a) where
  supportAt := SourceSupportAt t o m
  supportData := SourceSupportData t o m k
  previous_measurable := hprevious
  ratio_ne_top := prop49CandidateRatioEnvelope_ne_top _ _ _
  eligible := SourceProp49EligibleHistory
  eligible_card := fun eta heligible ↦ heligible.card_le
  near := fun eta candidate ↦ sourceProp49CandidateNear eta a low candidate
  near_measurable := fun eta candidate ↦
    measurableSet_sourceProp49CandidateNear eta a low candidate
  refinement := by
    intro eta candidate heligible hcandidate
    let cert := sourceRecoveryCertificate eta candidate hcandidate low
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)
      (prop49NarrowTotalWindow m a) hm hk
      (zero_not_mem_sourceWindow hm)
    apply cert.refinement
    · intro s hs
      exact ⟨hatom_previous eta heligible hs, hs⟩
    · intro cap
      exact heligible.good.acceptedRatioData a candidate hcandidate low hm hk
        hwindow harithmetic hexternalArithmetic cap
    · exact monotone_sourceProp49ScreenedFiber eta a candidate hcandidate low
    · intro s hs
      have hnear : s ∈ sourceProp49Near eta a candidate hcandidate low := by
        simpa only [sourceProp49CandidateNear, hcandidate, ↓reduceDIte] using
          hs.2.2
      exact hnear

/-- The checked stopped-history candidate family with the literal
`initialBudget48` budget and the polynomial Proposition 4.9 ratio. -/
noncomputable def sourceProp49StoppedHistoryCandidateFamily
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (previous : Set WalkPath)
    (hprevious : MeasurableSet previous)
    (hatom_previous : ∀ eta : SourceSupportedIndex t o m k,
      SourceProp49EligibleHistory eta →
      orientedAllCreationSupportTraceAtom t o m k (SourceSupportAt t o m)
        eta.1.1 eta.1.2 ⊆ previous)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :=
  (sourceProp49FilteredCoordinateData a low previous hprevious
    hatom_previous hm hk hwindow harithmetic hexternalArithmetic).family

/-- Literal containment criterion for the filtered next transition.  It asks
for exactly the source-good stopped atom, the selected first-strip point, and
membership in the prefix-correct narrow fibre; no event estimate appears. -/
theorem sourceProp49Next_subset_someCandidate
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (previous next : Set WalkPath)
    (hprevious : MeasurableSet previous)
    (hatom_previous : ∀ eta : SourceSupportedIndex t o m k,
      SourceProp49EligibleHistory eta →
      orientedAllCreationSupportTraceAtom t o m k (SourceSupportAt t o m)
        eta.1.1 eta.1.2 ⊆ previous)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (hnext : ∀ s ∈ next,
      ∃ (eta : SourceSupportedIndex t o m k) (candidate : Point),
        s ∈ historyPiece t o m k (SourceSupportAt t o m) previous (some eta) ∧
        SourceProp49EligibleHistory eta ∧ candidate ∈ eta.1.2 ∧
        s ∈ sourceProp49CandidateNear eta a low candidate) :
    next ⊆ (sourceProp49StoppedHistoryCandidateFamily a low previous
      hprevious hatom_previous hm hk hwindow harithmetic
      hexternalArithmetic).someCandidate := by
  exact (sourceProp49FilteredCoordinateData a low previous hprevious
    hatom_previous hm hk hwindow harithmetic
    hexternalArithmetic).next_subset_someCandidate hnext

/-- Final canonical low-coordinate package in the exact shape consumed by
the no-lazy mixed selector.  The countable mesh-creation input is deliberately
the separate strong-Markov layer; all conditional product and numerical-ratio
fields are constructed here. -/
noncomputable def sourceProp49FirstStripMeshLowCoordinateData
    {Index : Type} [Countable Index]
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (a : GapScale) (low : ℕ) (previous next : Set WalkPath)
    (hprevious : MeasurableSet previous)
    (hatom_previous : ∀ eta : SourceSupportedIndex t o m k,
      SourceProp49EligibleHistory eta →
      orientedAllCreationSupportTraceAtom t o m k (SourceSupportAt t o m)
        eta.1.1 eta.1.2 ⊆ previous)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (creation : CountableMeshCreationData Index
      (sourceProp49StoppedHistoryCandidateFamily a low previous
        hprevious hatom_previous hm hk hwindow harithmetic
        hexternalArithmetic).someCandidate next m k a) :
    FirstStripMeshLowCoordinateData prop49WindowRatioConstant m k a
      previous next where
  History := History t o m k (SourceSupportAt t o m)
  Candidate := Point
  Index := Index
  candidateRatio := prop49CandidateRatioEnvelope
    prop49WindowRatioConstant m a
  candidate := sourceProp49StoppedHistoryCandidateFamily a low previous
    hprevious hatom_previous hm hk hwindow harithmetic hexternalArithmetic
  creation := creation
  ratio_le := le_rfl

end

end Erdos1165.HLOZPrefixedCanonicalSourceProp49Refinement
