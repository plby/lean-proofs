/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1166.Erdos1166HLOZPrimedInverseClockProfile
import ErdosProblems.Erdos1166.Erdos1166HLOZExternalGreen
import ErdosProblems.Erdos1166.Erdos1166HLOZProp13FromAppendix
import ErdosProblems.Erdos1166.Erdos1166HLOZProp44ExternalChain
import ErdosProblems.Erdos1166.Erdos1166HLOZNearCriticalBridge

/-!
# The separate primed `X₁` atomization in HLOZ Proposition 4.5

The primed deletion pairs increments starting at original time one.  After
shifting by one and swapping the two entries of every adjacent pair, this is
the ordinary unprimed terminal-label decoder.  The iid restart and swap law
is already proved in `HLOZProp42InverseLaw`; here it is transferred to the
canonical path space and assembled into the two primed Proposition-4.5
branches.  No unprimed external-path atom occurs in the conditioning event.
-/

namespace Erdos1166.HLOZProp47Prop45XEastPrimed

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

open HLOZFoundation HLOZDecomposition HLOZUrn
open HLOZProp44
open HLOZProp47Parameters HLOZProp47SourceObjects
open HLOZProp45SourceClock HLOZProp45SourceInterval
open HLOZProp45SourceMirrors HLOZProp45SourceEndpoints
open HLOZProp45SourceAbsorption HLOZProp47Canonical
open HLOZSourceInstantiation HLOZProp42InverseLaw HLOZPrimedStopped
open HLOZProp47Prop45Connector HLOZProp47Prop45XEast
open HLOZProp47SourceAssembly HLOZPairing.ScreeningBridge
open HLOZReconstruction HLOZActualStopped

abbrev Path := ℕ → Site

private theorem measurableSet_firstDirection_iidHistory
    (first : Direction) :
    MeasurableSet[iidHistory (X := Direction) 1]
      {ω : ℕ → Direction | ω 0 = first} := by
  let _ : MeasurableSpace (ℕ → Direction) :=
    iidHistory (X := Direction) 1
  apply measurableSet_eq_fun _ measurable_const
  apply measurable_iff_comap_le.mpr
  exact le_iSup_of_le 0 (le_iSup_of_le (by omega) le_rfl)

noncomputable def primedIncrementExternalPathAtom {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair) :
    Set (ℕ → Direction) :=
  {ω | ω 0 = first} ∩
    swappedIncrementShiftAfter primedOneShift ⁻¹'
      firstPairExternalPathEqFrom 0
        (externalPathFromLabels (List.ofFn labels))

def primedExternalPathWalkAtom {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair) : Set Path :=
  simpleRandomWalk '' primedIncrementExternalPathAtom first labels

theorem measurable_primedOneShift : Measurable primedOneShift :=
  measurable_const

theorem measurableSet_primedIncrementExternalPathAtom {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair) :
    MeasurableSet (primedIncrementExternalPathAtom first labels) := by
  apply MeasurableSet.inter
  · exact ProbabilityTheory.iidHistory_le 1 _
      (measurableSet_firstDirection_iidHistory first)
  · exact (measurableSet_externalPathAtom 0 _).preimage
      (measurable_swappedIncrementShiftAfter measurable_primedOneShift)

theorem measurableSet_primedExternalPathWalkAtom {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair) :
    MeasurableSet (primedExternalPathWalkAtom first labels) := by
  exact measurableEmbedding_simpleRandomWalk.measurableSet_image.2
    (measurableSet_primedIncrementExternalPathAtom first labels)

theorem preimage_primedExternalPathWalkAtom {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair) :
    simpleRandomWalk ⁻¹' primedExternalPathWalkAtom first labels =
      primedIncrementExternalPathAtom first labels := by
  exact simpleRandomWalk_injective.preimage_image _

noncomputable def primedConditionalDecodedHoldingPrefix
    {q cut : ℕ} (first : Direction) (labels : Fin q → IncrementPair)
    (x : Site)
    (hcut : cut ≤
      (chronologicalExternalIndexList labels (primedRelativeSite first x)).length)
    (s : Path) : ℕ :=
  Function.extend simpleRandomWalk
    (fun ω ↦ decodedChronologicalHoldingPrefix labels
      (primedRelativeSite first x) hcut
      (listVectorToFin labels
        (conditionalPairRunVector 0 (List.ofFn labels)
          (swappedIncrementShiftAfter primedOneShift ω)))) 0 s

theorem measurable_primedConditionalDecodedHoldingPrefix
    {q cut : ℕ} (first : Direction) (labels : Fin q → IncrementPair)
    (hnondistinguished : ∀ i, labels i ≠ distinguishedIncrementPair)
    (x : Site)
    (hcut : cut ≤
      (chronologicalExternalIndexList labels (primedRelativeSite first x)).length) :
    Measurable (primedConditionalDecodedHoldingPrefix first labels x hcut) := by
  apply measurableEmbedding_simpleRandomWalk.measurable_extend
  · exact (measurable_conditionalDecodedChronologicalHoldingPrefix
      labels hnondistinguished (primedRelativeSite first x) hcut).comp
        (measurable_swappedIncrementShiftAfter measurable_primedOneShift)
  · exact measurable_const

theorem primedConditionalDecodedHoldingPrefix_simpleRandomWalk
    {q cut : ℕ} (first : Direction) (labels : Fin q → IncrementPair)
    (x : Site)
    (hcut : cut ≤
      (chronologicalExternalIndexList labels (primedRelativeSite first x)).length)
    (ω : ℕ → Direction) :
    primedConditionalDecodedHoldingPrefix first labels x hcut
        (simpleRandomWalk ω) =
      decodedChronologicalHoldingPrefix labels (primedRelativeSite first x) hcut
        (listVectorToFin labels
          (conditionalPairRunVector 0 (List.ofFn labels)
            (swappedIncrementShiftAfter primedOneShift ω))) := by
  unfold primedConditionalDecodedHoldingPrefix
  exact simpleRandomWalk_injective.extend_apply _ _ ω

private theorem primedFirstDirection_pastFiber (first : Direction) (n : ℕ) :
    MeasurableSet[iidHistory (X := Direction) n]
      ({ω | ω 0 = first} ∩ {ω | primedOneShift ω = n}) := by
  by_cases hn : n = 1
  · subst n
    simpa only [primedOneShift, Set.setOf_true, Set.inter_univ] using
      measurableSet_firstDirection_iidHistory first
  · have hempty : Set.univ ∩ {ω : ℕ → Direction |
        primedOneShift ω = n} = ∅ := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_univ, true_and,
        Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      simp only [primedOneShift]
      omega
    have hsub : {ω : ℕ → Direction | ω 0 = first} ∩
        {ω | primedOneShift ω = n} = ∅ := by
      rw [← Set.inter_univ {ω : ℕ → Direction | ω 0 = first},
        Set.inter_assoc, hempty, Set.inter_empty]
    rw [hsub]
    exact @MeasurableSet.empty (ℕ → Direction)
      (iidHistory (X := Direction) n)

/-- Path-space Proposition 4.2 for the one-step-shifted primed external
path.  The proof uses the actual shift-and-swap conditional law, rather than
postulating a primed negative-binomial distribution. -/
theorem primedConditionalDecodedHoldingPrefix_hasLaw
    {q cut : ℕ} (first : Direction) (labels : Fin q → IncrementPair)
    (hnondistinguished : ∀ i, labels i ≠ distinguishedIncrementPair)
    (x : Site)
    (hcut : cut ≤
      (chronologicalExternalIndexList labels (primedRelativeSite first x)).length) :
    HasLaw (primedConditionalDecodedHoldingPrefix first labels x hcut)
      (negBinMeasure cut)
      simpleRandomWalkLaw[|primedExternalPathWalkAtom first labels] := by
  let A : Set (ℕ → Direction) := {ω | ω 0 = first}
  let E := firstPairExternalPathEqFrom 0
    (externalPathFromLabels (List.ofFn labels))
  have hApos : incrementLaw A ≠ 0 := by
    change incrementLaw {ω | ω 0 = first} ≠ 0
    rw [increment_direction_prob]
    norm_num
  have hY := swappedIncrementShiftAfter_hasLaw_cond primedOneShift A
    measurable_primedOneShift (primedFirstDirection_pastFiber first) hApos
  have hYm : Measurable (swappedIncrementShiftAfter primedOneShift) :=
    measurable_swappedIncrementShiftAfter measurable_primedOneShift
  have hE : MeasurableSet E := measurableSet_externalPathAtom 0 _
  have hYcond := Erdos1166.HasLaw.cond_preimage hY hYm E hE
  have hdecoder := conditional_decodedChronologicalHoldingPrefix_hasLaw
    labels hnondistinguished (primedRelativeSite first x) hcut
  have hinc := hdecoder.fun_comp hYcond
  have hAmeas : MeasurableSet A :=
    measurableSet_pastEvent primedOneShift A
      (primedFirstDirection_pastFiber first)
  rw [cond_cond_eq_cond_inter hAmeas (hE.preimage hYm)] at hinc
  rw [simpleRandomWalkLaw]
  apply HasLaw.cond_map_image measurableEmbedding_simpleRandomWalk
    (measurableSet_primedIncrementExternalPathAtom first labels)
  · exact (measurable_conditionalDecodedChronologicalHoldingPrefix
      labels hnondistinguished (primedRelativeSite first x) hcut).comp
        (measurable_swappedIncrementShiftAfter measurable_primedOneShift)
  · intro ω _
    exact primedConditionalDecodedHoldingPrefix_simpleRandomWalk
      first labels x hcut ω
  · change HasLaw
      (fun ω ↦ decodedChronologicalHoldingPrefix labels
        (primedRelativeSite first x) hcut
        (listVectorToFin labels
          (conditionalPairRunVector 0 (List.ofFn labels)
            (swappedIncrementShiftAfter primedOneShift ω))))
      (negBinMeasure cut)
      incrementLaw[|primedIncrementExternalPathAtom first labels]
    simpa only [primedIncrementExternalPathAtom, A, E] using hinc

/-- The two primed branches of the paper's `X₁` stopped event. -/
noncomputable def xEastPrimedThetaEvent (m k : ℕ) : Set Path :=
  {s | (stoppedThetaHalfSites paperPrimedProfile
        (fun x ↦ ¬ HLOZPairing.chessEven x) false 10 s m k ∪
      stoppedThetaHalfSites paperPrimedProfile
        (fun x ↦ ¬ HLOZPairing.chessEven x) true 10 s m k).Nonempty}

/-- Pairing-independent threshold enlargement of the primed source event.
As on the unprimed side, every `prefixPairingEvent` has this threshold
conjunct, while its tiling-specific `PairFree` condition is discarded. -/
noncomputable def xEastPrimedSourceEvent (m k : ℕ) : Set Path :=
  hlozThresholdTimeEventK m (k + 1) ∩
    xEastPrimedThetaEvent m k

/-- Source-faithful primed lower branch, retaining the strict upper local-time
bound that excludes the level-`m` creation endpoint. -/
def primedIntervalStoppedThetaMinusCappedAt
    {m k : ℕ} (clock : PrimedShiftedDeletionClock m k)
    (a : ℕ) (x : Site) : Set Path :=
  primedIntervalStoppedThetaMinusAt clock a x ∩
    {s | localTime s (favoriteCreationHorizon m k s) x < m}

def primedIntervalStoppedThetaMinusCappedEvent
    {m k : ℕ} (clock : PrimedShiftedDeletionClock m k)
    (sites : Finset Site) (a : ℕ) : Set Path :=
  ⋃ x ∈ sites, primedIntervalStoppedThetaMinusCappedAt clock a x

noncomputable def xEastPrimedEncodedProfile {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair) : Site → ℕ :=
  fun x ↦ (chronologicalExternalIndexList labels
    (primedRelativeSite first x)).length

theorem primedInverseClockHoldingPrefix_mono_cut
    (s : Path) (q xCut yCut : ℕ) (x : Site) (hxy : xCut ≤ yCut) :
    primedInverseClockHoldingPrefix s q xCut x ≤
      primedInverseClockHoldingPrefix s q yCut x := by
  unfold primedInverseClockHoldingPrefix
  simpa only [List.map_take] using
    sum_take_mono_nat ((primedExternalVisitIndexList s q x).map
      (primedHoldingNat s)) hxy

/-- Once the deterministic external prefix contains every site visited by
the stopping horizon, membership in the unprimed half of the source
`Theta` event already gives one of the two natural endpoint events.  Thus
the endpoint split itself is not an atomization premise. -/
theorem xEastUnprimedThetaEvent_subset_intervalBranches
    (m k : ℕ) (sites : Finset Site) (hm : 2 ≤ m) (hk : 1 ≤ k)
    {s : Path}
    (hsites : visitedSites s (directCreationTime m k s) ⊆ sites)
    (htheta : s ∈ xEastUnprimedThetaEvent m k) :
    s ∈ intervalStoppedThetaMinusEvent sites m (sourceBandLowerNat m) k ∪
      intervalStoppedThetaPlusEvent sites m m k := by
  classical
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  change (stoppedThetaHalfSites paperUnprimedProfile
      HLOZPairing.chessEven false 10 s m (j + 1) ∪
    stoppedThetaHalfSites paperUnprimedProfile
      HLOZPairing.chessEven true 10 s m (j + 1)).Nonempty at htheta
  rcases htheta with ⟨x, hx⟩
  rcases Finset.mem_union.mp hx with hx | hx
  · left
    apply Set.mem_iUnion_of_mem x
    apply Set.mem_iUnion_of_mem
      (hsites (Finset.mem_filter.mp hx).1)
    exact mem_intervalStoppedThetaMinusAt_of_mem_stoppedThetaHalfSites
      HLOZPairing.chessEven s m j hm x (by
        simpa only [paperUnprimedProfile] using hx)
  · right
    apply Set.mem_iUnion_of_mem x
    apply Set.mem_iUnion_of_mem
      (hsites (Finset.mem_filter.mp hx).1)
    exact mem_intervalStoppedThetaPlusAt_of_mem_stoppedThetaHalfSites
      HLOZPairing.chessEven s m j hm x (by
        simpa only [paperUnprimedProfile] using hx)

/-- Primed analogue of
`xEastUnprimedThetaEvent_subset_intervalBranches`.  The stopped profile is
the concrete one-step-shifted deletion profile, so after identifying the
two stopping horizons the same source endpoint arithmetic applies. -/
theorem xEastPrimedThetaEvent_subset_intervalBranches
    (m k q : ℕ) (sites : Finset Site) (hm : 2 ≤ m) (hk : 1 ≤ k)
    {s : Path}
    (hsites : visitedSites s (directCreationTime m k s) ⊆ sites)
    (htheta : s ∈ xEastPrimedThetaEvent m k) :
    s ∈ primedIntervalStoppedThetaMinusEvent
        (concretePrimedShiftedDeletionClock m k q) sites
          (sourceBandLowerNat m) ∪
      primedIntervalStoppedThetaPlusEvent
        (concretePrimedShiftedDeletionClock m k q) sites m := by
  classical
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  change (stoppedThetaHalfSites paperPrimedProfile
      (fun x ↦ ¬ HLOZPairing.chessEven x) false 10 s m (j + 1) ∪
    stoppedThetaHalfSites paperPrimedProfile
      (fun x ↦ ¬ HLOZPairing.chessEven x) true 10 s m (j + 1)).Nonempty at htheta
  rcases htheta with ⟨x, hx⟩
  rcases Finset.mem_union.mp hx with hx | hx
  · left
    simp only [stoppedThetaHalfSites, Finset.mem_filter, Bool.false_eq_true,
      ↓reduceIte] at hx
    rcases hx with ⟨hxVisited, _hxFinite, _hxParity, hxLower, _hxUpper,
      hxExternal⟩
    apply Set.mem_iUnion_of_mem x
    apply Set.mem_iUnion_of_mem (hsites hxVisited)
    change primedExternalLocalTime s
        (favoriteCreationHorizon m (j + 1) s) x ≤
          intervalLowCut m (sourceBandLowerNat m) ∧
      sourceBandLowerNat m ≤
        localTime s (favoriteCreationHorizon m (j + 1) s) x
    rw [favoriteCreationHorizon_eq_directCreationTime s m j hm]
    refine ⟨le_intervalLowCut_of_le_sourceBandThreshold m _ ?_, ?_⟩
    · simpa only [paperPrimedProfile, Nat.cast_ofNat, one_mul] using hxExternal
    · exact (sourceBandLowerNat_le_iff m _).mpr hxLower
  · right
    simp only [stoppedThetaHalfSites, Finset.mem_filter, ↓reduceIte] at hx
    rcases hx with ⟨hxVisited, _hxFinite, _hxParity, _hxLower, hxUpper,
      hxExternal⟩
    apply Set.mem_iUnion_of_mem x
    apply Set.mem_iUnion_of_mem (hsites hxVisited)
    change intervalHighCut m m ≤
        primedExternalLocalTime s
          (favoriteCreationHorizon m (j + 1) s) x ∧
      localTime s (favoriteCreationHorizon m (j + 1) s) x < m
    rw [favoriteCreationHorizon_eq_directCreationTime s m j hm]
    refine ⟨intervalHighCut_top_le_of_sourceBandThreshold m _ ?_, ?_⟩
    · simpa only [paperPrimedProfile, Nat.cast_ofNat, one_mul] using hxExternal
    · exact_mod_cast hxUpper

/-- Fixed shifted external-path data for the primed half.  The inverse-clock
profile and holding-prefix identities are now derived from the exact
shift-and-swap transport, rather than supplied by the caller. -/
structure XEastPrimedExternalAtomInputs
    (m k q : ℕ) (first : Direction) (labels : Fin q → IncrementPair)
    (H : Set Path) where
  nondistinguished : ∀ i, labels i ≠ distinguishedIncrementPair
  positiveLength : 0 < q
  sites : Finset Site
  sitesOdd : ∀ x ∈ sites, ¬ HLOZPairing.chessEven x
  minus_capacity : ∀ x ∈ sites,
    intervalDotIndex m (sourceBandLowerNat m)
        (xEastPrimedEncodedProfile first labels) x ≤
      (chronologicalExternalIndexList labels
        (primedRelativeSite first x)).length
  plus_capacity : ∀ x ∈ intervalPlusCandidates sites m m
      (xEastPrimedEncodedProfile first labels),
    intervalHighCut m m ≤
      (chronologicalExternalIndexList labels
        (primedRelativeSite first x)).length
  theta_subset :
    primedExternalPathWalkAtom first labels ∩ H ∩
        xEastPrimedSourceEvent m k ⊆
      primedExternalPathWalkAtom first labels ∩ H ∩
        xEastPrimedSourceEvent m k ∩
          (primedIntervalStoppedThetaMinusCappedEvent
              (concretePrimedShiftedDeletionClock m k (2 * q - 1))
              sites (sourceBandLowerNat m) ∪
            primedIntervalStoppedThetaPlusEvent
              (concretePrimedShiftedDeletionClock m k (2 * q - 1)) sites m)
  minus_compatible : ∀ {s x},
    s ∈ primedExternalPathWalkAtom first labels ∩ H ∩
        xEastPrimedSourceEvent m k →
    x ∈ sites →
    s ∈ primedIntervalStoppedThetaMinusCappedAt
        (concretePrimedShiftedDeletionClock m k (2 * q - 1))
          (sourceBandLowerNat m) x →
      let clock := concretePrimedShiftedDeletionClock m k (2 * q - 1)
      clock.stoppedExternal s x ≤ clock.inverseProfile s x ∧
        clock.stoppedLazy s x ≤ clock.inverseHoldingPrefix s
          (intervalDotIndex m (sourceBandLowerNat m)
            (xEastPrimedEncodedProfile first labels) x) x
  plus_compatible : ∀ {s x},
    s ∈ primedExternalPathWalkAtom first labels ∩ H ∩
        xEastPrimedSourceEvent m k →
    x ∈ sites →
    s ∈ primedIntervalStoppedThetaPlusAt
        (concretePrimedShiftedDeletionClock m k (2 * q - 1)) m x →
      let clock := concretePrimedShiftedDeletionClock m k (2 * q - 1)
      clock.stoppedExternal s x ≤ clock.inverseProfile s x ∧
        clock.inverseHoldingPrefix s (intervalPriorHighCut m m) x ≤
          clock.stoppedLazy s x
  prop44_card : ((sourceProp44Candidates sites m
    (xEastPrimedEncodedProfile first labels)).card : ℝ) ≤
    Real.exp (16 * sourceRate m)
  horizon_card : (sites.card : ℝ) ≤
    Real.exp (16 * Real.sqrt (m : ℝ))

theorem XEastPrimedExternalAtomInputs.profile_atom
    {m k q : ℕ} {first : Direction} {labels : Fin q → IncrementPair}
    {H : Set Path}
    (h : XEastPrimedExternalAtomInputs m k q first labels H) :
    primedExternalPathWalkAtom first labels ⊆
      primedInverseProfileAtom
        (concretePrimedShiftedDeletionClock m k (2 * q - 1))
        h.sites (xEastPrimedEncodedProfile first labels) := by
  rintro s ⟨omega, homega, rfl⟩ x hx
  obtain ⟨N, hlabels⟩ := realized_terminalPairLabelsThrough
    labels h.nondistinguished homega.2
  have hfirst : omega 0 = first := homega.1
  have hprofile := primedInverseClockProfile_eq_chronological_length
    labels hlabels x (h.sitesOdd x hx) h.positiveLength
  rw [hfirst] at hprofile
  exact hprofile

theorem XEastPrimedExternalAtomInputs.holdingPrefix_hasLaw
    {m k q : ℕ} {first : Direction} {labels : Fin q → IncrementPair}
    {H : Set Path}
    (h : XEastPrimedExternalAtomInputs m k q first labels H)
    (x : Site) (hx : ¬ HLOZPairing.chessEven x) (cut : ℕ)
    (hcut : cut ≤
      (chronologicalExternalIndexList labels (primedRelativeSite first x)).length) :
    HasLaw (fun s ↦ primedInverseClockHoldingPrefix
      s (2 * q - 1) cut x) (negBinMeasure cut)
      simpleRandomWalkLaw[|primedExternalPathWalkAtom first labels] := by
  apply (primedConditionalDecodedHoldingPrefix_hasLaw
    first labels h.nondistinguished x hcut).congr
  filter_upwards [ae_cond_mem
    (measurableSet_primedExternalPathWalkAtom first labels)] with s hs
  rcases hs with ⟨omega, homega, rfl⟩
  rw [primedConditionalDecodedHoldingPrefix_simpleRandomWalk]
  have hfirst : omega 0 = first := homega.1
  have hcut' : cut ≤ (chronologicalExternalIndexList labels
      (primedRelativeSite (omega 0) x)).length := by
    simpa only [hfirst] using hcut
  have hprefix := primedInverseClockHoldingPrefix_eq_decodedChronological
    labels h.nondistinguished homega.2 x hx h.positiveLength hcut'
  simpa only [hfirst] using hprefix

private theorem XEastPrimedExternalAtomInputs.minus_law
    {m k q : ℕ} {first : Direction} {labels : Fin q → IncrementPair}
    {H : Set Path}
    (h : XEastPrimedExternalAtomInputs m k q first labels H)
    (x : Site) (hx : x ∈ h.sites) :
    HasLaw (fun s ↦ primedInverseClockHoldingPrefix s (2 * q - 1)
      (intervalDotIndex m (sourceBandLowerNat m)
        (xEastPrimedEncodedProfile first labels) x) x)
      (negBinMeasure
        (intervalDotIndex m (sourceBandLowerNat m)
          (xEastPrimedEncodedProfile first labels) x))
      simpleRandomWalkLaw[|primedExternalPathWalkAtom first labels] :=
  h.holdingPrefix_hasLaw x (h.sitesOdd x hx) _ (h.minus_capacity x hx)

private theorem XEastPrimedExternalAtomInputs.plus_law
    {m k q : ℕ} {first : Direction} {labels : Fin q → IncrementPair}
    {H : Set Path}
    (h : XEastPrimedExternalAtomInputs m k q first labels H)
    (x : Site) (hx : x ∈ intervalPlusCandidates h.sites m m
      (xEastPrimedEncodedProfile first labels)) :
    HasLaw (fun s ↦ primedInverseClockHoldingPrefix s (2 * q - 1)
      (intervalPriorHighCut m m) x)
      (negBinMeasure (intervalPriorHighCut m m))
      simpleRandomWalkLaw[|primedExternalPathWalkAtom first labels] :=
  h.holdingPrefix_hasLaw x
    (h.sitesOdd x (Finset.mem_filter.mp hx).1) _
      ((Nat.sub_le (intervalHighCut m m) 1).trans (h.plus_capacity x hx))

theorem XEastPrimedExternalAtomInputs.conditional_theta_le
    {m k q : ℕ} {first : Direction} {labels : Fin q → IncrementPair}
    {H : Set Path}
    (hs : SourceIntervalScale m (sourceBandLowerNat m) ∧
      SourceUpperScale m m)
    (h : XEastPrimedExternalAtomInputs m k q first labels H) :
    simpleRandomWalkLaw[|primedExternalPathWalkAtom first labels]
        (primedExternalPathWalkAtom first labels ∩ H ∩
          xEastPrimedSourceEvent m k) ≤ sourceProp45OneSideError m := by
  let C := primedExternalPathWalkAtom first labels
  let clock := concretePrimedShiftedDeletionClock m k (2 * q - 1)
  let minusEvent := primedIntervalStoppedThetaMinusCappedEvent clock h.sites
    (sourceBandLowerNat m)
  let plusEvent := primedIntervalStoppedThetaPlusEvent clock h.sites m
  have hminusSubset : (C ∩ H ∩ xEastPrimedSourceEvent m k) ∩
      minusEvent ⊆
      primedIntervalCanonicalDotThetaMinusEvent clock h.sites
        (sourceBandLowerNat m) (xEastPrimedEncodedProfile first labels) := by
    intro s hs'
    have hsTheta := hs'.2
    simp only [minusEvent, primedIntervalStoppedThetaMinusCappedEvent,
      Set.mem_iUnion] at hsTheta
    rcases hsTheta with ⟨x, hxsite, hxTheta⟩
    rw [primedIntervalCanonicalDotThetaMinusEvent, intervalDotThetaEvent]
    simp only [Set.mem_iUnion]
    refine ⟨x, hxsite, ?_⟩
    change sourceBandLowerNat m ≤
      intervalDotIndex m (sourceBandLowerNat m)
          (xEastPrimedEncodedProfile first labels) x +
        clock.inverseHoldingPrefix s
          (intervalDotIndex m (sourceBandLowerNat m)
            (xEastPrimedEncodedProfile first labels) x) x
    have hprofile : clock.inverseProfile s x =
        xEastPrimedEncodedProfile first labels x :=
      h.profile_atom hs'.1.1.1 x hxsite
    have hcompat := h.minus_compatible hs'.1 hxsite hxTheta
    have hcompatProfile : clock.stoppedExternal s x ≤
        clock.inverseProfile s x := by
      simpa only [clock] using hcompat.1
    have hext : clock.stoppedExternal s x ≤
      intervalDotIndex m (sourceBandLowerNat m)
        (xEastPrimedEncodedProfile first labels) x := by
      rw [intervalDotIndex]
      apply le_min
      · exact hcompatProfile.trans_eq hprofile
      · exact hxTheta.1.1
    calc
      sourceBandLowerNat m ≤
          localTime s (favoriteCreationHorizon m k s) x := hxTheta.1.2
      _ = clock.stoppedExternal s x + clock.stoppedLazy s x :=
        clock.stopped_decomposition s x
      _ ≤ intervalDotIndex m (sourceBandLowerNat m)
            (xEastPrimedEncodedProfile first labels) x +
          clock.inverseHoldingPrefix s
            (intervalDotIndex m (sourceBandLowerNat m)
              (xEastPrimedEncodedProfile first labels) x) x :=
        Nat.add_le_add hext hcompat.2
  have hplusSubset : (C ∩ H ∩ xEastPrimedSourceEvent m k) ∩
      plusEvent ⊆
      primedIntervalCanonicalPriorDotThetaPlusEvent clock h.sites m
        (xEastPrimedEncodedProfile first labels) := by
    intro s hs'
    have hsTheta := hs'.2
    simp only [plusEvent, primedIntervalStoppedThetaPlusEvent,
      Set.mem_iUnion] at hsTheta
    rcases hsTheta with ⟨x, hxsite, hxTheta⟩
    rw [primedIntervalCanonicalPriorDotThetaPlusEvent]
    simp only [Set.mem_iUnion]
    have hprofile : clock.inverseProfile s x =
        xEastPrimedEncodedProfile first labels x :=
      h.profile_atom hs'.1.1.1 x hxsite
    have hcompat := h.plus_compatible hs'.1 hxsite hxTheta
    have hcompatProfile : clock.stoppedExternal s x ≤
        clock.inverseProfile s x := by
      simpa only [clock] using hcompat.1
    have hcandidate : x ∈ intervalPlusCandidates h.sites m m
        (xEastPrimedEncodedProfile first labels) := by
      rw [intervalPlusCandidates, Finset.mem_filter]
      exact ⟨hxsite, hxTheta.1.trans (hcompatProfile.trans_eq hprofile)⟩
    refine ⟨x, hcandidate, ?_⟩
    change intervalHighCut m m +
      clock.inverseHoldingPrefix s (intervalPriorHighCut m m) x < m
    calc
      intervalHighCut m m +
          clock.inverseHoldingPrefix s (intervalPriorHighCut m m) x ≤
        clock.stoppedExternal s x + clock.stoppedLazy s x :=
        Nat.add_le_add hxTheta.1 hcompat.2
      _ = localTime s (favoriteCreationHorizon m k s) x :=
        (clock.stopped_decomposition s x).symm
      _ < m := hxTheta.2
  have hminus : simpleRandomWalkLaw[|C]
      ((C ∩ H ∩ xEastPrimedSourceEvent m k) ∩ minusEvent) ≤
      ENNReal.ofReal (Real.exp (-sourceRate m)) +
        ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ))) := by
    exact (measure_mono hminusSubset).trans
      (cond_intervalDotTheta_le_two_scale m (sourceBandLowerNat m) hs.1
        simpleRandomWalkLaw C h.sites
        (xEastPrimedEncodedProfile first labels)
        (fun s x ↦ clock.inverseHoldingPrefix s
          (intervalDotIndex m (sourceBandLowerNat m)
            (xEastPrimedEncodedProfile first labels) x) x)
        h.prop44_card h.horizon_card h.minus_law)
  have hplus : simpleRandomWalkLaw[|C]
      ((C ∩ H ∩ xEastPrimedSourceEvent m k) ∩ plusEvent) ≤
      ENNReal.ofReal (Real.exp (-sourceRate m)) := by
    exact (measure_mono hplusSubset).trans
      (cond_intervalPriorDotThetaPlus_le_exp m m hs.2 simpleRandomWalkLaw C
        h.sites (xEastPrimedEncodedProfile first labels)
        (fun s x ↦ clock.inverseHoldingPrefix s (intervalPriorHighCut m m) x)
        h.prop44_card h.plus_law)
  calc
    simpleRandomWalkLaw[|C] (C ∩ H ∩ xEastPrimedSourceEvent m k) ≤
        simpleRandomWalkLaw[|C]
          ((C ∩ H ∩ xEastPrimedSourceEvent m k) ∩
            (minusEvent ∪ plusEvent)) :=
      measure_mono h.theta_subset
    _ ≤ simpleRandomWalkLaw[|C]
          ((C ∩ H ∩ xEastPrimedSourceEvent m k) ∩ minusEvent) +
        simpleRandomWalkLaw[|C]
          ((C ∩ H ∩ xEastPrimedSourceEvent m k) ∩ plusEvent) := by
      have hunion :
          ((C ∩ H ∩ xEastPrimedSourceEvent m k) ∩
            (minusEvent ∪ plusEvent)) =
          ((C ∩ H ∩ xEastPrimedSourceEvent m k) ∩ minusEvent) ∪
          ((C ∩ H ∩ xEastPrimedSourceEvent m k) ∩ plusEvent) := by
        ext s
        simp only [Set.mem_inter_iff, Set.mem_union]
        tauto
      rw [hunion]
      exact measure_union_le _ _
    _ ≤ sourceProp45OneSideError m := add_le_add hminus hplus

structure XEastPrimedFiniteAtomization
    (m k badCoeff : ℕ) where
  atoms : Finset ℕ
  q : ℕ → ℕ
  first : ℕ → Direction
  labels : ∀ j, Fin (q j) → IncrementPair
  horizon : Set Path
  bad : Set Path
  atomInputs : ∀ j ∈ atoms,
    XEastPrimedExternalAtomInputs m k (q j) (first j) (labels j) horizon
  pairwise : (atoms : Set ℕ).PairwiseDisjoint
    (fun j ↦ primedExternalPathWalkAtom (first j) (labels j))
  cover : xEastPrimedSourceEvent m k ⊆ bad ∪
    ⋃ j ∈ atoms,
      primedExternalPathWalkAtom (first j) (labels j) ∩ horizon ∩
        xEastPrimedSourceEvent m k
  bad_bound : simpleRandomWalkLaw bad ≤
    sourceExceptionalRateWithPrefactor m badCoeff kappa

theorem XEastPrimedFiniteAtomization.theta_measure_le
    {m k badCoeff : ℕ}
    (hs : SourceIntervalScale m (sourceBandLowerNat m) ∧
      SourceUpperScale m m)
    (habsorb : sourceProp45OneSideError m ≤
      sourceExceptionalRateWithPrefactor m 3 kappa)
    (h : XEastPrimedFiniteAtomization m k badCoeff) :
    simpleRandomWalkLaw (xEastPrimedSourceEvent m k) ≤
      sourceExceptionalRateWithPrefactor m (badCoeff + 3) kappa := by
  have hcore := measure_le_bad_add_of_finite_conditional_partition
    simpleRandomWalkLaw h.atoms
    (fun j ↦ primedExternalPathWalkAtom (h.first j) (h.labels j))
    (xEastPrimedSourceEvent m k) h.horizon h.bad
    (sourceProp45OneSideError m)
    (sourceExceptionalRateWithPrefactor m badCoeff kappa)
    (fun j _ ↦ measurableSet_primedExternalPathWalkAtom
      (h.first j) (h.labels j)) h.pairwise h.cover h.bad_bound
    (fun j hj ↦ (h.atomInputs j hj).conditional_theta_le hs)
  calc
    simpleRandomWalkLaw (xEastPrimedSourceEvent m k) ≤
      sourceExceptionalRateWithPrefactor m badCoeff kappa +
        sourceProp45OneSideError m := hcore
    _ ≤ sourceExceptionalRateWithPrefactor m badCoeff kappa +
        sourceExceptionalRateWithPrefactor m 3 kappa := by gcongr
    _ = sourceExceptionalRateWithPrefactor m (badCoeff + 3) kappa := by
      simp only [sourceExceptionalRateWithPrefactor]
      push_cast
      ring

/-! ### Source-reduced fixed-depth atoms

The stopped external horizon is first bounded by a deterministic depth.
At that fixed depth the external labels form a literal finite partition.
This avoids the false stronger requirement that prefix cylinders of
different lengths be disjoint. -/

abbrev FixedExternalLabels (q : ℕ) :=
  Fin q → HLOZExternalChain.ExternalPairLabel

def fixedIncrementLabels {q : ℕ} (v : FixedExternalLabels q) :
    Fin q → IncrementPair := fun i ↦ v i

theorem fixedIncrementLabels_nondistinguished {q : ℕ}
    (v : FixedExternalLabels q) :
    ∀ i, fixedIncrementLabels v i ≠ distinguishedIncrementPair :=
  fun i ↦ (v i).property

/-- The base before the `i`th fixed terminal pair is the infinite external
walk at external time `2*i`, for every infinite label stream extending the
fixed vector. -/
theorem fixedExternalBase_eq_externalWalk_of_prefix
    {q : ℕ} (v : FixedExternalLabels q)
    (labels : ℕ → HLOZExternalChain.ExternalPairLabel)
    (hprefix : ∀ i : Fin q, labels i = v i)
    (i : ℕ) (hi : i ≤ q) :
    fixedExternalBase (fixedIncrementLabels v) i =
      HLOZExternalChain.externalWalk labels (2 * i) := by
  induction i with
  | zero =>
      rfl
  | succ i ih =>
      have hiq : i < q := by omega
      rw [fixedExternalBase_succ (fixedIncrementLabels v) hiq]
      rw [HLOZExternalChain.externalWalk]
      rw [simpleRandomWalk_pair_succ]
      rw [← HLOZExternalChain.externalWalk, ← ih (by omega)]
      have hpair : incrementPair i
          (HLOZExternalChain.externalDirectionStream labels) =
          fixedIncrementLabels v ⟨i, hiq⟩ := by
        have hv : (labels i : IncrementPair) =
            fixedIncrementLabels v ⟨i, hiq⟩ :=
          congrArg Subtype.val (hprefix ⟨i, hiq⟩)
        funext j
        fin_cases j
        · simpa [incrementPair_zero,
              HLOZExternalChain.externalDirectionStream,
              HLOZExternalChain.pairOffset] using congrFun hv 0
        · have hdiv : (2 * i + 1) / 2 = i := by omega
          simpa [incrementPair_one,
              HLOZExternalChain.externalDirectionStream,
              HLOZExternalChain.pairOffset, hdiv] using congrFun hv 1
      rw [← hpair]
      rfl

/-- Every visit counted by the fixed external profile occurs by external
time `2*q-1`; hence it is also counted at any later deterministic external
horizon. -/
theorem xEastEncodedProfile_le_externalWalk_localTime_of_prefix
    {q n : ℕ} (v : FixedExternalLabels q)
    (labels : ℕ → HLOZExternalChain.ExternalPairLabel)
    (hprefix : ∀ i : Fin q, labels i = v i)
    (hn : 2 * q - 1 ≤ n) (x : Site) :
    xEastEncodedProfile (fixedIncrementLabels v) x ≤
      localTime (HLOZExternalChain.externalWalk labels) n x := by
  let indices :=
    (chronologicalExternalIndexList (fixedIncrementLabels v) x).toFinset
  let times := indices.image fun i : Fin q ↦ 2 * i.1
  have htimes : times ⊆
      (Finset.range (n + 1)).filter fun t ↦
        HLOZExternalChain.externalWalk labels t = x := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨i, hi, rfl⟩
    have hilist : i ∈ chronologicalExternalIndexList
        (fixedIncrementLabels v) x := by
      exact List.mem_toFinset.mp hi
    have hbase : fixedExternalBase (fixedIncrementLabels v) i.1 = x := by
      exact of_decide_eq_true (List.mem_filter.mp hilist).2
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [← fixedExternalBase_eq_externalWalk_of_prefix v labels hprefix
      i.1 i.2.le]
    exact hbase
  calc
    xEastEncodedProfile (fixedIncrementLabels v) x = indices.card := by
      dsimp only [xEastEncodedProfile, indices]
      exact (List.toFinset_card_of_nodup
        (chronologicalExternalIndexList_nodup
          (fixedIncrementLabels v) x)).symm
    _ = times.card := by
      dsimp only [times]
      rw [Finset.card_image_of_injective]
      intro i j hij
      apply Fin.ext
      exact Nat.mul_left_cancel (by omega : 0 < 2) hij
    _ ≤ ((Finset.range (n + 1)).filter fun t ↦
        HLOZExternalChain.externalWalk labels t = x).card :=
      Finset.card_le_card htimes
    _ = localTime (HLOZExternalChain.externalWalk labels) n x := rfl

/-- The even external states whose visit multiplicities are encoded by a
fixed `q`-label unprimed atom. -/
noncomputable def xEastUnprimedFixedSites {q : ℕ}
    (v : FixedExternalLabels q) : Finset Site :=
  Finset.univ.image fun i : Fin q ↦ fixedExternalBase
    (fixedIncrementLabels v) i.1

/-- At any deterministic pair horizon inside a realized fixed-label
prefix, the walk is at the external base indexed by the number of terminal
labels already seen.  This includes stretches of distinguished lazy pairs:
they leave both the terminal-label count and the even-time position
unchanged. -/
theorem simpleRandomWalk_even_eq_fixedExternalBase_of_realized
    {q : ℕ} (labels : Fin q → IncrementPair) {omega : ℕ → Direction}
    {N : ℕ}
    (hlabels : terminalPairLabelsThrough omega N = List.ofFn labels)
    (r : ℕ) (hrN : r ≤ N) :
    simpleRandomWalk omega (2 * r) =
      fixedExternalBase labels (terminalPairLabelsThrough omega r).length := by
  induction r with
  | zero =>
      simp [simpleRandomWalk, terminalPairLabelsThrough, fixedExternalBase]
      change (0, 0) = (0, 0)
      rfl
  | succ r ih =>
      have hrN' : r ≤ N := by omega
      have ih' := ih hrN'
      by_cases hdist : incrementPair r omega = distinguishedIncrementPair
      · have hlen := terminalPairLabelsThrough_succ_length omega r
        rw [if_pos hdist] at hlen
        have h0 := congrFun hdist 0
        have h1 := congrFun hdist 1
        simp only [incrementPair_zero] at h0
        simp only [incrementPair_one] at h1
        rw [simpleRandomWalk_pair_succ, ih', h0, h1]
        have hzero := distinguishedPair_step_sum_zero
        simp only [add_assoc, hzero, add_zero, hlen]
        ext <;> simp
      · let i := (terminalPairLabelsThrough omega r).length
        have hstep := terminalPairLabelsThrough_succ_length omega r
        rw [if_neg hdist] at hstep
        have hprefix := terminalPairLabelsThrough_prefix omega
          (show r + 1 ≤ N by omega)
        have hlenLe :
            (terminalPairLabelsThrough omega (r + 1)).length ≤ q := by
          have := hprefix.length_le
          simpa only [hlabels, List.length_ofFn] using this
        have hiq : i < q := by
          dsimp only [i]
          omega
        have hex := terminalPairIndex_exists_of_realized labels hlabels hiq
        have hcount := terminalPairIndex_count omega i hex
        have hindexLe : terminalPairIndex omega i ≤ r :=
          terminalPairIndex_minimal omega i r (by
            dsimp only [i]
            omega)
        have hindex : terminalPairIndex omega i = r := by
          apply le_antisymm hindexLe
          by_contra hnot
          have hmono := terminalPairLabelsThrough_length_mono omega
            (show terminalPairIndex omega i + 1 ≤ r by omega)
          have hindexStep := terminalPairLabelsThrough_succ_length omega
            (terminalPairIndex omega i)
          rw [if_neg hcount.2, hcount.1] at hindexStep
          dsimp only [i] at hmono
          rw [hindexStep] at hmono
          omega
        have hlabel := terminalPairIndex_label_of_realized labels hlabels
          ⟨i, hiq⟩
        rw [hindex] at hlabel
        have h0 := congrFun hlabel 0
        have h1 := congrFun hlabel 1
        simp only [incrementPair_zero] at h0
        simp only [incrementPair_one] at h1
        rw [simpleRandomWalk_pair_succ, ih', h0, h1]
        change pairEndpoint (fixedExternalBase labels i) (labels ⟨i, hiq⟩) = _
        rw [← fixedExternalBase_succ labels hiq]
        exact congrArg (fixedExternalBase labels) hstep.symm

/-- A removed time strictly before an earlier horizon remains removed at
that horizon.  The only index that a later completed lazy pair can newly
remove at the boundary is the earlier current time itself. -/
theorem mem_lazyRemovedTimes_of_lt_of_mem_later
    (s : Path) {T U j : ℕ} (hjT : j < T) (hTU : T ≤ U)
    (hj : j ∈ lazyRemovedTimes s U) :
    j ∈ lazyRemovedTimes s T := by
  classical
  rw [lazyRemovedTimes, Finset.mem_union] at hj ⊢
  rcases hj with hj | hj
  · left
    rcases Finset.mem_biUnion.mp hj with ⟨e, he, hje⟩
    refine Finset.mem_biUnion.mpr ⟨e, ?_, hje⟩
    rw [lazyEndsThrough, Finset.mem_filter] at he ⊢
    rcases he with ⟨heIcc, heLazy⟩
    refine ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp heIcc).1, ?_⟩, heLazy⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hje
    rcases hje with rfl | rfl <;> omega
  · unfold partialLazyRemovedTimes at hj ⊢
    split at hj
    · simp only [Finset.mem_singleton] at hj
      omega
    · simp at hj

theorem mem_lazyRemovedTimes_of_le_of_mem_later
    (s : Path) {T U j : ℕ} (hjT : j ≤ T) (hTU : T ≤ U)
    (hj : j ∈ lazyRemovedTimes s U) :
    j ∈ lazyRemovedTimes s T := by
  classical
  by_cases hjlt : j < T
  · exact mem_lazyRemovedTimes_of_lt_of_mem_later s hjlt hTU hj
  have hjEq : j = T := by omega
  subst j
  rw [lazyRemovedTimes, Finset.mem_union] at hj ⊢
  rcases hj with hj | hj
  · rcases Finset.mem_biUnion.mp hj with ⟨e, he, hTe⟩
    rw [lazyEndsThrough, Finset.mem_filter] at he
    rcases he with ⟨heIcc, heLazy⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hTe
    rcases hTe with hTe | hTe
    · right
      unfold partialLazyRemovedTimes
      have he2 : 2 ≤ e := (Finset.mem_Icc.mp heIcc).1
      have heq : e = T + 1 := by omega
      rw [if_pos (by simpa only [heq] using heLazy)]
      simp
    · left
      apply Finset.mem_biUnion.mpr
      refine ⟨e, ?_, ?_⟩
      · rw [lazyEndsThrough, Finset.mem_filter]
        refine ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp heIcc).1, ?_⟩,
          heLazy⟩
        omega
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr hTe
  · right
    unfold partialLazyRemovedTimes at hj ⊢
    split at hj
    · simp only [Finset.mem_singleton] at hj
      have hUT : U = T := by omega
      subst U
      split
      · simp
      · contradiction
    · simp at hj

/-- Removed times persist when the unprimed deletion horizon is extended. -/
theorem mem_lazyRemovedTimes_of_mem_earlier
    (s : Path) {T U j : ℕ} (hTU : T ≤ U)
    (hj : j ∈ lazyRemovedTimes s T) :
    j ∈ lazyRemovedTimes s U := by
  classical
  rw [lazyRemovedTimes, Finset.mem_union] at hj ⊢
  rcases hj with hj | hj
  · left
    rcases Finset.mem_biUnion.mp hj with ⟨e, he, hje⟩
    refine Finset.mem_biUnion.mpr ⟨e, ?_, hje⟩
    rw [lazyEndsThrough, Finset.mem_filter] at he ⊢
    exact ⟨Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp he.1).1, (Finset.mem_Icc.mp he.1).2.trans hTU⟩,
        he.2⟩
  · unfold partialLazyRemovedTimes at hj
    by_cases hEnd : IsLazyEnd s (T + 1)
    · rw [if_pos hEnd] at hj
      simp only [Finset.mem_singleton] at hj
      subst j
      by_cases hEq : U = T
      · subst U
        right
        unfold partialLazyRemovedTimes
        rw [if_pos hEnd]
        simp
      · left
        apply Finset.mem_biUnion.mpr
        refine ⟨T + 1, ?_, ?_⟩
        · rw [lazyEndsThrough, Finset.mem_filter]
          exact ⟨Finset.mem_Icc.mpr ⟨hEnd.1, by omega⟩, hEnd⟩
        · simp
    · rw [if_neg hEnd] at hj
      simp at hj

theorem paperLazyLocalTime_mono
    (s : Path) {T U : ℕ} (x : Site) (hTU : T ≤ U) :
    paperLazyLocalTime s T x ≤ paperLazyLocalTime s U x := by
  unfold paperLazyLocalTime
  apply Finset.card_le_card
  intro j hj
  rw [Finset.mem_filter] at hj ⊢
  exact ⟨mem_lazyRemovedTimes_of_mem_earlier s hTU hj.1, hj.2⟩

/-- External local time cannot decrease when the horizon is extended.  The
one-step lookahead in `partialLazyRemovedTimes` already removes the boundary
point if a later completed lazy pair would otherwise delete it. -/
theorem paperExternalLocalTime_mono
    (s : Path) {T U : ℕ} (x : Site) (hTU : T ≤ U) :
    paperExternalLocalTime s T x ≤ paperExternalLocalTime s U x := by
  unfold paperExternalLocalTime
  apply Finset.card_le_card
  intro j hj
  rw [Finset.mem_filter, retainedTimes, Finset.mem_sdiff] at hj ⊢
  rcases hj with ⟨⟨hjRange, hjNotRemoved⟩, hjx⟩
  refine ⟨⟨?_, ?_⟩, hjx⟩
  · simp only [Finset.mem_range] at hjRange ⊢
    omega
  · intro hjRemoved
    have hjle : j ≤ T := by
      have hjlt : j < T + 1 := Finset.mem_range.mp hjRange
      omega
    exact hjNotRemoved
      (mem_lazyRemovedTimes_of_le_of_mem_later s hjle hTU hjRemoved)

theorem mem_primedRemovedTimes_of_lt_of_mem_later
    (s : Path) {T U j : ℕ} (hjT : j < T) (hTU : T ≤ U)
    (hj : j ∈ primedRemovedTimes s U) :
    j ∈ primedRemovedTimes s T := by
  classical
  rw [primedRemovedTimes, Finset.mem_union] at hj ⊢
  rcases hj with hj | hj
  · left
    rcases Finset.mem_biUnion.mp hj with ⟨e, he, hje⟩
    refine Finset.mem_biUnion.mpr ⟨e, ?_, hje⟩
    rw [primedLazyEndsThrough, Finset.mem_filter] at he ⊢
    rcases he with ⟨heIcc, heLazy⟩
    refine ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp heIcc).1, ?_⟩, heLazy⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hje
    rcases hje with rfl | rfl <;> omega
  · unfold primedPartialRemovedTimes at hj ⊢
    split at hj
    · simp only [Finset.mem_singleton] at hj
      omega
    · simp at hj

theorem mem_primedRemovedTimes_of_le_of_mem_later
    (s : Path) {T U j : ℕ} (hjT : j ≤ T) (hTU : T ≤ U)
    (hj : j ∈ primedRemovedTimes s U) :
    j ∈ primedRemovedTimes s T := by
  classical
  by_cases hjlt : j < T
  · exact mem_primedRemovedTimes_of_lt_of_mem_later s hjlt hTU hj
  have hjEq : j = T := by omega
  subst j
  rw [primedRemovedTimes, Finset.mem_union] at hj ⊢
  rcases hj with hj | hj
  · rcases Finset.mem_biUnion.mp hj with ⟨e, he, hTe⟩
    rw [primedLazyEndsThrough, Finset.mem_filter] at he
    rcases he with ⟨heIcc, heLazy⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hTe
    rcases hTe with hTe | hTe
    · right
      unfold primedPartialRemovedTimes
      have he3 : 3 ≤ e := (Finset.mem_Icc.mp heIcc).1
      have heq : e = T + 1 := by omega
      rw [if_pos (by simpa only [heq] using heLazy)]
      simp
    · left
      apply Finset.mem_biUnion.mpr
      refine ⟨e, ?_, ?_⟩
      · rw [primedLazyEndsThrough, Finset.mem_filter]
        refine ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp heIcc).1, ?_⟩,
          heLazy⟩
        omega
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr hTe
  · right
    unfold primedPartialRemovedTimes at hj ⊢
    split at hj
    · simp only [Finset.mem_singleton] at hj
      have hUT : U = T := by omega
      subst U
      split
      · simp
      · contradiction
    · simp at hj

/-- Removed times persist when the primed deletion horizon is extended. -/
theorem mem_primedRemovedTimes_of_mem_earlier
    (s : Path) {T U j : ℕ} (hTU : T ≤ U)
    (hj : j ∈ primedRemovedTimes s T) :
    j ∈ primedRemovedTimes s U := by
  classical
  rw [primedRemovedTimes, Finset.mem_union] at hj ⊢
  rcases hj with hj | hj
  · left
    rcases Finset.mem_biUnion.mp hj with ⟨e, he, hje⟩
    refine Finset.mem_biUnion.mpr ⟨e, ?_, hje⟩
    rw [primedLazyEndsThrough, Finset.mem_filter] at he ⊢
    exact ⟨Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp he.1).1, (Finset.mem_Icc.mp he.1).2.trans hTU⟩,
        he.2⟩
  · unfold primedPartialRemovedTimes at hj
    by_cases hEnd : IsPrimedLazyEnd s (T + 1)
    · rw [if_pos hEnd] at hj
      simp only [Finset.mem_singleton] at hj
      subst j
      by_cases hEq : U = T
      · subst U
        right
        unfold primedPartialRemovedTimes
        rw [if_pos hEnd]
        simp
      · left
        apply Finset.mem_biUnion.mpr
        refine ⟨T + 1, ?_, ?_⟩
        · rw [primedLazyEndsThrough, Finset.mem_filter]
          exact ⟨Finset.mem_Icc.mpr ⟨hEnd.1, by omega⟩, hEnd⟩
        · simp
    · rw [if_neg hEnd] at hj
      simp at hj

theorem primedLazyLocalTime_mono
    (s : Path) {T U : ℕ} (x : Site) (hTU : T ≤ U) :
    primedLazyLocalTime s T x ≤ primedLazyLocalTime s U x := by
  unfold primedLazyLocalTime
  apply Finset.card_le_card
  intro j hj
  rw [Finset.mem_filter] at hj ⊢
  exact ⟨mem_primedRemovedTimes_of_mem_earlier s hTU hj.1, hj.2⟩

theorem primedExternalLocalTime_mono
    (s : Path) {T U : ℕ} (x : Site) (hTU : T ≤ U) :
    primedExternalLocalTime s T x ≤ primedExternalLocalTime s U x := by
  unfold primedExternalLocalTime
  apply Finset.card_le_card
  intro j hj
  rw [Finset.mem_filter, primedRetainedTimes, Finset.mem_sdiff] at hj ⊢
  rcases hj with ⟨⟨hjRange, hjNotRemoved⟩, hjx⟩
  refine ⟨⟨?_, ?_⟩, hjx⟩
  · simp only [Finset.mem_range] at hjRange ⊢
    omega
  · intro hjRemoved
    have hjle : j ≤ T := by
      have hjlt : j < T + 1 := Finset.mem_range.mp hjRange
      omega
    exact hjNotRemoved
      (mem_primedRemovedTimes_of_le_of_mem_later s hjle hTU hjRemoved)

/-- If the newly exposed endpoint is not `x`, neither side of the unprimed
lazy/external decomposition can change its local time at `x`. -/
theorem paperExternalLocalTime_succ_eq_of_ne
    (s : Path) (T : ℕ) (x : Site) (hnew : s (T + 1) ≠ x) :
    paperExternalLocalTime s (T + 1) x =
      paperExternalLocalTime s T x := by
  have hlocal : localTime s (T + 1) x = localTime s T x := by
    rw [localTime_succ, if_neg hnew, add_zero]
  have hext := paperExternalLocalTime_mono s x (show T ≤ T + 1 by omega)
  have hlazy := paperLazyLocalTime_mono s x (show T ≤ T + 1 by omega)
  have hdecompT := localTime_eq_paperExternal_add_paperLazy s T x
  have hdecompSucc := localTime_eq_paperExternal_add_paperLazy s (T + 1) x
  omega

/-- Primed counterpart of `paperExternalLocalTime_succ_eq_of_ne`. -/
theorem primedExternalLocalTime_succ_eq_of_ne
    (s : Path) (T : ℕ) (x : Site) (hnew : s (T + 1) ≠ x) :
    primedExternalLocalTime s (T + 1) x =
      primedExternalLocalTime s T x := by
  have hlocal : localTime s (T + 1) x = localTime s T x := by
    rw [localTime_succ, if_neg hnew, add_zero]
  have hext := primedExternalLocalTime_mono s x (show T ≤ T + 1 by omega)
  have hlazy := primedLazyLocalTime_mono s x (show T ≤ T + 1 by omega)
  have hdecompT := localTime_eq_primedExternal_add_primedLazy s T x
  have hdecompSucc := localTime_eq_primedExternal_add_primedLazy s (T + 1) x
  omega

/-- At an even checkerboard site, the unprimed external local time is
unchanged by the first (odd-time) step of the next pair. -/
theorem paperExternalLocalTime_odd_eq_even_of_chessEven
    (omega : ℕ → Direction) (R : ℕ) (x : Site)
    (hx : HLOZPairing.chessEven x) :
    paperExternalLocalTime (simpleRandomWalk omega) (2 * R + 1) x =
      paperExternalLocalTime (simpleRandomWalk omega) (2 * R) x := by
  classical
  unfold paperExternalLocalTime retainedTimes lazyRemovedTimes
    completedLazyRemovedTimes partialLazyRemovedTimes
  apply congrArg Finset.card
  ext j
  rw [lazyEndsThrough_odd_eq_even]
  have hnot : ¬ IsLazyEnd (simpleRandomWalk omega) (2 * R + 1) := by
    intro h
    rcases h.2.1 with ⟨a, ha⟩
    omega
  by_cases hnext : IsLazyEnd (simpleRandomWalk omega) (2 * R + 2)
  · simp only [hnext, if_true, hnot, if_false, Finset.mem_filter, Finset.mem_sdiff,
      Finset.mem_range, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, or_false, not_or]
    constructor
    · rintro ⟨⟨hjRange, hjRemoved, hjNext⟩, hjx⟩
      refine ⟨⟨by omega, hjRemoved⟩, hjx⟩
    · rintro ⟨⟨hjRange, hjRemoved⟩, hjx⟩
      refine ⟨⟨by omega, hjRemoved, ?_⟩, hjx⟩
      intro hjeq
      have hjEven := (chessEven_simpleRandomWalk_iff omega j).mp
        (hjx ▸ hx)
      rcases hjEven with ⟨a, ha⟩
      omega
  · simp only [hnext, if_false, hnot, Finset.mem_filter,
      Finset.mem_sdiff, Finset.mem_range, Finset.mem_union,
      Finset.notMem_empty, or_false]
    constructor
    · rintro ⟨⟨hjRange, hjRemoved⟩, hjx⟩
      have hjEven := (chessEven_simpleRandomWalk_iff omega j).mp
        (hjx ▸ hx)
      rcases hjEven with ⟨a, ha⟩
      exact ⟨⟨by omega, hjRemoved⟩, hjx⟩
    · rintro ⟨⟨hjRange, hjRemoved⟩, hjx⟩
      exact ⟨⟨by omega, hjRemoved⟩, hjx⟩

/-- No new completed primed lazy pair can end at an even horizon. -/
theorem primedLazyEndsThrough_even_eq_odd
    (s : Path) (R : ℕ) :
    primedLazyEndsThrough s (2 * R + 2) =
      primedLazyEndsThrough s (2 * R + 1) := by
  ext k
  simp only [primedLazyEndsThrough, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hk3, hkR⟩, hkLazy⟩
    refine ⟨⟨hk3, ?_⟩, hkLazy⟩
    rcases hkLazy.2.1 with ⟨a, ha⟩
    omega
  · rintro ⟨⟨hk3, hkR⟩, hkLazy⟩
    exact ⟨⟨hk3, by omega⟩, hkLazy⟩

/-- At an odd checkerboard site, the primed external local time is
unchanged by the even-time step following a shifted pair. -/
theorem primedExternalLocalTime_even_eq_odd_of_chessOdd
    (omega : ℕ → Direction) (R : ℕ) (x : Site)
    (hx : ¬ HLOZPairing.chessEven x) :
    primedExternalLocalTime (simpleRandomWalk omega) (2 * R + 2) x =
      primedExternalLocalTime (simpleRandomWalk omega) (2 * R + 1) x := by
  classical
  unfold primedExternalLocalTime primedRetainedTimes primedRemovedTimes
    primedCompletedRemovedTimes primedPartialRemovedTimes
  apply congrArg Finset.card
  ext j
  rw [primedLazyEndsThrough_even_eq_odd]
  have hnot : ¬ IsPrimedLazyEnd (simpleRandomWalk omega) (2 * R + 2) := by
    intro h
    rcases h.2.1 with ⟨a, ha⟩
    omega
  by_cases hnext : IsPrimedLazyEnd (simpleRandomWalk omega) (2 * R + 3)
  · simp only [hnext, if_true, hnot, if_false, Finset.mem_filter,
      Finset.mem_sdiff, Finset.mem_range, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, or_false, not_or]
    constructor
    · rintro ⟨⟨hjRange, hjRemoved, hjNext⟩, hjx⟩
      have hjNotEven : ¬ Even j := by
        intro hjEven
        exact hx (hjx ▸ (chessEven_simpleRandomWalk_iff omega j).mpr hjEven)
      rcases Nat.not_even_iff_odd.mp hjNotEven with ⟨a, ha⟩
      exact ⟨⟨by omega, hjRemoved⟩, hjx⟩
    · rintro ⟨⟨hjRange, hjRemoved⟩, hjx⟩
      refine ⟨⟨by omega, hjRemoved, ?_⟩, hjx⟩
      intro hjeq
      have hjNotEven : ¬ Even j := by
        intro hjEven
        exact hx (hjx ▸ (chessEven_simpleRandomWalk_iff omega j).mpr hjEven)
      rcases Nat.not_even_iff_odd.mp hjNotEven with ⟨a, ha⟩
      omega
  · simp only [hnext, if_false, hnot, Finset.mem_filter,
      Finset.mem_sdiff, Finset.mem_range, Finset.mem_union,
      Finset.notMem_empty, or_false]
    constructor
    · rintro ⟨⟨hjRange, hjRemoved⟩, hjx⟩
      have hjNotEven : ¬ Even j := by
        intro hjEven
        exact hx (hjx ▸ (chessEven_simpleRandomWalk_iff omega j).mpr hjEven)
      rcases Nat.not_even_iff_odd.mp hjNotEven with ⟨a, ha⟩
      exact ⟨⟨by omega, hjRemoved⟩, hjx⟩
    · rintro ⟨⟨hjRange, hjRemoved⟩, hjx⟩
      exact ⟨⟨by omega, hjRemoved⟩, hjx⟩

/-- At an even checkerboard site the full lazy contribution is likewise
unchanged by the first, odd-time step of the next pair.  This follows from
the local/external decomposition, so it retains the one-step lookahead in
`paperLazyLocalTime` exactly. -/
theorem paperLazyLocalTime_odd_eq_even_of_chessEven
    (omega : ℕ → Direction) (R : ℕ) (x : Site)
    (hx : HLOZPairing.chessEven x) :
    paperLazyLocalTime (simpleRandomWalk omega) (2 * R + 1) x =
      paperLazyLocalTime (simpleRandomWalk omega) (2 * R) x := by
  have hnew : simpleRandomWalk omega (2 * R + 1) ≠ x := by
    intro heq
    have hodd : ¬ Even (2 * R + 1) :=
      Nat.not_even_iff_odd.mpr ⟨R, by omega⟩
    exact hodd ((chessEven_simpleRandomWalk_iff omega (2 * R + 1)).mp
      (heq ▸ hx))
  have hlocal : localTime (simpleRandomWalk omega) (2 * R + 1) x =
      localTime (simpleRandomWalk omega) (2 * R) x := by
    rw [localTime_succ, if_neg hnew, add_zero]
  have hext := paperExternalLocalTime_odd_eq_even_of_chessEven omega R x hx
  have hdecompOdd := localTime_eq_paperExternal_add_paperLazy
    (simpleRandomWalk omega) (2 * R + 1) x
  have hdecompEven := localTime_eq_paperExternal_add_paperLazy
    (simpleRandomWalk omega) (2 * R) x
  omega

/-- At an odd checkerboard site, the primed lazy contribution is unchanged
by the following even-time step. -/
theorem primedLazyLocalTime_even_eq_odd_of_chessOdd
    (omega : ℕ → Direction) (R : ℕ) (x : Site)
    (hx : ¬ HLOZPairing.chessEven x) :
    primedLazyLocalTime (simpleRandomWalk omega) (2 * R + 2) x =
      primedLazyLocalTime (simpleRandomWalk omega) (2 * R + 1) x := by
  have hnew : simpleRandomWalk omega (2 * R + 2) ≠ x := by
    intro heq
    apply hx
    exact heq ▸ (chessEven_simpleRandomWalk_iff omega (2 * R + 2)).mpr
      (by exact ⟨R + 1, by omega⟩)
  have hlocal : localTime (simpleRandomWalk omega) (2 * R + 2) x =
      localTime (simpleRandomWalk omega) (2 * R + 1) x := by
    rw [localTime_succ, if_neg hnew, add_zero]
  have hext := primedExternalLocalTime_even_eq_odd_of_chessOdd omega R x hx
  have hdecompEven := localTime_eq_primedExternal_add_primedLazy
    (simpleRandomWalk omega) (2 * R + 2) x
  have hdecompOdd := localTime_eq_primedExternal_add_primedLazy
    (simpleRandomWalk omega) (2 * R + 1) x
  omega

/-- Before the last fixed label, every retained visit to an even site is
represented by a distinct base coordinate of the fixed external profile. -/
theorem paperExternalLocalTime_even_le_fixedProfile_of_lt
    {q R : ℕ} (v : FixedExternalLabels q) (hR : R < q)
    {s : Path}
    (hs : s ∈ externalPathWalkAtom
      (List.ofFn (fixedIncrementLabels v)))
    (x : Site) (hx : HLOZPairing.chessEven x) :
    paperExternalLocalTime s (2 * R) x ≤
      inverseClockProfile s (2 * q - 1) x := by
  classical
  rcases hs with ⟨omega, homega, rfl⟩
  obtain ⟨N, hlabels⟩ := realized_terminalPairLabelsThrough
    (fixedIncrementLabels v) (fixedIncrementLabels_nondistinguished v) homega
  have hqN : q ≤ N := by
    have hcount := distinguished_add_terminal_count omega N
    rw [hlabels, List.length_ofFn] at hcount
    omega
  rw [inverseClockProfile_eq_chronological_length
    (fixedIncrementLabels v) hlabels x hx (by omega)]
  let A := (retainedTimes (simpleRandomWalk omega) (2 * R)).filter
    fun j ↦ simpleRandomWalk omega j = x
  let f : ℕ → ℕ := fun j ↦
    (terminalPairLabelsThrough omega (j / 2)).length
  let B := (Finset.range q).filter fun i ↦
    fixedExternalBase (fixedIncrementLabels v) i = x
  have hfmem : ∀ j ∈ A, f j ∈ B := by
    intro j hj
    rw [Finset.mem_filter] at hj
    have hjEven : Even j :=
      (chessEven_simpleRandomWalk_iff omega j).mp (hj.2 ▸ hx)
    rcases hjEven with ⟨r, hr⟩
    have hrR : r ≤ R := by
      rw [retainedTimes, Finset.mem_sdiff, Finset.mem_range] at hj
      omega
    have hrN : r ≤ N := hrR.trans (hR.le.trans hqN)
    have hwalk := simpleRandomWalk_even_eq_fixedExternalBase_of_realized
      (fixedIncrementLabels v) hlabels r hrN
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, ?_⟩
    · dsimp only [f]
      have hcount := distinguished_add_terminal_count omega r
      rw [show j / 2 = r by omega]
      omega
    · dsimp only [f]
      rw [show j / 2 = r by omega]
      have hjr : simpleRandomWalk omega (2 * r) = x := by
        rw [two_mul, ← hr]
        exact hj.2
      exact hwalk.symm.trans hjr
  have hfinj : Set.InjOn f A := by
    intro j₁ hj₁ j₂ hj₂ heq
    change j₁ ∈ A at hj₁
    change j₂ ∈ A at hj₂
    rw [Finset.mem_filter] at hj₁ hj₂
    have hj₁Even : Even j₁ :=
      (chessEven_simpleRandomWalk_iff omega j₁).mp (hj₁.2 ▸ hx)
    have hj₂Even : Even j₂ :=
      (chessEven_simpleRandomWalk_iff omega j₂).mp (hj₂.2 ▸ hx)
    rcases hj₁Even with ⟨r₁, hr₁⟩
    rcases hj₂Even with ⟨r₂, hr₂⟩
    have hr₁R : r₁ ≤ R := by
      rw [retainedTimes, Finset.mem_sdiff, Finset.mem_range] at hj₁
      omega
    have hr₂R : r₂ ≤ R := by
      rw [retainedTimes, Finset.mem_sdiff, Finset.mem_range] at hj₂
      omega
    have hstrict : ∀ {j a b : ℕ},
        j ∈ retainedTimes (simpleRandomWalk omega) (2 * R) →
        j = 2 * b → a < b → b ≤ R →
        (terminalPairLabelsThrough omega a).length <
          (terminalPairLabelsThrough omega b).length := by
      intro j a b hjRet hjb hab hbR
      subst j
      have hbpos : 0 < b := by omega
      have hnotRemoved := (Finset.mem_sdiff.mp hjRet).2
      have hnondist : incrementPair (b - 1) omega ≠
          distinguishedIncrementPair := by
        intro hdist
        apply hnotRemoved
        rw [lazyRemovedTimes, Finset.mem_union]
        left
        apply Finset.mem_biUnion.mpr
        refine ⟨2 * b, ?_, ?_⟩
        · rw [lazyEndsThrough, Finset.mem_filter]
          refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
          rw [show 2 * b = 2 * (b - 1) + 2 by omega,
            isLazyEnd_simpleRandomWalk_pair_iff]
          exact hdist
        · simp only [Finset.mem_insert, Finset.mem_singleton]
          simp
      have hstep := terminalPairLabelsThrough_succ_length omega (b - 1)
      rw [if_neg hnondist, Nat.sub_add_cancel hbpos] at hstep
      have hmono := terminalPairLabelsThrough_length_mono omega
        (show a ≤ b - 1 by omega)
      omega
    have hrEq : r₁ = r₂ := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have := hstrict hj₂.1 (by omega) hlt hr₂R
        dsimp only [f] at heq
        rw [show j₁ / 2 = r₁ by omega,
          show j₂ / 2 = r₂ by omega] at heq
        omega
      · have := hstrict hj₁.1 (by omega) hgt hr₁R
        dsimp only [f] at heq
        rw [show j₁ / 2 = r₁ by omega,
          show j₂ / 2 = r₂ by omega] at heq
        omega
    omega
  have hcard : A.card ≤ B.card := by
    calc
      A.card = (A.image f).card :=
        (Finset.card_image_iff.mpr (by
          intro a ha b hb hab
          exact hfinj ha hb hab)).symm
      _ ≤ B.card := Finset.card_le_card (by
        intro i hi
        rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
        exact hfmem j hj)
  have hB : B.card =
      (chronologicalExternalIndexList (fixedIncrementLabels v) x).length := by
    have hmap := congrArg List.length
      (map_chronologicalExternalIndexList (fixedIncrementLabels v) x)
    let P : ℕ → Prop := fun i ↦
      fixedExternalBase (fixedIncrementLabels v) i = x
    calc
      B.card = List.countP (fun i ↦ decide (P i)) (List.range q) := by
        dsimp only [B, P]
        have hrange : (List.range q).toFinset = Finset.range q := by
          ext i
          simp
        rw [← hrange]
        exact (List.nodup_range (n := q)).card_eq_countP
          (P := fun i : ℕ ↦
            fixedExternalBase (fixedIncrementLabels v) i = x)
      _ = ((List.range q).filter P).length :=
        List.countP_eq_length_filter
      _ = (chronologicalExternalIndexList
          (fixedIncrementLabels v) x).length := by
        dsimp only [P]
        simpa only [List.length_map] using hmap.symm
  simpa only [paperExternalLocalTime, A, hB] using hcard

/-- A realized fixed-label atom controls the unprimed external local time at
every horizon before its final represented external vertex.  The only parity
issue is the first step of the last pair, which cannot contribute at an even
checkerboard site. -/
theorem paperExternalLocalTime_le_fixedProfile_of_le
    {q T : ℕ} (v : FixedExternalLabels q) (hq : 0 < q)
    {s : Path}
    (hs : s ∈ externalPathWalkAtom
      (List.ofFn (fixedIncrementLabels v)))
    (x : Site) (hx : HLOZPairing.chessEven x)
    (hT : T ≤ 2 * q - 1) :
    paperExternalLocalTime s T x ≤
      inverseClockProfile s (2 * q - 1) x := by
  rcases hs with ⟨omega, homega, rfl⟩
  obtain ⟨R, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  have hmono : paperExternalLocalTime (simpleRandomWalk omega) T x ≤
      paperExternalLocalTime (simpleRandomWalk omega) (2 * R + 1) x :=
    paperExternalLocalTime_mono (simpleRandomWalk omega) x (by omega)
  have hparity := paperExternalLocalTime_odd_eq_even_of_chessEven
    omega R x hx
  have hfixed := paperExternalLocalTime_even_le_fixedProfile_of_lt
    v (show R < R + 1 by omega)
      (show simpleRandomWalk omega ∈ externalPathWalkAtom
        (List.ofFn (fixedIncrementLabels v)) from ⟨omega, homega, rfl⟩)
      x hx
  exact hmono.trans (hparity.le.trans hfixed)

/-- At an even checkerboard site, each completed lazy excursion contributes
exactly its even endpoint to the lazy local time.  Its odd midpoint cannot
equal the selected site.  This is the first pathwise identification needed
to compare the stopped lazy clock with a prefix of the inverse holding
coordinates. -/
theorem completedLazyLocalTime_eq_lazyEndCount_of_chessEven
    (omega : ℕ → Direction) (T : ℕ) (x : Site)
    (hx : HLOZPairing.chessEven x) :
    completedLazyLocalTime (simpleRandomWalk omega) T x =
      ((lazyEndsThrough (simpleRandomWalk omega) T).filter
        fun k ↦ simpleRandomWalk omega k = x).card := by
  classical
  apply congrArg Finset.card
  ext j
  simp only [completedLazyRemovedTimes,
    Finset.mem_filter, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨k, hk, hjk⟩, hjx⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hjk
    rcases hjk with hjk | hjk
    · subst j
      have hkData := Finset.mem_filter.mp hk
      have hkEven : Even k := hkData.2.2.1
      have hkTwo : 2 ≤ k := hkData.2.1
      have hodd : ¬ Even (k - 1) := by
        intro hsubEven
        rcases hkEven with ⟨r, hr⟩
        rcases hsubEven with ⟨u, hu⟩
        omega
      have hxTime : HLOZPairing.chessEven
          (simpleRandomWalk omega (k - 1)) := by
        simpa only [hjx] using hx
      exact (hodd ((chessEven_simpleRandomWalk_iff omega (k - 1)).mp
        hxTime)).elim
    · subst j
      exact ⟨hk, hjx⟩
  · rintro ⟨hj, hjx⟩
    refine ⟨?_, hjx⟩
    exact ⟨j, hj, by simp⟩

/-- Away from the current endpoint, the full lazy local time is therefore
the number of completed lazy excursions whose endpoint is `x`. -/
theorem paperLazyLocalTime_eq_lazyEndCount_of_chessEven
    (omega : ℕ → Direction) (T : ℕ) (x : Site)
    (hx : HLOZPairing.chessEven x)
    (hcurrent : simpleRandomWalk omega T ≠ x) :
    paperLazyLocalTime (simpleRandomWalk omega) T x =
      ((lazyEndsThrough (simpleRandomWalk omega) T).filter
        fun k ↦ simpleRandomWalk omega k = x).card := by
  rw [paperLazyLocalTime_eq_completed_of_ne_current _ _ _ hcurrent.symm]
  exact completedLazyLocalTime_eq_lazyEndCount_of_chessEven omega T x hx

/-- At an even horizon the one-step partial unprimed deletion is impossible,
so the lazy local time is the completed lazy-end count even when the current
endpoint itself is the selected even site. -/
theorem paperLazyLocalTime_even_eq_lazyEndCount_of_chessEven
    (omega : ℕ → Direction) (R : ℕ) (x : Site)
    (hx : HLOZPairing.chessEven x) :
    paperLazyLocalTime (simpleRandomWalk omega) (2 * R) x =
      ((lazyEndsThrough (simpleRandomWalk omega) (2 * R)).filter
        fun k ↦ simpleRandomWalk omega k = x).card := by
  have hnot : ¬ IsLazyEnd (simpleRandomWalk omega) (2 * R + 1) := by
    intro h
    rcases h.2.1 with ⟨a, ha⟩
    omega
  have heq : paperLazyLocalTime (simpleRandomWalk omega) (2 * R) x =
      completedLazyLocalTime (simpleRandomWalk omega) (2 * R) x := by
    unfold paperLazyLocalTime completedLazyLocalTime lazyRemovedTimes
      partialLazyRemovedTimes
    rw [if_neg hnot, Finset.union_empty]
  rw [heq]
  exact completedLazyLocalTime_eq_lazyEndCount_of_chessEven omega (2 * R) x hx

/-- For the shifted deletion the corresponding statement is cleaner: at an
odd site, neither the even midpoint of a completed primed lazy excursion nor
the one-step partial midpoint can contribute.  Hence the primed lazy local
time is exactly the number of completed primed lazy endpoints at `x`. -/
theorem primedLazyLocalTime_eq_primedLazyEndCount_of_chessOdd
    (omega : ℕ → Direction) (T : ℕ) (x : Site)
    (hx : ¬ HLOZPairing.chessEven x) :
    primedLazyLocalTime (simpleRandomWalk omega) T x =
      ((primedLazyEndsThrough (simpleRandomWalk omega) T).filter
        fun k ↦ simpleRandomWalk omega k = x).card := by
  classical
  apply congrArg Finset.card
  ext j
  unfold primedRemovedTimes primedCompletedRemovedTimes
    primedPartialRemovedTimes
  by_cases hpartial : IsPrimedLazyEnd (simpleRandomWalk omega) (T + 1)
  · rw [if_pos hpartial]
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_biUnion,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨(⟨k, hk, hjk⟩ | hjT), hjx⟩
      · rcases hjk with hjk | hjk
        · subst j
          have hkData := Finset.mem_filter.mp hk
          have hkOdd : Odd k := hkData.2.2.1
          have hkThree : 3 ≤ k := hkData.2.1
          have heven : Even (k - 1) := by
            rcases hkOdd with ⟨r, hr⟩
            use r
            omega
          exact (hx (hjx ▸
            (chessEven_simpleRandomWalk_iff omega (k - 1)).mpr heven)).elim
        · subst j
          exact ⟨hk, hjx⟩
      · subst j
        have hTodd : Odd (T + 1) := hpartial.2.1
        have hTeven : Even T := by
          rcases hTodd with ⟨r, hr⟩
          use r
          omega
        exact (hx (hjx ▸
          (chessEven_simpleRandomWalk_iff omega T).mpr hTeven)).elim
    · rintro ⟨hj, hjx⟩
      exact ⟨Or.inl ⟨j, hj, Or.inr rfl⟩, hjx⟩
  · rw [if_neg hpartial, Finset.union_empty]
    simp only [Finset.mem_filter, Finset.mem_biUnion,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨k, hk, hjk⟩, hjx⟩
      rcases hjk with hjk | hjk
      · subst j
        have hkData := Finset.mem_filter.mp hk
        have hkOdd : Odd k := hkData.2.2.1
        have hkThree : 3 ≤ k := hkData.2.1
        have heven : Even (k - 1) := by
          rcases hkOdd with ⟨r, hr⟩
          use r
          omega
        exact (hx (hjx ▸
          (chessEven_simpleRandomWalk_iff omega (k - 1)).mpr heven)).elim
      · subst j
        exact ⟨hk, hjx⟩
    · rintro ⟨hj, hjx⟩
      exact ⟨⟨j, hj, Or.inr rfl⟩, hjx⟩

/-- Translating an odd checkerboard site by the first primed step produces
an even site in the shifted walk. -/
theorem chessEven_primedRelativeSite_of_not_chessEven
    (first : Direction) (x : Site) (hx : ¬ HLOZPairing.chessEven x) :
    HLOZPairing.chessEven (primedRelativeSite first x) := by
  have hsum : primedRelativeSite first x + directionStep first = x := by
    unfold primedRelativeSite
    abel
  have hflip := chessEven_add_directionStep_iff
    (primedRelativeSite first x) first
  rw [hsum] at hflip
  tauto

/-- At odd original times, local time at an odd site is exactly local time
at the translated even site of the swapped one-step suffix.  Only odd
original times (and hence only even shifted times) can visit these sites. -/
theorem localTime_odd_eq_swapped_even_of_chessOdd
    (omega : ℕ → Direction) (R : ℕ) (x : Site)
    (hx : ¬ HLOZPairing.chessEven x) :
    localTime (simpleRandomWalk omega) (2 * R + 1) x =
      localTime
        (simpleRandomWalk
          (swappedIncrementShiftAfter primedOneShift omega)) (2 * R)
        (primedRelativeSite (omega 0) x) := by
  classical
  let eta := swappedIncrementShiftAfter primedOneShift omega
  let y := primedRelativeSite (omega 0) x
  let C : Finset ℕ := (Finset.range (R + 1)).filter fun r ↦
    simpleRandomWalk omega (2 * r + 1) = x
  have hy : HLOZPairing.chessEven y := by
    exact chessEven_primedRelativeSite_of_not_chessEven (omega 0) x hx
  have hrel (r : ℕ) :
      simpleRandomWalk omega (2 * r + 1) = x ↔
        simpleRandomWalk eta (2 * r) = y := by
    rw [simpleRandomWalk_odd_eq_first_add_swapped_even]
    dsimp only [eta, y, primedRelativeSite]
    constructor <;> intro h
    · calc
        simpleRandomWalk
            (swappedIncrementShiftAfter primedOneShift omega) (2 * r) =
            (directionStep (omega 0) + simpleRandomWalk
              (swappedIncrementShiftAfter primedOneShift omega) (2 * r)) -
                directionStep (omega 0) := by abel
        _ = x - directionStep (omega 0) := congrArg
          (fun z : Site ↦ z - directionStep (omega 0)) h
    · calc
        directionStep (omega 0) + simpleRandomWalk
            (swappedIncrementShiftAfter primedOneShift omega) (2 * r) =
            directionStep (omega 0) +
              (x - directionStep (omega 0)) := congrArg
                (fun z : Site ↦ directionStep (omega 0) + z) h
        _ = x := by abel
  have horiginal :
      ((Finset.range (2 * R + 2)).filter fun j ↦
        simpleRandomWalk omega j = x) =
      Finset.image (fun r : ℕ ↦ 2 * r + 1) C := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, C]
    constructor
    · rintro ⟨hj, hjx⟩
      have hjNotEven : ¬ Even j := by
        intro hjEven
        exact hx (hjx ▸ (chessEven_simpleRandomWalk_iff omega j).mpr hjEven)
      rcases Nat.not_even_iff_odd.mp hjNotEven with ⟨r, hr⟩
      refine ⟨r, ?_, hr.symm⟩
      exact ⟨by omega, by simpa only [hr] using hjx⟩
    · rintro ⟨r, ⟨hr, hrx⟩, rfl⟩
      exact ⟨by omega, hrx⟩
  have hshifted :
      ((Finset.range (2 * R + 1)).filter fun j ↦
        simpleRandomWalk eta j = y) =
      Finset.image (fun r : ℕ ↦ 2 * r) C := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, C]
    constructor
    · rintro ⟨hj, hjy⟩
      have hjEven : Even j :=
        (chessEven_simpleRandomWalk_iff eta j).mp (hjy ▸ hy)
      rcases hjEven with ⟨r, hr⟩
      refine ⟨r, ?_, ?_⟩
      · exact ⟨by omega, (hrel r).mpr (by
          rw [show j = 2 * r by omega] at hjy
          exact hjy)⟩
      · omega
    · rintro ⟨r, ⟨hr, hrx⟩, rfl⟩
      exact ⟨by omega, (hrel r).mp hrx⟩
  unfold localTime
  rw [show 2 * R + 1 + 1 = 2 * R + 2 by omega, horiginal]
  change (Finset.image (fun r : ℕ ↦ 2 * r + 1) C).card =
    ((Finset.range (2 * R + 1)).filter fun j ↦
      simpleRandomWalk eta j = y).card
  rw [hshifted]
  have hf : Function.Injective (fun r : ℕ ↦ 2 * r + 1) := by
    intro a b hab
    dsimp at hab
    omega
  have hg : Function.Injective (fun r : ℕ ↦ 2 * r) := by
    intro a b hab
    dsimp at hab
    omega
  rw [Finset.card_image_of_injective _ hf,
    Finset.card_image_of_injective _ hg]

/-- The primed lazy contribution at an odd horizon is the ordinary lazy
contribution of the swapped suffix at the preceding even horizon. -/
theorem primedLazyLocalTime_odd_eq_swapped_even_of_chessOdd
    (omega : ℕ → Direction) (R : ℕ) (x : Site)
    (hx : ¬ HLOZPairing.chessEven x) :
    primedLazyLocalTime (simpleRandomWalk omega) (2 * R + 1) x =
      paperLazyLocalTime
        (simpleRandomWalk
          (swappedIncrementShiftAfter primedOneShift omega)) (2 * R)
        (primedRelativeSite (omega 0) x) := by
  classical
  let eta := swappedIncrementShiftAfter primedOneShift omega
  let y := primedRelativeSite (omega 0) x
  have hy : HLOZPairing.chessEven y :=
    chessEven_primedRelativeSite_of_not_chessEven (omega 0) x hx
  rw [primedLazyLocalTime_eq_primedLazyEndCount_of_chessOdd
    omega (2 * R + 1) x hx]
  rw [paperLazyLocalTime_even_eq_lazyEndCount_of_chessEven eta R y hy]
  rw [show 2 * R + 1 = (2 * R) + 1 by omega,
    primedLazyEndsThrough_succ_eq_image]
  let D := lazyEndsThrough (simpleRandomWalk eta) (2 * R)
  let C : Finset ℕ := D.filter fun j ↦ simpleRandomWalk eta j = y
  have hrel {j : ℕ} (hj : j ∈ D) :
      simpleRandomWalk omega (j + 1) = x ↔
        simpleRandomWalk eta j = y := by
    have hjEven : Even j := (Finset.mem_filter.mp hj).2.2.1
    rcases hjEven with ⟨r, hr⟩
    have hr' : j = 2 * r := by omega
    rw [hr', simpleRandomWalk_odd_eq_first_add_swapped_even]
    dsimp only [eta, y, primedRelativeSite]
    constructor <;> intro h
    · calc
        simpleRandomWalk
            (swappedIncrementShiftAfter primedOneShift omega) (2 * r) =
            (directionStep (omega 0) + simpleRandomWalk
              (swappedIncrementShiftAfter primedOneShift omega) (2 * r)) -
                directionStep (omega 0) := by abel
        _ = x - directionStep (omega 0) := congrArg
          (fun z : Site ↦ z - directionStep (omega 0)) h
    · calc
        directionStep (omega 0) + simpleRandomWalk
            (swappedIncrementShiftAfter primedOneShift omega) (2 * r) =
            directionStep (omega 0) +
              (x - directionStep (omega 0)) := congrArg
                (fun z : Site ↦ directionStep (omega 0) + z) h
        _ = x := by abel
  have hset :
      (D.image Nat.succ).filter
          (fun j ↦ simpleRandomWalk omega j = x) =
        C.image Nat.succ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_image, C]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, hix⟩
      exact ⟨i, ⟨hi, (hrel hi).mp hix⟩, rfl⟩
    · rintro ⟨i, ⟨hi, hiy⟩, rfl⟩
      exact ⟨⟨i, hi, rfl⟩, (hrel hi).mpr hiy⟩
  rw [hset, Finset.card_image_of_injective _ Nat.succ_injective]

/-- Consequently the primed external local time at an odd horizon is the
ordinary external local time of the swapped suffix at the preceding even
horizon. -/
theorem primedExternalLocalTime_odd_eq_swapped_even_of_chessOdd
    (omega : ℕ → Direction) (R : ℕ) (x : Site)
    (hx : ¬ HLOZPairing.chessEven x) :
    primedExternalLocalTime (simpleRandomWalk omega) (2 * R + 1) x =
      paperExternalLocalTime
        (simpleRandomWalk
          (swappedIncrementShiftAfter primedOneShift omega)) (2 * R)
        (primedRelativeSite (omega 0) x) := by
  have hlocal := localTime_odd_eq_swapped_even_of_chessOdd omega R x hx
  have hlazy := primedLazyLocalTime_odd_eq_swapped_even_of_chessOdd
    omega R x hx
  have hprimed := localTime_eq_primedExternal_add_primedLazy
    (simpleRandomWalk omega) (2 * R + 1) x
  have hunprimed := localTime_eq_paperExternal_add_paperLazy
    (simpleRandomWalk
      (swappedIncrementShiftAfter primedOneShift omega)) (2 * R)
    (primedRelativeSite (omega 0) x)
  omega

/-- The primed inverse holding prefix is literally the unprimed inverse
holding prefix of the swapped suffix, with every odd original coordinate
translated to its preceding even shifted coordinate. -/
theorem primedInverseClockHoldingPrefix_eq_swapped
    {q : ℕ} (labels : Fin q → IncrementPair)
    {omega : ℕ → Direction} {N : ℕ}
    (hlabels : terminalPairLabelsThrough
      (swappedIncrementShiftAfter primedOneShift omega) N = List.ofFn labels)
    (x : Site) (hx : ¬ HLOZPairing.chessEven x) (hq : 0 < q)
    (cut : ℕ) :
    primedInverseClockHoldingPrefix (simpleRandomWalk omega)
        (2 * q - 1) cut x =
      inverseClockHoldingPrefix
        (simpleRandomWalk
          (swappedIncrementShiftAfter primedOneShift omega))
        (2 * q - 1) cut (primedRelativeSite (omega 0) x) := by
  have hy : HLOZPairing.chessEven (primedRelativeSite (omega 0) x) :=
    chessEven_primedRelativeSite_of_not_chessEven (omega 0) x hx
  unfold primedInverseClockHoldingPrefix inverseClockHoldingPrefix
  rw [primedExternalVisitIndexList_eq_chronological
    labels hlabels x hx hq]
  rw [externalVisitIndexList_eq_chronologicalExternalIndexList
    labels hlabels (primedRelativeSite (omega 0) x) hy hq]
  rw [← List.map_take, ← List.map_take, List.map_map, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  exact primedHoldingNat_succ_eq_paperHoldingNat omega (2 * i.val)

/-- At a completed pair horizon, the unprimed lazy local time is the sum of
the stopped holding blocks attached to all external bases seen so far,
including the currently active base.  Its block is stopped at `2 * R`, so no
future holding time is inserted. -/
theorem paperLazyLocalTime_even_eq_sum_stoppedBlocks_inclusive
    {q R : ℕ} (labels : Fin q → IncrementPair)
    {omega : ℕ → Direction} {N : ℕ}
    (hlabels : terminalPairLabelsThrough omega N = List.ofFn labels)
    (hRN : R ≤ N) (x : Site) (hx : HLOZPairing.chessEven x) :
    paperLazyLocalTime (simpleRandomWalk omega) (2 * R) x =
      ∑ i ∈ (Finset.range
          ((terminalPairLabelsThrough omega R).length + 1)).filter
            (fun i ↦ fixedExternalBase labels i = x),
        stoppedExcursionBlock (simpleRandomWalk omega) (2 * R) (2 * i) := by
  classical
  let L := (terminalPairLabelsThrough omega R).length
  let D := distinguishedPairIndicesThrough omega R
  let I := (Finset.range (L + 1)).filter fun i ↦ fixedExternalBase labels i = x
  let g : ℕ → ℕ := fun r ↦
    (terminalPairLabelsThrough omega r).length
  have hfiber (i : ℕ) (hi : i ∈ I) :
      ((D.filter fun r ↦ g r = i).card) =
        stoppedExcursionBlock (simpleRandomWalk omega) (2 * R) (2 * i) := by
    rw [stoppedExcursionBlock_even_eq_pairBlock_card]
    apply congrArg Finset.card
    ext r
    simp only [D, g, distinguishedPairIndicesThrough,
      completedPairBlockIndices, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨hrR, hdist⟩, hlen⟩
      exact ⟨hrR, hdist, by omega⟩
    · rintro ⟨hrR, hdist, hlen⟩
      exact ⟨⟨hrR, hdist⟩, by omega⟩
  have hmem (r : ℕ) (hr : r ∈ D) :
      g r ∈ I ↔ simpleRandomWalk omega (2 * r + 2) = x := by
    have hrData := Finset.mem_filter.mp hr
    have hrR : r < R := Finset.mem_range.mp hrData.1
    have hdist : incrementPair r omega = distinguishedIncrementPair := hrData.2
    have hrN : r ≤ N := by omega
    have hwalkr : simpleRandomWalk omega (2 * r) =
        fixedExternalBase labels (g r) := by
      simpa only [g] using
        simpleRandomWalk_even_eq_fixedExternalBase_of_realized
          labels hlabels r hrN
    have hend : simpleRandomWalk omega (2 * r + 2) =
        simpleRandomWalk omega (2 * r) := by
      rw [show 2 * r + 2 = 2 * (r + 1) by omega,
        simpleRandomWalk_pair_succ]
      have h0 := congrFun hdist 0
      have h1 := congrFun hdist 1
      simp only [incrementPair_zero] at h0
      simp only [incrementPair_one] at h1
      rw [h0, h1, add_assoc, distinguishedPair_step_sum_zero]
      ext <;> simp
    have hstep := terminalPairLabelsThrough_succ_length omega r
    rw [if_pos hdist] at hstep
    have hle : g r ≤ L := by
      dsimp only [g, L]
      exact terminalPairLabelsThrough_length_mono omega (by omega)
    constructor
    · intro hgi
      have hbase : fixedExternalBase labels (g r) = x :=
        (Finset.mem_filter.mp hgi).2
      rw [hend, hwalkr, hbase]
    · intro hendx
      have hbase : fixedExternalBase labels (g r) = x := by
        rw [← hwalkr, ← hend]
        exact hendx
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), hbase⟩
  have hpartition :
      ∑ i ∈ I, (D.filter fun r ↦ g r = i).card =
        (D.filter fun r ↦ simpleRandomWalk omega (2 * r + 2) = x).card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter D I g]
    apply congrArg Finset.card
    ext r
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hr, hgi⟩
      exact ⟨hr, (hmem r hr).mp hgi⟩
    · rintro ⟨hr, hrx⟩
      exact ⟨hr, (hmem r hr).mpr hrx⟩
  have hends :
      ((lazyEndsThrough (simpleRandomWalk omega) (2 * R)).filter
        fun k ↦ simpleRandomWalk omega k = x).card =
        (D.filter fun r ↦ simpleRandomWalk omega (2 * r + 2) = x).card := by
    rw [lazyEndsThrough_even_eq_image]
    let f : ℕ → ℕ := fun r ↦ 2 * r + 2
    have hinj : Function.Injective f := by
      intro a b hab
      dsimp only [f] at hab
      omega
    have hset :
        (D.image f).filter
            (fun k ↦ simpleRandomWalk omega k = x) =
          (D.filter fun r ↦ simpleRandomWalk omega (2 * r + 2) = x).image f := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨r, hr, rfl⟩, hrx⟩
        exact ⟨r, ⟨hr, hrx⟩, rfl⟩
      · rintro ⟨r, ⟨hr, hrx⟩, rfl⟩
        exact ⟨⟨r, hr, rfl⟩, hrx⟩
    rw [hset, Finset.card_image_of_injective _ hinj]
  rw [paperLazyLocalTime_eq_completed_add_terminalIndicator,
    if_neg (by
      simp only [not_isLazyEnd_odd (simpleRandomWalk omega) R, false_and,
        not_false_eq_true]), Nat.add_zero,
    completedLazyLocalTime_eq_lazyEndCount_of_chessEven omega (2 * R) x hx,
    hends, ← hpartition]
  apply Finset.sum_congr rfl
  intro i hi
  exact hfiber i hi

/-- Away from the active base, the inclusive formula reduces to the earlier
external bases. -/
theorem paperLazyLocalTime_even_eq_sum_stoppedBlocks
    {q R : ℕ} (labels : Fin q → IncrementPair)
    {omega : ℕ → Direction} {N : ℕ}
    (hlabels : terminalPairLabelsThrough omega N = List.ofFn labels)
    (hRN : R ≤ N) (x : Site) (hx : HLOZPairing.chessEven x)
    (hcurrent : simpleRandomWalk omega (2 * R) ≠ x) :
    paperLazyLocalTime (simpleRandomWalk omega) (2 * R) x =
      ∑ i ∈ (Finset.range
          (terminalPairLabelsThrough omega R).length).filter
            (fun i ↦ fixedExternalBase labels i = x),
        stoppedExcursionBlock (simpleRandomWalk omega) (2 * R) (2 * i) := by
  let L := (terminalPairLabelsThrough omega R).length
  have hwalkR : simpleRandomWalk omega (2 * R) =
      fixedExternalBase labels L := by
    simpa only [L] using
      simpleRandomWalk_even_eq_fixedExternalBase_of_realized
        labels hlabels R hRN
  have hlast : fixedExternalBase labels L ≠ x := by
    intro h
    apply hcurrent
    rw [hwalkR, h]
  have hfilter :
      (Finset.range (L + 1)).filter (fun i ↦ fixedExternalBase labels i = x) =
        (Finset.range L).filter (fun i ↦ fixedExternalBase labels i = x) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hi, hix⟩
      refine ⟨?_, hix⟩
      by_contra hnot
      have : i = L := by omega
      subst i
      exact hlast hix
    · rintro ⟨hi, hix⟩
      exact ⟨by omega, hix⟩
  have h := paperLazyLocalTime_even_eq_sum_stoppedBlocks_inclusive
    labels hlabels hRN x hx
  simpa only [L, hfilter] using h

/-- At the same completed pair horizon, the stopped external local time is
the number of fixed external bases through the active base, hence the
inclusive range `0,…,L`. -/
theorem paperExternalLocalTime_even_eq_fixedBase_count_inclusive
    {q R : ℕ} (labels : Fin q → IncrementPair)
    {omega : ℕ → Direction} {N : ℕ}
    (hlabels : terminalPairLabelsThrough omega N = List.ofFn labels)
    (hRN : R ≤ N) (x : Site) (hx : HLOZPairing.chessEven x) :
    paperExternalLocalTime (simpleRandomWalk omega) (2 * R) x =
      ((Finset.range ((terminalPairLabelsThrough omega R).length + 1)).filter
        fun i ↦ fixedExternalBase labels i = x).card := by
  classical
  let L := (terminalPairLabelsThrough omega R).length
  let A := (retainedTimes (simpleRandomWalk omega) (2 * R)).filter
    fun j ↦ simpleRandomWalk omega j = x
  let f : ℕ → ℕ := fun j ↦
    (terminalPairLabelsThrough omega (j / 2)).length
  let I := (Finset.range (L + 1)).filter fun i ↦ fixedExternalBase labels i = x
  have hfmem : ∀ j ∈ A, f j ∈ I := by
    intro j hj
    rw [Finset.mem_filter] at hj
    have hjEven : Even j :=
      (chessEven_simpleRandomWalk_iff omega j).mp (hj.2 ▸ hx)
    rcases hjEven with ⟨r, hr⟩
    have hrR : r ≤ R := by
      rw [retainedTimes, Finset.mem_sdiff, Finset.mem_range] at hj
      omega
    have hrN : r ≤ N := hrR.trans hRN
    have hwalkr := simpleRandomWalk_even_eq_fixedExternalBase_of_realized
      labels hlabels r hrN
    have hbase : fixedExternalBase labels (f j) = x := by
      dsimp only [f]
      rw [show j / 2 = r by omega, ← hwalkr]
      simpa [show j = 2 * r by omega] using hj.2
    have hle : f j ≤ L := by
      dsimp only [f, L]
      exact terminalPairLabelsThrough_length_mono omega (by omega)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), hbase⟩
  have hfinj : Set.InjOn f A := by
    intro j₁ hj₁ j₂ hj₂ heq
    change j₁ ∈ A at hj₁
    change j₂ ∈ A at hj₂
    rw [Finset.mem_filter] at hj₁ hj₂
    have hj₁Even : Even j₁ :=
      (chessEven_simpleRandomWalk_iff omega j₁).mp (hj₁.2 ▸ hx)
    have hj₂Even : Even j₂ :=
      (chessEven_simpleRandomWalk_iff omega j₂).mp (hj₂.2 ▸ hx)
    rcases hj₁Even with ⟨r₁, hr₁⟩
    rcases hj₂Even with ⟨r₂, hr₂⟩
    have hr₁R : r₁ ≤ R := by
      rw [retainedTimes, Finset.mem_sdiff, Finset.mem_range] at hj₁
      omega
    have hr₂R : r₂ ≤ R := by
      rw [retainedTimes, Finset.mem_sdiff, Finset.mem_range] at hj₂
      omega
    have hstrict : ∀ {j a b : ℕ},
        j ∈ retainedTimes (simpleRandomWalk omega) (2 * R) →
        j = 2 * b → a < b → b ≤ R →
        (terminalPairLabelsThrough omega a).length <
          (terminalPairLabelsThrough omega b).length := by
      intro j a b hjRet hjb hab hbR
      subst j
      have hbpos : 0 < b := by omega
      have hnotRemoved := (Finset.mem_sdiff.mp hjRet).2
      have hnondist : incrementPair (b - 1) omega ≠
          distinguishedIncrementPair := by
        intro hdist
        apply hnotRemoved
        rw [lazyRemovedTimes, Finset.mem_union]
        left
        apply Finset.mem_biUnion.mpr
        refine ⟨2 * b, ?_, ?_⟩
        · rw [lazyEndsThrough, Finset.mem_filter]
          refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
          rw [show 2 * b = 2 * (b - 1) + 2 by omega,
            isLazyEnd_simpleRandomWalk_pair_iff]
          exact hdist
        · simp
      have hstep := terminalPairLabelsThrough_succ_length omega (b - 1)
      rw [if_neg hnondist, Nat.sub_add_cancel hbpos] at hstep
      have hmono := terminalPairLabelsThrough_length_mono omega
        (show a ≤ b - 1 by omega)
      omega
    have hrEq : r₁ = r₂ := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have := hstrict hj₂.1 (by omega) hlt hr₂R
        dsimp only [f] at heq
        rw [show j₁ / 2 = r₁ by omega,
          show j₂ / 2 = r₂ by omega] at heq
        omega
      · have := hstrict hj₁.1 (by omega) hgt hr₁R
        dsimp only [f] at heq
        rw [show j₁ / 2 = r₁ by omega,
          show j₂ / 2 = r₂ by omega] at heq
        omega
    omega
  have hsurj : ∀ i ∈ I, ∃ j ∈ A, f j = i := by
    intro i hi
    have hiData := Finset.mem_filter.mp hi
    have hiL : i ≤ L := by
      have := Finset.mem_range.mp hiData.1
      omega
    by_cases hi0 : i = 0
    · subst i
      refine ⟨0, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨?_, ?_⟩
        · rw [retainedTimes_even_eq_explicit]
          simp [explicitRetainedPairTimes]
        · change (0 : Site) = x
          exact hiData.2
      · simp [f, terminalPairLabelsThrough]
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
      have hnL : n < L := by omega
      have hex : ∃ a, n <
          (terminalPairLabelsThrough omega (a + 1)).length :=
        exists_terminalPairIndex_of_lt_length omega (by
          dsimp only [L] at hnL
          exact hnL)
      let r := terminalPairIndex omega n
      have hcount := terminalPairIndex_count omega n hex
      have hrR : r < R := by
        have hRpos : 1 ≤ R := by
          by_contra hRzero
          have hReq : R = 0 := by omega
          subst R
          simp [L, terminalPairLabelsThrough] at hnL
        have hRsub : R - 1 + 1 = R := Nat.sub_add_cancel hRpos
        have hbound : n <
            (terminalPairLabelsThrough omega (R - 1 + 1)).length := by
          rw [hRsub]
          simpa only [L] using hnL
        have hmin := terminalPairIndex_minimal omega n (R - 1) hbound
        dsimp only [r]
        omega
      let j := 2 * r + 2
      have hjstate : simpleRandomWalk omega j =
          fixedExternalBase labels (n + 1) := by
        have hstate := externalStateAt_even_eq_fixedExternalBase
          labels hlabels (n + 1) (by
            have hprefix := terminalPairLabelsThrough_prefix omega hRN
            have hLq : L ≤ q := by
              dsimp only [L]
              simpa only [hlabels, List.length_ofFn] using hprefix.length_le
            omega)
        have hinv := externalInverseMinus_even_succ omega n hex
        unfold externalStateAt at hstate
        rw [hinv] at hstate
        simpa only [j, r] using hstate
      refine ⟨j, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨?_, ?_⟩
        · rw [retainedTimes_even_eq_explicit]
          rw [explicitRetainedPairTimes, Finset.mem_union]
          right
          apply Finset.mem_biUnion.mpr
          refine ⟨r, Finset.mem_range.mpr hrR, ?_⟩
          rw [if_neg hcount.2]
          simp [j]
        · rw [hjstate]
          exact hiData.2
      · dsimp only [f, j]
        rw [show (2 * r + 2) / 2 = r + 1 by omega,
          terminalPairLabelsThrough_succ_length, if_neg hcount.2,
          hcount.1]
  have himage : A.image f = I := by
    ext i
    constructor
    · intro hi
      rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
      exact hfmem j hj
    · intro hi
      rcases hsurj i hi with ⟨j, hj, hji⟩
      exact Finset.mem_image.mpr ⟨j, hj, hji⟩
  have hcard : A.card = I.card := by
    calc
      A.card = (A.image f).card :=
        (Finset.card_image_iff.mpr (by
          intro a ha b hb hab
          exact hfinj ha hb hab)).symm
      _ = I.card := congrArg Finset.card himage
  simpa only [paperExternalLocalTime, A, I, L] using hcard

/-- Away from the active base, the inclusive external count has no last
term and reduces to the earlier fixed bases. -/
theorem paperExternalLocalTime_even_eq_fixedBase_count
    {q R : ℕ} (labels : Fin q → IncrementPair)
    {omega : ℕ → Direction} {N : ℕ}
    (hlabels : terminalPairLabelsThrough omega N = List.ofFn labels)
    (hRN : R ≤ N) (x : Site) (hx : HLOZPairing.chessEven x)
    (hcurrent : simpleRandomWalk omega (2 * R) ≠ x) :
    paperExternalLocalTime (simpleRandomWalk omega) (2 * R) x =
      ((Finset.range (terminalPairLabelsThrough omega R).length).filter
        fun i ↦ fixedExternalBase labels i = x).card := by
  let L := (terminalPairLabelsThrough omega R).length
  have hwalkR : simpleRandomWalk omega (2 * R) =
      fixedExternalBase labels L := by
    simpa only [L] using
      simpleRandomWalk_even_eq_fixedExternalBase_of_realized
        labels hlabels R hRN
  have hlast : fixedExternalBase labels L ≠ x := by
    intro h
    apply hcurrent
    rw [hwalkR, h]
  have hfilter :
      (Finset.range (L + 1)).filter (fun i ↦ fixedExternalBase labels i = x) =
        (Finset.range L).filter (fun i ↦ fixedExternalBase labels i = x) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hi, hix⟩
      refine ⟨?_, hix⟩
      by_contra hnot
      have : i = L := by omega
      subst i
      exact hlast hix
    · rintro ⟨hi, hix⟩
      exact ⟨by omega, hix⟩
  have h := paperExternalLocalTime_even_eq_fixedBase_count_inclusive
    labels hlabels hRN x hx
  simpa only [L, hfilter] using h

/-- Consequently, at an even horizon and away from its endpoint, the lazy
local time is exactly the inverse-clock holding prefix cut at the stopped
external local time.  This is the chronological identification missing from
the earlier source interface. -/
theorem paperLazyLocalTime_even_eq_inverseClockHoldingPrefix
    {q R : ℕ} (labels : Fin q → IncrementPair) (hq : 0 < q)
    {omega : ℕ → Direction} {N : ℕ}
    (hlabels : terminalPairLabelsThrough omega N = List.ofFn labels)
    (hRN : R ≤ N) (x : Site) (hx : HLOZPairing.chessEven x)
    (hcurrent : simpleRandomWalk omega (2 * R) ≠ x) :
    paperLazyLocalTime (simpleRandomWalk omega) (2 * R) x =
      inverseClockHoldingPrefix (simpleRandomWalk omega) (2 * q - 1)
        (paperExternalLocalTime (simpleRandomWalk omega) (2 * R) x) x := by
  classical
  let L := (terminalPairLabelsThrough omega R).length
  let P : ℕ → Prop := fun i ↦ fixedExternalBase labels i = x
  let small := (List.range L).filter P
  let big := (List.range q).filter P
  let I := (Finset.range L).filter P
  have hLq : L ≤ q := by
    have hprefix := terminalPairLabelsThrough_prefix omega hRN
    dsimp only [L]
    simpa only [hlabels, List.length_ofFn] using hprefix.length_le
  have hrangePrefix : List.range L <+: List.range q := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hLq
    rw [List.range_add]
    exact List.prefix_append _ _
  have hprefix : small <+: big := by
    exact List.IsPrefix.filter P hrangePrefix
  have hsmallNodup : small.Nodup := by
    dsimp only [small]
    apply List.Nodup.filter
    exact List.nodup_range
  have hsmallFinset : small.toFinset = I := by
    ext i
    simp [small, I, P]
  have hsmallLength : small.length = I.card := by
    rw [← hsmallFinset]
    exact (List.toFinset_card_of_nodup hsmallNodup).symm
  have htake : big.take I.card = small := by
    rw [← hsmallLength]
    exact (List.prefix_iff_eq_take.mp hprefix).symm
  have hext := paperExternalLocalTime_even_eq_fixedBase_count
    labels hlabels hRN x hx hcurrent
  have hlazy := paperLazyLocalTime_even_eq_sum_stoppedBlocks
    labels hlabels hRN x hx hcurrent
  rw [hext]
  change paperLazyLocalTime (simpleRandomWalk omega) (2 * R) x =
    inverseClockHoldingPrefix (simpleRandomWalk omega) (2 * q - 1) I.card x
  rw [hlazy]
  change (∑ i ∈ I,
      stoppedExcursionBlock (simpleRandomWalk omega) (2 * R) (2 * i)) = _
  unfold inverseClockHoldingPrefix
  rw [externalVisitIndexList_eq_fixedExternalBases labels hlabels x hx hq]
  change ∑ i ∈ I,
      stoppedExcursionBlock (simpleRandomWalk omega) (2 * R) (2 * i) =
    (((big.map fun i ↦ 2 * i).take I.card).map
      (paperHoldingNat (simpleRandomWalk omega))).sum
  rw [← List.map_take, htake, List.map_map]
  change (∑ i ∈ I,
      stoppedExcursionBlock (simpleRandomWalk omega) (2 * R) (2 * i)) =
    (small.map fun i ↦ paperHoldingNat (simpleRandomWalk omega) (2 * i)).sum
  have hlistSum :
      (small.map fun i ↦ paperHoldingNat (simpleRandomWalk omega) (2 * i)).sum =
        ∑ i ∈ I, paperHoldingNat (simpleRandomWalk omega) (2 * i) := by
    rw [← hsmallFinset]
    exact (List.sum_toFinset
      (fun i ↦ paperHoldingNat (simpleRandomWalk omega) (2 * i))
      hsmallNodup).symm
  rw [hlistSum]
  apply Finset.sum_congr rfl
  intro i hi
  symm
  apply paperHoldingNat_even_eq_stoppedExcursionBlock omega R i
  exact Finset.mem_range.mp (Finset.mem_filter.mp hi).1

/-- Stopping an excursion block later can only add completed excursions. -/
theorem stoppedExcursionBlock_mono {s : Path} {T U q : ℕ} (hTU : T ≤ U) :
    stoppedExcursionBlock s T q ≤ stoppedExcursionBlock s U q := by
  unfold stoppedExcursionBlock
  apply Finset.card_le_card
  intro k hk
  rw [mem_stoppedExcursionEnds_iff] at hk ⊢
  exact ⟨hk.1, hk.2.1.trans hTU, hk.2.2⟩

/-- If the fixed label vector extends strictly beyond the current pair, its
full holding coordinates dominate every stopped holding block seen so far.
Consequently the inverse prefix cut at the stopped external count contains
the stopped lazy local time even at the active base. -/
theorem paperLazyLocalTime_even_le_inverseClockHoldingPrefix_of_lt_pair
    {q R : ℕ} (labels : Fin q → IncrementPair) (hq : 0 < q)
    {omega : ℕ → Direction} {N : ℕ}
    (hlabels : terminalPairLabelsThrough omega N = List.ofFn labels)
    (hRN : R ≤ N) (hRq : R < q)
    (x : Site) (hx : HLOZPairing.chessEven x) :
    paperLazyLocalTime (simpleRandomWalk omega) (2 * R) x ≤
      inverseClockHoldingPrefix (simpleRandomWalk omega) (2 * q - 1)
        (paperExternalLocalTime (simpleRandomWalk omega) (2 * R) x) x := by
  classical
  let L := (terminalPairLabelsThrough omega R).length
  let P : ℕ → Prop := fun i ↦ fixedExternalBase labels i = x
  let small := (List.range (L + 1)).filter P
  let big := (List.range q).filter P
  let I := (Finset.range (L + 1)).filter P
  have hLR : L ≤ R := by
    have hcount := distinguished_add_terminal_count omega R
    dsimp only [L]
    omega
  have hLq : L + 1 ≤ q := by omega
  have hrangePrefix : List.range (L + 1) <+: List.range q := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hLq
    rw [hd]
    conv_rhs => rw [List.range_add]
    exact List.prefix_append _ _
  have hprefix : small <+: big := List.IsPrefix.filter P hrangePrefix
  have hsmallNodup : small.Nodup := by
    dsimp only [small]
    exact List.Nodup.filter P List.nodup_range
  have hsmallFinset : small.toFinset = I := by
    ext i
    simp [small, I, P]
  have hsmallLength : small.length = I.card := by
    rw [← hsmallFinset]
    exact (List.toFinset_card_of_nodup hsmallNodup).symm
  have htake : big.take I.card = small := by
    rw [← hsmallLength]
    exact (List.prefix_iff_eq_take.mp hprefix).symm
  have hext := paperExternalLocalTime_even_eq_fixedBase_count_inclusive
    labels hlabels hRN x hx
  have hlazy := paperLazyLocalTime_even_eq_sum_stoppedBlocks_inclusive
    labels hlabels hRN x hx
  rw [hext, hlazy]
  change (∑ i ∈ I,
      stoppedExcursionBlock (simpleRandomWalk omega) (2 * R) (2 * i)) ≤
    inverseClockHoldingPrefix (simpleRandomWalk omega) (2 * q - 1) I.card x
  unfold inverseClockHoldingPrefix
  rw [externalVisitIndexList_eq_fixedExternalBases labels hlabels x hx hq]
  change (∑ i ∈ I,
      stoppedExcursionBlock (simpleRandomWalk omega) (2 * R) (2 * i)) ≤
    (((big.map fun i ↦ 2 * i).take I.card).map
      (paperHoldingNat (simpleRandomWalk omega))).sum
  rw [← List.map_take, htake, List.map_map]
  change (∑ i ∈ I,
      stoppedExcursionBlock (simpleRandomWalk omega) (2 * R) (2 * i)) ≤
    (small.map fun i ↦ paperHoldingNat (simpleRandomWalk omega) (2 * i)).sum
  have hlistSum :
      (small.map fun i ↦ paperHoldingNat (simpleRandomWalk omega) (2 * i)).sum =
        ∑ i ∈ I, paperHoldingNat (simpleRandomWalk omega) (2 * i) := by
    rw [← hsmallFinset]
    exact (List.sum_toFinset
      (fun i ↦ paperHoldingNat (simpleRandomWalk omega) (2 * i))
      hsmallNodup).symm
  rw [hlistSum]
  apply Finset.sum_le_sum
  intro i hi
  have hiq : i < q :=
    (Finset.mem_range.mp (Finset.mem_filter.mp hi).1).trans_le hLq
  have hfuture : paperHoldingNat (simpleRandomWalk omega) (2 * i) =
      stoppedExcursionBlock (simpleRandomWalk omega) (2 * N) (2 * i) := by
    apply paperHoldingNat_even_eq_stoppedExcursionBlock
    rw [hlabels, List.length_ofFn]
    exact hiq
  exact (stoppedExcursionBlock_mono (show 2 * R ≤ 2 * N by omega)).trans_eq
    hfuture.symm

/-- Conversely, a strict cut below the stopped external count only sees
completed holding blocks.  When the current even endpoint is `x`, it is the
last element of the inclusive fixed-base list; the strict cut therefore
removes precisely the potentially unfinished active block. -/
theorem inverseClockHoldingPrefix_le_paperLazyLocalTime_even_of_cut_lt
    {q R cut : ℕ} (labels : Fin q → IncrementPair) (hq : 0 < q)
    {omega : ℕ → Direction} {N : ℕ}
    (hlabels : terminalPairLabelsThrough omega N = List.ofFn labels)
    (hRN : R ≤ N) (hRq : R < q)
    (x : Site) (hx : HLOZPairing.chessEven x)
    (hcurrent : simpleRandomWalk omega (2 * R) = x)
    (hcut : cut < paperExternalLocalTime (simpleRandomWalk omega) (2 * R) x) :
    inverseClockHoldingPrefix (simpleRandomWalk omega) (2 * q - 1) cut x ≤
      paperLazyLocalTime (simpleRandomWalk omega) (2 * R) x := by
  classical
  let L := (terminalPairLabelsThrough omega R).length
  let P : ℕ → Prop := fun i ↦ fixedExternalBase labels i = x
  let prior := (List.range L).filter P
  let small := (List.range (L + 1)).filter P
  let big := (List.range q).filter P
  let I := (Finset.range (L + 1)).filter P
  have hLR : L ≤ R := by
    have hcount := distinguished_add_terminal_count omega R
    dsimp only [L]
    omega
  have hLq : L + 1 ≤ q := by omega
  have hbaseL : fixedExternalBase labels L = x := by
    have hwalk := simpleRandomWalk_even_eq_fixedExternalBase_of_realized
      labels hlabels R hRN
    exact (by simpa only [L] using hwalk.symm.trans hcurrent)
  have hsmallEq : small = prior ++ [L] := by
    dsimp only [small, prior]
    rw [List.range_succ, List.filter_append]
    simp [P, hbaseL]
  have hrangePrefix : List.range (L + 1) <+: List.range q := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hLq
    rw [hd]
    conv_rhs => rw [List.range_add]
    exact List.prefix_append _ _
  have hsmallPrefix : small <+: big := List.IsPrefix.filter P hrangePrefix
  have hpriorPrefix : prior <+: big := by
    exact (hsmallEq ▸ List.prefix_append prior [L]).trans hsmallPrefix
  have hsmallNodup : small.Nodup := by
    dsimp only [small]
    exact List.Nodup.filter P List.nodup_range
  have hpriorNodup : prior.Nodup := by
    dsimp only [prior]
    exact List.Nodup.filter P List.nodup_range
  have hsmallFinset : small.toFinset = I := by
    ext i
    simp [small, I, P]
  have hsmallLength : small.length = I.card := by
    rw [← hsmallFinset]
    exact (List.toFinset_card_of_nodup hsmallNodup).symm
  have hext := paperExternalLocalTime_even_eq_fixedBase_count_inclusive
    labels hlabels hRN x hx
  have hcutPrior : cut ≤ prior.length := by
    rw [hext] at hcut
    rw [← hsmallLength, hsmallEq] at hcut
    simp only [List.length_append, List.length_singleton] at hcut
    omega
  have htakePrior : big.take prior.length = prior :=
    (List.prefix_iff_eq_take.mp hpriorPrefix).symm
  have htake : big.take cut = prior.take cut := by
    calc
      big.take cut = (big.take prior.length).take cut := by
        rw [List.take_take, min_eq_left hcutPrior]
      _ = prior.take cut := by rw [htakePrior]
  have hlazy := paperLazyLocalTime_even_eq_sum_stoppedBlocks_inclusive
    labels hlabels hRN x hx
  rw [hlazy]
  unfold inverseClockHoldingPrefix
  rw [externalVisitIndexList_eq_fixedExternalBases labels hlabels x hx hq]
  change (((big.map fun i ↦ 2 * i).take cut).map
      (paperHoldingNat (simpleRandomWalk omega))).sum ≤
    ∑ i ∈ I, stoppedExcursionBlock (simpleRandomWalk omega) (2 * R) (2 * i)
  rw [← List.map_take, htake, List.map_map]
  let J := (prior.take cut).toFinset
  have htakeNodup : (prior.take cut).Nodup := hpriorNodup.take
  have hsum :
      ((prior.take cut).map fun i ↦
          paperHoldingNat (simpleRandomWalk omega) (2 * i)).sum =
        ∑ i ∈ J, stoppedExcursionBlock
          (simpleRandomWalk omega) (2 * R) (2 * i) := by
    calc
      ((prior.take cut).map fun i ↦
          paperHoldingNat (simpleRandomWalk omega) (2 * i)).sum =
          ∑ i ∈ J, paperHoldingNat (simpleRandomWalk omega) (2 * i) := by
        change ((prior.take cut).map fun i ↦
            paperHoldingNat (simpleRandomWalk omega) (2 * i)).sum =
          ∑ i ∈ (prior.take cut).toFinset,
            paperHoldingNat (simpleRandomWalk omega) (2 * i)
        exact (List.sum_toFinset _ htakeNodup).symm
      _ = ∑ i ∈ J, stoppedExcursionBlock
          (simpleRandomWalk omega) (2 * R) (2 * i) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply paperHoldingNat_even_eq_stoppedExcursionBlock omega R i
        have hiList : i ∈ prior.take cut := by
          simpa only [J, List.mem_toFinset] using hi
        have hiPrior := List.mem_of_mem_take hiList
        simp only [prior, List.mem_filter, List.mem_range] at hiPrior
        exact hiPrior.1
  change ((prior.take cut).map (fun i ↦
      paperHoldingNat (simpleRandomWalk omega) (2 * i))).sum ≤
    ∑ i ∈ I, stoppedExcursionBlock (simpleRandomWalk omega) (2 * R) (2 * i)
  rw [hsum]
  apply Finset.sum_le_sum_of_subset
  intro i hi
  have hiList : i ∈ prior.take cut := by
    simpa only [J, List.mem_toFinset] using hi
  have hiPrior := List.mem_of_mem_take hiList
  simp only [prior, List.mem_filter, List.mem_range] at hiPrior
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨hiPrior.1.trans_le (Nat.le_succ L), of_decide_eq_true hiPrior.2⟩

/-- Odd primed horizons satisfy the same exact stopped-lazy/prefix identity
after transporting to the swapped suffix. -/
theorem primedLazyLocalTime_odd_eq_inverseClockHoldingPrefix
    {q R : ℕ} (labels : Fin q → IncrementPair)
    (hnondistinguished : ∀ i, labels i ≠ distinguishedIncrementPair)
    (hq : 0 < q) {omega : ℕ → Direction}
    (homega : swappedIncrementShiftAfter primedOneShift omega ∈
      firstPairExternalPathEqFrom 0
        (externalPathFromLabels (List.ofFn labels)))
    (hR : R ≤ q) (x : Site) (hx : ¬ HLOZPairing.chessEven x)
    (hcurrent : simpleRandomWalk omega (2 * R + 1) ≠ x) :
    primedLazyLocalTime (simpleRandomWalk omega) (2 * R + 1) x =
      primedInverseClockHoldingPrefix (simpleRandomWalk omega) (2 * q - 1)
        (primedExternalLocalTime (simpleRandomWalk omega) (2 * R + 1) x) x := by
  let eta := swappedIncrementShiftAfter primedOneShift omega
  let y := primedRelativeSite (omega 0) x
  obtain ⟨N, hlabels⟩ := realized_terminalPairLabelsThrough
    labels hnondistinguished homega
  have hqN : q ≤ N := by
    have hcount := distinguished_add_terminal_count eta N
    rw [hlabels, List.length_ofFn] at hcount
    omega
  have hRN : R ≤ N := hR.trans hqN
  have hy : HLOZPairing.chessEven y :=
    chessEven_primedRelativeSite_of_not_chessEven (omega 0) x hx
  have hshiftCurrent : simpleRandomWalk eta (2 * R) ≠ y := by
    intro h
    apply hcurrent
    rw [simpleRandomWalk_odd_eq_first_add_swapped_even]
    dsimp only [eta, y, primedRelativeSite] at h ⊢
    rw [h]
    abel
  have hlazy := primedLazyLocalTime_odd_eq_swapped_even_of_chessOdd
    omega R x hx
  have hext := primedExternalLocalTime_odd_eq_swapped_even_of_chessOdd
    omega R x hx
  have hunprimed := paperLazyLocalTime_even_eq_inverseClockHoldingPrefix
    labels hq hlabels hRN y hy hshiftCurrent
  calc
    primedLazyLocalTime (simpleRandomWalk omega) (2 * R + 1) x =
        paperLazyLocalTime (simpleRandomWalk eta) (2 * R) y := hlazy
    _ = inverseClockHoldingPrefix (simpleRandomWalk eta) (2 * q - 1)
        (paperExternalLocalTime (simpleRandomWalk eta) (2 * R) y) y := hunprimed
    _ = inverseClockHoldingPrefix (simpleRandomWalk eta) (2 * q - 1)
        (primedExternalLocalTime (simpleRandomWalk omega) (2 * R + 1) x) y := by
          rw [hext]
    _ = primedInverseClockHoldingPrefix (simpleRandomWalk omega) (2 * q - 1)
        (primedExternalLocalTime (simpleRandomWalk omega) (2 * R + 1) x) x :=
      (primedInverseClockHoldingPrefix_eq_swapped labels hlabels x hx hq _).symm

/-- Before the last fixed primed pair, the possibly active odd terminal
block is bounded by its completed shifted holding coordinate. -/
theorem primedLazyLocalTime_odd_le_inverseClockHoldingPrefix_of_lt_pair
    {q R : ℕ} (labels : Fin q → IncrementPair)
    (hnondistinguished : ∀ i, labels i ≠ distinguishedIncrementPair)
    (hq : 0 < q) {omega : ℕ → Direction}
    (homega : swappedIncrementShiftAfter primedOneShift omega ∈
      firstPairExternalPathEqFrom 0
        (externalPathFromLabels (List.ofFn labels)))
    (hR : R < q) (x : Site) (hx : ¬ HLOZPairing.chessEven x) :
    primedLazyLocalTime (simpleRandomWalk omega) (2 * R + 1) x ≤
      primedInverseClockHoldingPrefix (simpleRandomWalk omega) (2 * q - 1)
        (primedExternalLocalTime (simpleRandomWalk omega) (2 * R + 1) x) x := by
  let eta := swappedIncrementShiftAfter primedOneShift omega
  let y := primedRelativeSite (omega 0) x
  obtain ⟨N, hlabels⟩ := realized_terminalPairLabelsThrough
    labels hnondistinguished homega
  have hqN : q ≤ N := by
    have hcount := distinguished_add_terminal_count eta N
    rw [hlabels, List.length_ofFn] at hcount
    omega
  have hy : HLOZPairing.chessEven y :=
    chessEven_primedRelativeSite_of_not_chessEven (omega 0) x hx
  have hlazy := primedLazyLocalTime_odd_eq_swapped_even_of_chessOdd
    omega R x hx
  have hext := primedExternalLocalTime_odd_eq_swapped_even_of_chessOdd
    omega R x hx
  have hunprimed := paperLazyLocalTime_even_le_inverseClockHoldingPrefix_of_lt_pair
    labels hq hlabels (hR.le.trans hqN) hR y hy
  calc
    primedLazyLocalTime (simpleRandomWalk omega) (2 * R + 1) x =
        paperLazyLocalTime (simpleRandomWalk eta) (2 * R) y := hlazy
    _ ≤ inverseClockHoldingPrefix (simpleRandomWalk eta) (2 * q - 1)
        (paperExternalLocalTime (simpleRandomWalk eta) (2 * R) y) y := hunprimed
    _ = inverseClockHoldingPrefix (simpleRandomWalk eta) (2 * q - 1)
        (primedExternalLocalTime (simpleRandomWalk omega) (2 * R + 1) x) y := by
          rw [hext]
    _ = primedInverseClockHoldingPrefix (simpleRandomWalk omega) (2 * q - 1)
        (primedExternalLocalTime (simpleRandomWalk omega) (2 * R + 1) x) x :=
      (primedInverseClockHoldingPrefix_eq_swapped labels hlabels x hx hq _).symm

/-- A strict cut below the stopped primed external count excludes the active
odd terminal block, so every selected holding coordinate is already complete
at the odd horizon. -/
theorem primedInverseClockHoldingPrefix_le_primedLazyLocalTime_odd_of_cut_lt
    {q R cut : ℕ} (labels : Fin q → IncrementPair)
    (hnondistinguished : ∀ i, labels i ≠ distinguishedIncrementPair)
    (hq : 0 < q) {omega : ℕ → Direction}
    (homega : swappedIncrementShiftAfter primedOneShift omega ∈
      firstPairExternalPathEqFrom 0
        (externalPathFromLabels (List.ofFn labels)))
    (hR : R < q) (x : Site) (hx : ¬ HLOZPairing.chessEven x)
    (hcurrent : simpleRandomWalk omega (2 * R + 1) = x)
    (hcut : cut <
      primedExternalLocalTime (simpleRandomWalk omega) (2 * R + 1) x) :
    primedInverseClockHoldingPrefix (simpleRandomWalk omega) (2 * q - 1) cut x ≤
      primedLazyLocalTime (simpleRandomWalk omega) (2 * R + 1) x := by
  let eta := swappedIncrementShiftAfter primedOneShift omega
  let y := primedRelativeSite (omega 0) x
  obtain ⟨N, hlabels⟩ := realized_terminalPairLabelsThrough
    labels hnondistinguished homega
  have hqN : q ≤ N := by
    have hcount := distinguished_add_terminal_count eta N
    rw [hlabels, List.length_ofFn] at hcount
    omega
  have hy : HLOZPairing.chessEven y :=
    chessEven_primedRelativeSite_of_not_chessEven (omega 0) x hx
  have hshiftCurrent : simpleRandomWalk eta (2 * R) = y := by
    rw [simpleRandomWalk_odd_eq_first_add_swapped_even] at hcurrent
    dsimp only [eta, y, primedRelativeSite] at hcurrent ⊢
    rw [← hcurrent]
    abel
  have hlazy := primedLazyLocalTime_odd_eq_swapped_even_of_chessOdd
    omega R x hx
  have hext := primedExternalLocalTime_odd_eq_swapped_even_of_chessOdd
    omega R x hx
  have hcutShift : cut <
      paperExternalLocalTime (simpleRandomWalk eta) (2 * R) y := by
    rwa [hext] at hcut
  have hunprimed := inverseClockHoldingPrefix_le_paperLazyLocalTime_even_of_cut_lt
    labels hq hlabels (hR.le.trans hqN) hR y hy hshiftCurrent hcutShift
  calc
    primedInverseClockHoldingPrefix (simpleRandomWalk omega) (2 * q - 1) cut x =
        inverseClockHoldingPrefix (simpleRandomWalk eta) (2 * q - 1) cut y :=
      primedInverseClockHoldingPrefix_eq_swapped labels hlabels x hx hq cut
    _ ≤ paperLazyLocalTime (simpleRandomWalk eta) (2 * R) y := hunprimed
    _ = primedLazyLocalTime (simpleRandomWalk omega) (2 * R + 1) x := hlazy.symm

/-- The canonical label count also controls an original-time horizon.  The
only possible vertex beyond `2*q-1` is the endpoint at `2*q`; excluding that
endpoint from `x` makes the external local time stable across the final
step. -/
theorem paperExternalLocalTime_le_canonicalFixedProfile
    {n T : ℕ} (hn : 0 < n)
    (v : FixedExternalLabels
      (HLOZExternalUpper.externalLabelCount n))
    {s : Path}
    (hs : s ∈ externalPathWalkAtom
      (List.ofFn (fixedIncrementLabels v)))
    (x : Site) (hx : HLOZPairing.chessEven x)
    (hT : T ≤ n) (hendpoint : s T ≠ x) :
    paperExternalLocalTime s T x ≤
      inverseClockProfile s
        (2 * HLOZExternalUpper.externalLabelCount n - 1) x := by
  let q := HLOZExternalUpper.externalLabelCount n
  have hq : 0 < q := by
    dsimp only [q, HLOZExternalUpper.externalLabelCount]
    omega
  have hfit := HLOZExternalUpper.external_time_fits_labelCount n
  change paperExternalLocalTime s T x ≤
    inverseClockProfile s (2 * q - 1) x
  by_cases hTq : T ≤ 2 * q - 1
  · exact paperExternalLocalTime_le_fixedProfile_of_le v hq hs x hx hTq
  · have hTeq : T = 2 * q := by omega
    have hendpoint' : s (2 * q) ≠ x := by
      rw [hTeq] at hendpoint
      exact hendpoint
    have hstable : paperExternalLocalTime s T x =
        paperExternalLocalTime s (2 * q - 1) x := by
      rw [hTeq]
      have hnew : s ((2 * q - 1) + 1) ≠ x := by
        simpa [show (2 * q - 1) + 1 = 2 * q by omega] using hendpoint'
      simpa [show (2 * q - 1) + 1 = 2 * q by omega] using
        paperExternalLocalTime_succ_eq_of_ne s (2 * q - 1) x hnew
    rw [hstable]
    exact paperExternalLocalTime_le_fixedProfile_of_le v hq hs x hx le_rfl

/-- Before the last shifted fixed label, every retained visit to an odd site
is represented by a distinct odd coordinate of the primed inverse profile. -/
theorem primedExternalLocalTime_odd_le_fixedProfile_of_lt
    {q R : ℕ} (first : Direction) (v : FixedExternalLabels q) (hR : R < q)
    {s : Path}
    (hs : s ∈ primedExternalPathWalkAtom first
      (fixedIncrementLabels v))
    (x : Site) (hx : ¬ HLOZPairing.chessEven x) :
    primedExternalLocalTime s (2 * R + 1) x ≤
      primedInverseClockProfile s (2 * q - 1) x := by
  classical
  rcases hs with ⟨omega, homega, rfl⟩
  let eta := swappedIncrementShiftAfter primedOneShift omega
  obtain ⟨N, hlabels⟩ := realized_terminalPairLabelsThrough
    (fixedIncrementLabels v) (fixedIncrementLabels_nondistinguished v)
      homega.2
  have hqN : q ≤ N := by
    have hcount := distinguished_add_terminal_count eta N
    rw [hlabels, List.length_ofFn] at hcount
    omega
  rw [primedInverseClockProfile_eq_chronological_length
    (fixedIncrementLabels v) hlabels x hx (by omega)]
  let A := (primedRetainedTimes (simpleRandomWalk omega) (2 * R + 1)).filter
    fun j ↦ simpleRandomWalk omega j = x
  let f : ℕ → ℕ := fun j ↦
    (terminalPairLabelsThrough eta ((j - 1) / 2)).length
  let B := (Finset.range q).filter fun i ↦
    fixedExternalBase (fixedIncrementLabels v) i =
      primedRelativeSite (omega 0) x
  have hfmem : ∀ j ∈ A, f j ∈ B := by
    intro j hj
    rw [Finset.mem_filter] at hj
    have hjNotEven : ¬ Even j := by
      intro hjEven
      exact hx (hj.2 ▸ (chessEven_simpleRandomWalk_iff omega j).mpr hjEven)
    rcases Nat.not_even_iff_odd.mp hjNotEven with ⟨r, hr⟩
    have hrR : r ≤ R := by
      rw [primedRetainedTimes, Finset.mem_sdiff, Finset.mem_range] at hj
      omega
    have hrN : r ≤ N := hrR.trans (hR.le.trans hqN)
    have hetaWalk := simpleRandomWalk_even_eq_fixedExternalBase_of_realized
      (fixedIncrementLabels v) hlabels r hrN
    have hwalk := simpleRandomWalk_odd_eq_first_add_swapped_even omega r
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, ?_⟩
    · dsimp only [f]
      have hcount := distinguished_add_terminal_count eta r
      rw [show (j - 1) / 2 = r by omega]
      omega
    · dsimp only [f]
      rw [show (j - 1) / 2 = r by omega]
      have hjr : simpleRandomWalk omega (2 * r + 1) = x := by
        rw [← hr]
        exact hj.2
      rw [hetaWalk] at hwalk
      unfold primedRelativeSite
      rw [hjr] at hwalk
      dsimp only [eta]
      rw [hwalk]
      abel
  have hfinj : Set.InjOn f A := by
    intro j₁ hj₁ j₂ hj₂ heq
    change j₁ ∈ A at hj₁
    change j₂ ∈ A at hj₂
    rw [Finset.mem_filter] at hj₁ hj₂
    have hj₁NotEven : ¬ Even j₁ := by
      intro hjEven
      exact hx (hj₁.2 ▸ (chessEven_simpleRandomWalk_iff omega j₁).mpr hjEven)
    have hj₂NotEven : ¬ Even j₂ := by
      intro hjEven
      exact hx (hj₂.2 ▸ (chessEven_simpleRandomWalk_iff omega j₂).mpr hjEven)
    rcases Nat.not_even_iff_odd.mp hj₁NotEven with ⟨r₁, hr₁⟩
    rcases Nat.not_even_iff_odd.mp hj₂NotEven with ⟨r₂, hr₂⟩
    have hr₁R : r₁ ≤ R := by
      rw [primedRetainedTimes, Finset.mem_sdiff, Finset.mem_range] at hj₁
      omega
    have hr₂R : r₂ ≤ R := by
      rw [primedRetainedTimes, Finset.mem_sdiff, Finset.mem_range] at hj₂
      omega
    have hstrict : ∀ {j a b : ℕ},
        j ∈ primedRetainedTimes (simpleRandomWalk omega) (2 * R + 1) →
        j = 2 * b + 1 → a < b → b ≤ R →
        (terminalPairLabelsThrough eta a).length <
          (terminalPairLabelsThrough eta b).length := by
      intro j a b hjRet hjb hab hbR
      subst j
      have hbpos : 0 < b := by omega
      have hnotRemoved := (Finset.mem_sdiff.mp hjRet).2
      have hnondist : incrementPair (b - 1) eta ≠
          distinguishedIncrementPair := by
        intro hdist
        apply hnotRemoved
        rw [primedRemovedTimes, Finset.mem_union]
        left
        apply Finset.mem_biUnion.mpr
        refine ⟨2 * b + 1, ?_, ?_⟩
        · rw [primedLazyEndsThrough, Finset.mem_filter]
          refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
          rw [show 2 * b + 1 = 2 * (b - 1) + 3 by omega,
            isPrimedLazyEnd_simpleRandomWalk_pair_iff]
          exact hdist
        · simp only [Finset.mem_insert, Finset.mem_singleton]
          simp
      have hstep := terminalPairLabelsThrough_succ_length eta (b - 1)
      rw [if_neg hnondist, Nat.sub_add_cancel hbpos] at hstep
      have hmono := terminalPairLabelsThrough_length_mono eta
        (show a ≤ b - 1 by omega)
      omega
    have hrEq : r₁ = r₂ := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have := hstrict hj₂.1 (by omega) hlt hr₂R
        dsimp only [f] at heq
        rw [show (j₁ - 1) / 2 = r₁ by omega,
          show (j₂ - 1) / 2 = r₂ by omega] at heq
        omega
      · have := hstrict hj₁.1 (by omega) hgt hr₁R
        dsimp only [f] at heq
        rw [show (j₁ - 1) / 2 = r₁ by omega,
          show (j₂ - 1) / 2 = r₂ by omega] at heq
        omega
    omega
  have hcard : A.card ≤ B.card := by
    calc
      A.card = (A.image f).card :=
        (Finset.card_image_iff.mpr (by
          intro a ha b hb hab
          exact hfinj ha hb hab)).symm
      _ ≤ B.card := Finset.card_le_card (by
        intro i hi
        rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
        exact hfmem j hj)
  have hB : B.card =
      (chronologicalExternalIndexList (fixedIncrementLabels v)
        (primedRelativeSite (omega 0) x)).length := by
    have hmap := congrArg List.length
      (map_chronologicalExternalIndexList (fixedIncrementLabels v)
        (primedRelativeSite (omega 0) x))
    let P : ℕ → Prop := fun i ↦
      fixedExternalBase (fixedIncrementLabels v) i =
        primedRelativeSite (omega 0) x
    calc
      B.card = List.countP (fun i ↦ decide (P i)) (List.range q) := by
        dsimp only [B, P]
        have hrange : (List.range q).toFinset = Finset.range q := by
          ext i
          simp
        rw [← hrange]
        exact (List.nodup_range (n := q)).card_eq_countP
          (P := fun i : ℕ ↦
            fixedExternalBase (fixedIncrementLabels v) i =
              primedRelativeSite (omega 0) x)
      _ = ((List.range q).filter P).length :=
        List.countP_eq_length_filter
      _ = (chronologicalExternalIndexList (fixedIncrementLabels v)
          (primedRelativeSite (omega 0) x)).length := by
        dsimp only [P]
        simpa only [List.length_map] using hmap.symm
  simpa only [primedExternalLocalTime, A, hB] using hcard

/-- A realized shifted fixed-label atom controls the primed external local
time at every original horizon represented by its `q` labels. -/
theorem primedExternalLocalTime_le_fixedProfile_of_le
    {q T : ℕ} (first : Direction) (v : FixedExternalLabels q) (hq : 0 < q)
    {s : Path}
    (hs : s ∈ primedExternalPathWalkAtom first
      (fixedIncrementLabels v))
    (x : Site) (hx : ¬ HLOZPairing.chessEven x)
    (hT : T ≤ 2 * q) :
    primedExternalLocalTime s T x ≤
      primedInverseClockProfile s (2 * q - 1) x := by
  rcases hs with ⟨omega, homega, rfl⟩
  obtain ⟨R, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  have hmono : primedExternalLocalTime (simpleRandomWalk omega) T x ≤
      primedExternalLocalTime (simpleRandomWalk omega) (2 * R + 2) x :=
    primedExternalLocalTime_mono (simpleRandomWalk omega) x (by omega)
  have hparity := primedExternalLocalTime_even_eq_odd_of_chessOdd
    omega R x hx
  have hfixed := primedExternalLocalTime_odd_le_fixedProfile_of_lt
    first v (show R < R + 1 by omega)
      (show simpleRandomWalk omega ∈ primedExternalPathWalkAtom first
        (fixedIncrementLabels v) from ⟨omega, homega, rfl⟩)
      x hx
  exact hmono.trans (hparity.le.trans hfixed)

/-- The canonical label count controls the primed external local time at
every original horizon up to the Proposition-4.4 cutoff. -/
theorem primedExternalLocalTime_le_canonicalFixedProfile
    {n T : ℕ} (hn : 0 < n) (first : Direction)
    (v : FixedExternalLabels
      (HLOZExternalUpper.externalLabelCount n))
    {s : Path}
    (hs : s ∈ primedExternalPathWalkAtom first
      (fixedIncrementLabels v))
    (x : Site) (hx : ¬ HLOZPairing.chessEven x)
    (hT : T ≤ n) :
    primedExternalLocalTime s T x ≤
      primedInverseClockProfile s
        (2 * HLOZExternalUpper.externalLabelCount n - 1) x := by
  let q := HLOZExternalUpper.externalLabelCount n
  have hq : 0 < q := by
    dsimp only [q, HLOZExternalUpper.externalLabelCount]
    omega
  have hfit := HLOZExternalUpper.external_time_fits_labelCount n
  apply primedExternalLocalTime_le_fixedProfile_of_le first v hq hs x hx
  omega

/-- On a realized canonical label atom, every even site in a stopped
`Theta` half below the level-`m` creation endpoint is one of the canonical
fixed external bases.  Only the deterministic horizon bound is needed;
the final level-`m` endpoint is excluded by the strict `< m` condition in
`stoppedThetaHalfSites`. -/
theorem xEastUnprimedThetaSite_mem_fixedSites_of_time_le
    (m k : ℕ)
    (v : FixedExternalLabels
      (HLOZExternalUpper.externalLabelCount (prop44Psi m)))
    {s : Path} {x : Site} (hm : 0 < m) (hk : 0 < k)
    (hatom : s ∈ externalPathWalkAtom
      (List.ofFn (fixedIncrementLabels v)))
    (hTle : directCreationTime m k s ≤ prop44Psi m)
    (hx : x ∈ stoppedThetaHalfSites paperUnprimedProfile
      HLOZPairing.chessEven false 10 s m k ∪
        stoppedThetaHalfSites paperUnprimedProfile
          HLOZPairing.chessEven true 10 s m k) :
    x ∈ xEastUnprimedFixedSites v := by
  classical
  rcases hatom with ⟨omega, homega, rfl⟩
  obtain ⟨N, hlabels⟩ := realized_terminalPairLabelsThrough
    (fixedIncrementLabels v) (fixedIncrementLabels_nondistinguished v) homega
  rcases Finset.mem_union.mp hx with hx | hx <;>
    simp only [stoppedThetaHalfSites, Finset.mem_filter] at hx
  all_goals
    rcases hx with ⟨hxvisited, hfinite, hxEven, _hxLower, hxUpper, _hxExternal⟩
    rcases Finset.mem_image.mp hxvisited with ⟨j, hj, hjx⟩
    have hxlt : localTime (simpleRandomWalk omega)
        (directCreationTime m k (simpleRandomWalk omega)) x < m := by
      exact_mod_cast hxUpper
    have hjlt : j < directCreationTime m k (simpleRandomWalk omega) := by
      have hjle : j ≤ directCreationTime m k (simpleRandomWalk omega) := by
        have hj' := Finset.mem_range.mp hj
        omega
      apply lt_of_le_of_ne hjle
      intro hjeq
      have hcreated := levelCreationSite_localTime_eq
        (simpleRandomWalk omega) m k hm hk hfinite
      have hxendpoint : x = levelCreationSite (simpleRandomWalk omega) m k := by
        rw [levelCreationSite, ← hjx]
        congr
      have hcreated' : localTime (simpleRandomWalk omega)
          (directCreationTime m k (simpleRandomWalk omega))
            (levelCreationSite (simpleRandomWalk omega) m k) = m := by
        simpa only [directCreationTime] using hcreated
      rw [hxendpoint, hcreated'] at hxlt
      exact (Nat.lt_irrefl m) hxlt
    have hjEven : Even j :=
      (chessEven_simpleRandomWalk_iff omega j).mp (hjx ▸ hxEven)
    rcases hjEven with ⟨r, hr⟩
    have hjtwo : j = 2 * r := by omega
    have hrPsi : 2 * r < prop44Psi m := by omega
    have hrq : r < HLOZExternalUpper.externalLabelCount (prop44Psi m) := by
      unfold HLOZExternalUpper.externalLabelCount
      omega
    have hqN : HLOZExternalUpper.externalLabelCount (prop44Psi m) ≤ N := by
      have hcount := distinguished_add_terminal_count omega N
      rw [hlabels, List.length_ofFn] at hcount
      omega
    have hwalk := simpleRandomWalk_even_eq_fixedExternalBase_of_realized
      (fixedIncrementLabels v) hlabels r (hrq.le.trans hqN)
    apply Finset.mem_image.mpr
    refine ⟨⟨(terminalPairLabelsThrough omega r).length, ?_⟩,
      Finset.mem_univ _, ?_⟩
    · have hcount := distinguished_add_terminal_count omega r
      omega
    · rw [← hwalk, ← hjtwo, hjx]

theorem fixedExternalBase_chessEven {q : ℕ}
    (labels : Fin q → IncrementPair) (i : Fin q) :
    HLOZPairing.chessEven (fixedExternalBase labels i.1) := by
  have haux : ∀ n, n < q →
      HLOZPairing.chessEven (fixedExternalBase labels n) := by
    intro n
    induction n with
    | zero =>
        intro _
        exact ⟨0, by simp [HLOZPairing.chessEven]⟩
    | succ n ih =>
        intro hn
        rw [fixedExternalBase_succ labels (by omega),
          chessEven_pairEndpoint_iff]
        exact ih (by omega)
  exact haux i.1 i.2

theorem xEastUnprimedFixedSites_even {q : ℕ}
    (v : FixedExternalLabels q) (x : Site)
    (hx : x ∈ xEastUnprimedFixedSites v) :
    HLOZPairing.chessEven x := by
  rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
  exact fixedExternalBase_chessEven (fixedIncrementLabels v) i

theorem card_xEastUnprimedFixedSites_le {q : ℕ}
    (v : FixedExternalLabels q) :
    (xEastUnprimedFixedSites v).card ≤ q := by
  calc
    (xEastUnprimedFixedSites v).card ≤
        (Finset.univ : Finset (Fin q)).card := Finset.card_image_le
    _ = q := Fintype.card_fin q

theorem xEastUnprimed_minus_capacity {m q : ℕ}
    (v : FixedExternalLabels q) (x : Site) :
    intervalDotIndex m (sourceBandLowerNat m)
        (xEastEncodedProfile (fixedIncrementLabels v)) x ≤
      (chronologicalExternalIndexList (fixedIncrementLabels v) x).length := by
  exact min_le_left _ _

theorem xEastUnprimed_plus_capacity {m q : ℕ}
    (v : FixedExternalLabels q) (x : Site)
    (hx : x ∈ intervalPlusCandidates (xEastUnprimedFixedSites v) m m
      (xEastEncodedProfile (fixedIncrementLabels v))) :
    intervalHighCut m m ≤
      (chronologicalExternalIndexList (fixedIncrementLabels v) x).length := by
  exact (Finset.mem_filter.mp hx).2

theorem xEastUnprimedFixedAtom_inverseProfile
    {q : ℕ} (v : FixedExternalLabels q) (hq : 0 < q)
    {s : Path}
    (hs : s ∈ externalPathWalkAtom
      (List.ofFn (fixedIncrementLabels v)))
    (x : Site) (hx : x ∈ xEastUnprimedFixedSites v) :
    inverseClockProfile s (2 * q - 1) x =
      xEastEncodedProfile (fixedIncrementLabels v) x := by
  rcases hs with ⟨omega, homega, rfl⟩
  obtain ⟨N, hlabels⟩ := realized_terminalPairLabelsThrough
    (fixedIncrementLabels v) (fixedIncrementLabels_nondistinguished v) homega
  exact inverseClockProfile_eq_chronological_length
    (fixedIncrementLabels v) hlabels x
      (xEastUnprimedFixedSites_even v x hx) hq

/-- Literal good fixed-label vectors: precisely the Proposition-4.4
candidate-cardinality inequality.  The horizon-cardinality inequality is
instead a deterministic consequence of the fixed depth `q`. -/
def XEastUnprimedFixedLabelGood (m : ℕ) {q : ℕ}
    (v : FixedExternalLabels q) : Prop :=
  ((sourceProp44Candidates (xEastUnprimedFixedSites v) m
      (xEastEncodedProfile (fixedIncrementLabels v))).card : ℝ) ≤
      Real.exp (16 * sourceRate m)

noncomputable def xEastUnprimedGoodFixedAtoms (m q : ℕ) :
    Finset (FixedExternalLabels q) := by
  classical
  exact Finset.univ.filter (XEastUnprimedFixedLabelGood m)

theorem mem_xEastUnprimedGoodFixedAtoms_iff {m q : ℕ}
    {v : FixedExternalLabels q} :
    v ∈ xEastUnprimedGoodFixedAtoms m q ↔
      XEastUnprimedFixedLabelGood m v := by
  simp [xEastUnprimedGoodFixedAtoms]

theorem twice_externalLabelCount_sub_one_le (n : ℕ) :
    2 * HLOZExternalUpper.externalLabelCount n - 1 ≤ n := by
  unfold HLOZExternalUpper.externalLabelCount
  omega

theorem externalLabelCount_prop44Psi_pos (m : ℕ) :
    0 < HLOZExternalUpper.externalLabelCount (prop44Psi m) := by
  have hpsi : 0 < prop44Psi m := by
    rw [HLOZProp44ExternalChain.prop44Psi_eq_nearCriticalHorizon]
    exact HLOZNearCriticalBridge.nearCriticalHorizon_pos m
  unfold HLOZExternalUpper.externalLabelCount
  omega

/-- A bad fixed label vector is a genuine Proposition-4.4 many-site
configuration of the infinite iid external path. -/
theorem sourceProp44Candidates_subset_external_many
    (m : ℕ)
    (v : FixedExternalLabels
      (HLOZExternalUpper.externalLabelCount (prop44Psi m)))
    (labels : ℕ → HLOZExternalChain.ExternalPairLabel)
    (hprefix : ∀ i : Fin (HLOZExternalUpper.externalLabelCount (prop44Psi m)),
      labels i = v i) :
    sourceProp44Candidates (xEastUnprimedFixedSites v) m
        (xEastEncodedProfile (fixedIncrementLabels v)) ⊆
      evenSitesAtLeastReal (HLOZExternalChain.externalWalk labels)
        (prop44Psi m) (prop44SiteThreshold m) := by
  classical
  intro x hx
  rw [sourceProp44Candidates, Finset.mem_filter] at hx
  rw [evenSitesAtLeastReal, Finset.mem_filter,
    sitesAtLeastReal, Finset.mem_filter]
  have hprofile := xEastEncodedProfile_le_externalWalk_localTime_of_prefix
    v labels hprefix (twice_externalLabelCount_sub_one_le (prop44Psi m)) x
  refine ⟨⟨?_, ?_⟩, xEastUnprimedFixedSites_even v x hx.1⟩
  · rcases Finset.mem_image.mp hx.1 with ⟨i, _hi, rfl⟩
    rw [visitedSites]
    apply Finset.mem_image.mpr
    refine ⟨2 * i.1, ?_, ?_⟩
    · rw [Finset.mem_range]
      have hqpos : 0 < HLOZExternalUpper.externalLabelCount (prop44Psi m) := by
        unfold HLOZExternalUpper.externalLabelCount
        have := prop44Psi_pos m
        omega
      have hn := twice_externalLabelCount_sub_one_le (prop44Psi m)
      omega
    · exact (fixedExternalBase_eq_externalWalk_of_prefix v labels hprefix
        i.1 i.2.le).symm
  · have hxthreshold : prop44SiteThreshold m ≤
        (xEastEncodedProfile (fixedIncrementLabels v) x : ℝ) := by
      simpa [sourceProp44Threshold, prop44SiteThreshold] using hx.2
    exact hxthreshold.trans (by exact_mod_cast hprofile)

noncomputable def xEastUnprimedBadVector (m q : ℕ)
    (v : FixedExternalLabels q) : Prop :=
  ¬ XEastUnprimedFixedLabelGood m v

theorem selectedLabelEvent_xEastUnprimedBadVector_subset (m : ℕ) :
    HLOZExternalChain.selectedLabelEvent
        (xEastUnprimedBadVector m
          (HLOZExternalUpper.externalLabelCount (prop44Psi m))) ⊆
      {labels |
        Real.exp (16 * (m : ℝ) ^ prop44RateExponent) <
          ((evenSitesAtLeastReal (HLOZExternalChain.externalWalk labels)
            (prop44Psi m) (prop44SiteThreshold m)).card : ℝ)} := by
  classical
  intro labels hlabels
  simp only [HLOZExternalChain.selectedLabelEvent, Set.mem_iUnion] at hlabels
  obtain ⟨v, hv⟩ := hlabels
  by_cases hbad : xEastUnprimedBadVector m
      (HLOZExternalUpper.externalLabelCount (prop44Psi m)) v
  · simp only [hbad, if_true] at hv
    have hsubset := sourceProp44Candidates_subset_external_many m v labels hv
    have hcard := Finset.card_le_card hsubset
    have hvbad : Real.exp (16 * sourceRate m) <
        ((sourceProp44Candidates (xEastUnprimedFixedSites v) m
          (xEastEncodedProfile (fixedIncrementLabels v))).card : ℝ) := by
      exact lt_of_not_ge hbad
    have hrate : sourceRate m = (m : ℝ) ^ prop44RateExponent := by
      rw [sourceRate, sourceRateExponent_eq, prop44RateExponent_eq]
    rw [← hrate]
    exact hvbad.trans_le (by exact_mod_cast hcard)
  · simp [hbad] at hv

noncomputable def unprimedFixedAtomUnion (q : ℕ) : Set Path :=
  ⋃ v : FixedExternalLabels q,
    externalPathWalkAtom (List.ofFn (fixedIncrementLabels v))

theorem pairwise_unprimedFixedAtoms (q : ℕ) :
    (Set.univ : Set (FixedExternalLabels q)).PairwiseDisjoint
      (fun v ↦ externalPathWalkAtom
        (List.ofFn (fixedIncrementLabels v))) := by
  intro v _ w _ hvw
  change Disjoint
    (externalPathWalkAtom (List.ofFn (fixedIncrementLabels v)))
    (externalPathWalkAtom (List.ofFn (fixedIncrementLabels w)))
  rw [Set.disjoint_left]
  rintro s ⟨omega, hωv, rfl⟩ ⟨eta, hωw, hs⟩
  have hωeta : omega = eta := simpleRandomWalk_injective hs.symm
  subst eta
  apply hvw
  have htv : omega ∈ firstPairTerminalLabelsEqFrom 0
      (List.ofFn (fixedIncrementLabels v)) := by
    rwa [← firstPairExternalPathEqFrom_reconstructed]
  have htw : omega ∈ firstPairTerminalLabelsEqFrom 0
      (List.ofFn (fixedIncrementLabels w)) := by
    rwa [← firstPairExternalPathEqFrom_reconstructed]
  change omega ∈ firstPairTerminalLabelsEqFrom 0
      (List.ofFn fun i ↦ (v i : IncrementPair)) at htv
  change omega ∈ firstPairTerminalLabelsEqFrom 0
      (List.ofFn fun i ↦ (w i : IncrementPair)) at htw
  have heq := HLOZExternalChain.firstPairTerminalLabels_unique 0
    (fun p hp ↦ by
      rw [List.mem_ofFn] at hp
      obtain ⟨i, rfl⟩ := hp
      exact (v i).property)
    (fun p hp ↦ by
      rw [List.mem_ofFn] at hp
      obtain ⟨i, rfl⟩ := hp
      exact (w i).property)
    (by simp) htv htw
  have hfun : fixedIncrementLabels v = fixedIncrementLabels w :=
    List.ofFn_injective heq
  funext i
  exact Subtype.ext (congrFun hfun i)

theorem preimage_unprimedFixedAtomUnion (q : ℕ) :
    simpleRandomWalk ⁻¹' unprimedFixedAtomUnion q =
      HLOZExternalChain.selectedOriginalEvent
        (fun _ : FixedExternalLabels q ↦ True) := by
  classical
  ext omega
  simp only [unprimedFixedAtomUnion, Set.mem_preimage, Set.mem_iUnion,
    HLOZExternalChain.selectedOriginalEvent, if_true,
    HLOZExternalChain.vectorLabels]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    have hv' : omega ∈ simpleRandomWalk ⁻¹'
        externalPathWalkAtom (List.ofFn (fixedIncrementLabels v)) := hv
    rw [preimage_externalPathWalkAtom,
      firstPairExternalPathEqFrom_reconstructed] at hv'
    exact hv'
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    have hv' : omega ∈ firstPairExternalPathEqFrom 0
        (externalPathFromLabels (List.ofFn (fixedIncrementLabels v))) := by
      rwa [firstPairExternalPathEqFrom_reconstructed]
    have : omega ∈ simpleRandomWalk ⁻¹'
        externalPathWalkAtom (List.ofFn (fixedIncrementLabels v)) := by
      rwa [preimage_externalPathWalkAtom]
    exact this

theorem incrementLaw_selectedOriginalEvent_true (q : ℕ) :
    incrementLaw
      (HLOZExternalChain.selectedOriginalEvent
        (fun _ : FixedExternalLabels q ↦ True)) = 1 := by
  rw [HLOZExternalChain.measure_selectedOriginalEvent]
  unfold HLOZExternalChain.selectedMass
  rw [tsum_fintype]
  have hcard : Fintype.card HLOZExternalChain.ExternalPairLabel = 15 := by
    decide
  simp only [if_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, hcard, nsmul_eq_mul]
  rw [Nat.cast_pow, ← mul_pow]
  change (((15 : ENNReal) * (15 : ENNReal)⁻¹) ^ q) = 1
  rw [ENNReal.mul_inv_cancel] <;> norm_num

theorem simpleRandomWalkLaw_unprimedFixedAtomUnion (q : ℕ) :
    simpleRandomWalkLaw (unprimedFixedAtomUnion q) = 1 := by
  rw [simpleRandomWalkLaw]
  change (Measure.map simpleRandomWalk incrementLaw)
    (unprimedFixedAtomUnion q) = 1
  have hmeas : MeasurableSet (unprimedFixedAtomUnion q) :=
    MeasurableSet.iUnion fun v ↦
      measurableSet_externalPathWalkAtom
        (List.ofFn (fixedIncrementLabels v))
  rw [Measure.map_apply measurable_simpleRandomWalk hmeas,
    preimage_unprimedFixedAtomUnion,
    incrementLaw_selectedOriginalEvent_true]

theorem simpleRandomWalkLaw_unprimedFixedAtomUnion_compl (q : ℕ) :
    simpleRandomWalkLaw (unprimedFixedAtomUnion q)ᶜ = 0 := by
  have hmeas : MeasurableSet (unprimedFixedAtomUnion q) :=
    MeasurableSet.iUnion fun v ↦
      measurableSet_externalPathWalkAtom
        (List.ofFn (fixedIncrementLabels v))
  rw [measure_compl hmeas (measure_ne_top _ _),
    simpleRandomWalkLaw_unprimedFixedAtomUnion, measure_univ]
  simp

noncomputable def xEastUnprimedBadLabelUnion (m q : ℕ) : Set Path :=
  ⋃ v : FixedExternalLabels q,
    if v ∈ xEastUnprimedGoodFixedAtoms m q then ∅
    else externalPathWalkAtom (List.ofFn (fixedIncrementLabels v))

theorem preimage_xEastUnprimedBadLabelUnion (m q : ℕ) :
    simpleRandomWalk ⁻¹' xEastUnprimedBadLabelUnion m q =
      HLOZExternalChain.selectedOriginalEvent
        (xEastUnprimedBadVector m q) := by
  classical
  ext omega
  simp only [xEastUnprimedBadLabelUnion, Set.mem_preimage,
    Set.mem_iUnion, HLOZExternalChain.selectedOriginalEvent,
    HLOZExternalChain.vectorLabels]
  constructor
  · rintro ⟨v, hv⟩
    by_cases hgood : v ∈ xEastUnprimedGoodFixedAtoms m q
    · simp [hgood] at hv
    · refine ⟨v, ?_⟩
      have hbad : xEastUnprimedBadVector m q v := by
        rwa [xEastUnprimedBadVector,
          ← mem_xEastUnprimedGoodFixedAtoms_iff]
      simp only [hbad, if_true]
      simp only [hgood, if_false] at hv
      have hv' : omega ∈ simpleRandomWalk ⁻¹'
          externalPathWalkAtom
            (List.ofFn (fixedIncrementLabels v)) := hv
      rw [preimage_externalPathWalkAtom,
        firstPairExternalPathEqFrom_reconstructed] at hv'
      exact hv'
  · rintro ⟨v, hv⟩
    by_cases hbad : xEastUnprimedBadVector m q v
    · simp only [hbad, if_true] at hv
      refine ⟨v, ?_⟩
      have hgood : v ∉ xEastUnprimedGoodFixedAtoms m q := by
        rwa [mem_xEastUnprimedGoodFixedAtoms_iff]
      simp only [hgood, if_false]
      have hv' : omega ∈ firstPairExternalPathEqFrom 0
          (externalPathFromLabels
            (List.ofFn (fixedIncrementLabels v))) := by
        rwa [firstPairExternalPathEqFrom_reconstructed]
      have : omega ∈ simpleRandomWalk ⁻¹'
          externalPathWalkAtom
            (List.ofFn (fixedIncrementLabels v)) := by
        rwa [preimage_externalPathWalkAtom]
      exact this
    · simp [hbad] at hv

theorem simpleRandomWalkLaw_xEastUnprimedBadLabelUnion_eq_selectedMass
    (m q : ℕ) :
    simpleRandomWalkLaw (xEastUnprimedBadLabelUnion m q) =
      HLOZExternalChain.externalLabelLaw
        (HLOZExternalChain.selectedLabelEvent
          (xEastUnprimedBadVector m q)) := by
  have hmeas : MeasurableSet (xEastUnprimedBadLabelUnion m q) := by
    apply MeasurableSet.iUnion
    intro v
    by_cases hv : v ∈ xEastUnprimedGoodFixedAtoms m q
    · simp [hv]
    · simpa [hv] using
        measurableSet_externalPathWalkAtom
          (List.ofFn (fixedIncrementLabels v))
  rw [simpleRandomWalkLaw, Measure.map_apply measurable_simpleRandomWalk hmeas,
    preimage_xEastUnprimedBadLabelUnion,
    HLOZExternalChain.measure_selected_events_eq]

theorem simpleRandomWalkLaw_xEastUnprimedBadLabelUnion_le_prop44 (m : ℕ) :
    simpleRandomWalkLaw
        (xEastUnprimedBadLabelUnion m
          (HLOZExternalUpper.externalLabelCount (prop44Psi m))) ≤
      HLOZExternalChain.externalPathLaw {s |
        Real.exp (16 * (m : ℝ) ^ prop44RateExponent) <
          ((evenSitesAtLeastReal s (prop44Psi m)
            (prop44SiteThreshold m)).card : ℝ)} := by
  rw [simpleRandomWalkLaw_xEastUnprimedBadLabelUnion_eq_selectedMass]
  let E : Set (ℕ → Site) := {s |
    Real.exp (16 * (m : ℝ) ^ prop44RateExponent) <
      ((evenSitesAtLeastReal s (prop44Psi m)
        (prop44SiteThreshold m)).card : ℝ)}
  have hE : MeasurableSet E := by
    have hsites : Measurable fun s : ℕ → Site ↦
        evenSitesAtLeastReal s (prop44Psi m) (prop44SiteThreshold m) := by
      rw [measurable_finset_iff]
      intro x
      simp only [evenSitesAtLeastReal, sitesAtLeastReal,
        Finset.mem_filter]
      exact (((measurable_finset_mem x).comp
          (measurable_visitedSites_eval (prop44Psi m))).and
        (measurableSet_setOfPred.mp
          (measurableSet_le measurable_const
            ((measurable_of_countable fun k : ℕ ↦ (k : ℝ)).comp
              (measurable_localTime_eval (prop44Psi m) x))))).and
        measurable_const
    exact measurableSet_lt measurable_const
      ((measurable_of_countable fun A : Finset Site ↦ (A.card : ℝ)).comp
        hsites)
  rw [HLOZExternalChain.externalPathLaw,
    Measure.map_apply HLOZExternalChain.measurable_externalWalk hE]
  exact measure_mono
    (selectedLabelEvent_xEastUnprimedBadVector_subset m)

theorem eventually_xEastUnprimedBadLabelUnion_measure_le :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalkLaw
          (xEastUnprimedBadLabelUnion m
            (HLOZExternalUpper.externalLabelCount (prop44Psi m))) ≤
        ENNReal.ofReal (Real.exp (-sourceRate m)) := by
  filter_upwards [HLOZExternalStepLaw.eventually_prop44_many_even_sites_bound]
    with m hm
  have hrate : sourceRate m = (m : ℝ) ^ prop44RateExponent := by
    rw [sourceRate, sourceRateExponent_eq, prop44RateExponent_eq]
  rw [hrate]
  exact (simpleRandomWalkLaw_xEastUnprimedBadLabelUnion_le_prop44 m).trans hm

/-- Proposition 4.4 supplies one eventual copy of the polynomial source
exceptional rate for the canonical unprimed label depth. -/
theorem eventually_xEastUnprimedBadLabelUnion_measure_le_exceptional :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalkLaw
          (xEastUnprimedBadLabelUnion m
            (HLOZExternalUpper.externalLabelCount (prop44Psi m))) ≤
        sourceExceptionalRateWithPrefactor m 1 kappa := by
  filter_upwards [eventually_xEastUnprimedBadLabelUnion_measure_le,
    eventually_source_errors_le_exceptional] with m hlabels hsource
  exact hlabels.trans (by
    simpa [sourceExceptionalRateWithPrefactor] using hsource.1)

/-- The genuine source exceptional event before the null complement of the
full fixed-label partition is added. -/
noncomputable def xEastUnprimedSourceBadEvent
    (m q : ℕ) (H : Set Path) : Set Path :=
  Hᶜ ∪ xEastUnprimedBadLabelUnion m q

noncomputable def xEastUnprimedPartitionBadEvent
    (m q : ℕ) (H : Set Path) : Set Path :=
  xEastUnprimedSourceBadEvent m q H ∪ (unprimedFixedAtomUnion q)ᶜ

theorem xEastUnprimed_goodAtom_cover (m k q : ℕ) (H : Set Path) :
    xEastUnprimedSourceEvent m k ⊆
      xEastUnprimedPartitionBadEvent m q H ∪
        ⋃ v ∈ xEastUnprimedGoodFixedAtoms m q,
          externalPathWalkAtom (List.ofFn (fixedIncrementLabels v)) ∩
            H ∩ xEastUnprimedSourceEvent m k := by
  intro s hs
  by_cases hsH : s ∈ H
  · by_cases hsU : s ∈ unprimedFixedAtomUnion q
    · rcases Set.mem_iUnion.mp hsU with ⟨v, hsv⟩
      by_cases hv : v ∈ xEastUnprimedGoodFixedAtoms m q
      · apply Or.inr
        rw [Set.mem_iUnion]
        refine ⟨v, ?_⟩
        rw [Set.mem_iUnion]
        exact ⟨hv, ⟨⟨hsv, hsH⟩, hs⟩⟩
      · apply Or.inl
        apply Or.inl
        apply Or.inr
        rw [xEastUnprimedBadLabelUnion]
        exact Set.mem_iUnion.mpr ⟨v, by simp [hv, hsv]⟩
    · exact Or.inl (Or.inr hsU)
  · exact Or.inl (Or.inl (Or.inl hsH))

theorem xEastUnprimedPartitionBadEvent_measure_le
    (m q badCoeff : ℕ) (H : Set Path)
    (hbad : simpleRandomWalkLaw (xEastUnprimedSourceBadEvent m q H) ≤
      sourceExceptionalRateWithPrefactor m badCoeff kappa) :
    simpleRandomWalkLaw (xEastUnprimedPartitionBadEvent m q H) ≤
      sourceExceptionalRateWithPrefactor m badCoeff kappa := by
  calc
    simpleRandomWalkLaw (xEastUnprimedPartitionBadEvent m q H) ≤
        simpleRandomWalkLaw (xEastUnprimedSourceBadEvent m q H) +
          simpleRandomWalkLaw (unprimedFixedAtomUnion q)ᶜ :=
      measure_union_le _ _
    _ = simpleRandomWalkLaw (xEastUnprimedSourceBadEvent m q H) := by
      rw [simpleRandomWalkLaw_unprimedFixedAtomUnion_compl, add_zero]
    _ ≤ _ := hbad

theorem xEastUnprimedSourceBadEvent_measure_le
    (m q horizonCoeff labelCoeff : ℕ) (H : Set Path)
    (hH : simpleRandomWalkLaw Hᶜ ≤
      sourceExceptionalRateWithPrefactor m horizonCoeff kappa)
    (hlabels : simpleRandomWalkLaw (xEastUnprimedBadLabelUnion m q) ≤
      sourceExceptionalRateWithPrefactor m labelCoeff kappa) :
    simpleRandomWalkLaw (xEastUnprimedSourceBadEvent m q H) ≤
      sourceExceptionalRateWithPrefactor m (horizonCoeff + labelCoeff) kappa := by
  calc
    simpleRandomWalkLaw (xEastUnprimedSourceBadEvent m q H) ≤
        simpleRandomWalkLaw Hᶜ +
          simpleRandomWalkLaw (xEastUnprimedBadLabelUnion m q) :=
      measure_union_le _ _
    _ ≤ sourceExceptionalRateWithPrefactor m horizonCoeff kappa +
        sourceExceptionalRateWithPrefactor m labelCoeff kappa :=
      add_le_add hH hlabels
    _ = sourceExceptionalRateWithPrefactor m
        (horizonCoeff + labelCoeff) kappa := by
      simp only [sourceExceptionalRateWithPrefactor]
      push_cast
      ring

abbrev PrimedFixedExternalLabels (q : ℕ) :=
  Direction × FixedExternalLabels q

/-- The odd external states encoded by a fixed first direction and the
fixed shifted terminal-label vector. -/
noncomputable def xEastPrimedFixedSites {q : ℕ}
    (z : PrimedFixedExternalLabels q) : Finset Site :=
  Finset.univ.image fun i : Fin q ↦
    directionStep z.1 + fixedExternalBase (fixedIncrementLabels z.2) i.1

/-- Primed analogue of
`xEastUnprimedThetaSite_mem_fixedSites_of_time_le`.  Odd walk times are the
fixed first increment followed by an even state of the adjacent-pair-swapped
walk, so the same realized-label reconstruction applies after the shift. -/
theorem xEastPrimedThetaSite_mem_fixedSites_of_time_le
    (m k : ℕ)
    (z : PrimedFixedExternalLabels
      (HLOZExternalUpper.externalLabelCount (prop44Psi m)))
    {s : Path} {x : Site} (hm : 0 < m) (hk : 0 < k)
    (hatom : s ∈ primedExternalPathWalkAtom z.1
      (fixedIncrementLabels z.2))
    (hTle : directCreationTime m k s ≤ prop44Psi m)
    (hx : x ∈ stoppedThetaHalfSites paperPrimedProfile
      (fun y ↦ ¬ HLOZPairing.chessEven y) false 10 s m k ∪
        stoppedThetaHalfSites paperPrimedProfile
          (fun y ↦ ¬ HLOZPairing.chessEven y) true 10 s m k) :
    x ∈ xEastPrimedFixedSites z := by
  classical
  rcases hatom with ⟨omega, homega, rfl⟩
  let eta := swappedIncrementShiftAfter primedOneShift omega
  obtain ⟨N, hlabels⟩ := realized_terminalPairLabelsThrough
    (fixedIncrementLabels z.2) (fixedIncrementLabels_nondistinguished z.2)
      homega.2
  rcases Finset.mem_union.mp hx with hx | hx <;>
    simp only [stoppedThetaHalfSites, Finset.mem_filter] at hx
  all_goals
    rcases hx with ⟨hxvisited, hfinite, hxOdd, _hxLower, hxUpper, _hxExternal⟩
    rcases Finset.mem_image.mp hxvisited with ⟨j, hj, hjx⟩
    have hxlt : localTime (simpleRandomWalk omega)
        (directCreationTime m k (simpleRandomWalk omega)) x < m := by
      exact_mod_cast hxUpper
    have hjlt : j < directCreationTime m k (simpleRandomWalk omega) := by
      have hjle : j ≤ directCreationTime m k (simpleRandomWalk omega) := by
        have hj' := Finset.mem_range.mp hj
        omega
      apply lt_of_le_of_ne hjle
      intro hjeq
      have hcreated := levelCreationSite_localTime_eq
        (simpleRandomWalk omega) m k hm hk hfinite
      have hxendpoint : x = levelCreationSite (simpleRandomWalk omega) m k := by
        rw [levelCreationSite, ← hjx]
        congr
      have hcreated' : localTime (simpleRandomWalk omega)
          (directCreationTime m k (simpleRandomWalk omega))
            (levelCreationSite (simpleRandomWalk omega) m k) = m := by
        simpa only [directCreationTime] using hcreated
      rw [hxendpoint, hcreated'] at hxlt
      exact (Nat.lt_irrefl m) hxlt
    have hjNotEven : ¬ Even j := by
      intro hjEven
      apply hxOdd
      rw [← hjx]
      exact (chessEven_simpleRandomWalk_iff omega j).mpr hjEven
    rcases Nat.not_even_iff_odd.mp hjNotEven with ⟨r, hr⟩
    have hjtwo : j = 2 * r + 1 := by omega
    have hrPsi : 2 * r + 1 < prop44Psi m := by omega
    have hrq : r < HLOZExternalUpper.externalLabelCount (prop44Psi m) := by
      unfold HLOZExternalUpper.externalLabelCount
      omega
    have hqN : HLOZExternalUpper.externalLabelCount (prop44Psi m) ≤ N := by
      have hcount := distinguished_add_terminal_count eta N
      rw [hlabels, List.length_ofFn] at hcount
      omega
    have heta := simpleRandomWalk_even_eq_fixedExternalBase_of_realized
      (fixedIncrementLabels z.2) hlabels r (hrq.le.trans hqN)
    have hwalk := simpleRandomWalk_odd_eq_first_add_swapped_even omega r
    rw [heta, homega.1] at hwalk
    apply Finset.mem_image.mpr
    refine ⟨⟨(terminalPairLabelsThrough eta r).length, ?_⟩,
      Finset.mem_univ _, ?_⟩
    · have hcount := distinguished_add_terminal_count eta r
      omega
    · rw [← hwalk, ← hjtwo, hjx]

theorem xEastPrimedFixedSites_odd {q : ℕ}
    (z : PrimedFixedExternalLabels q) (x : Site)
    (hx : x ∈ xEastPrimedFixedSites z) :
    ¬ HLOZPairing.chessEven x := by
  rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
  rw [add_comm, chessEven_add_directionStep_iff]
  exact not_not_intro
    (fixedExternalBase_chessEven (fixedIncrementLabels z.2) i)

theorem card_xEastPrimedFixedSites_le {q : ℕ}
    (z : PrimedFixedExternalLabels q) :
    (xEastPrimedFixedSites z).card ≤ q := by
  calc
    (xEastPrimedFixedSites z).card ≤
        (Finset.univ : Finset (Fin q)).card := Finset.card_image_le
    _ = q := Fintype.card_fin q

theorem primedRelativeSite_fixedSite {q : ℕ}
    (z : PrimedFixedExternalLabels q) (i : Fin q) :
    primedRelativeSite z.1
        (directionStep z.1 + fixedExternalBase
          (fixedIncrementLabels z.2) i.1) =
      fixedExternalBase (fixedIncrementLabels z.2) i.1 := by
  simp [primedRelativeSite]

theorem xEastPrimed_minus_capacity {m q : ℕ}
    (z : PrimedFixedExternalLabels q) (x : Site) :
    intervalDotIndex m (sourceBandLowerNat m)
        (xEastPrimedEncodedProfile z.1 (fixedIncrementLabels z.2)) x ≤
      (chronologicalExternalIndexList (fixedIncrementLabels z.2)
        (primedRelativeSite z.1 x)).length := by
  exact min_le_left _ _

theorem xEastPrimed_plus_capacity {m q : ℕ}
    (z : PrimedFixedExternalLabels q) (x : Site)
    (hx : x ∈ intervalPlusCandidates (xEastPrimedFixedSites z) m m
      (xEastPrimedEncodedProfile z.1 (fixedIncrementLabels z.2))) :
    intervalHighCut m m ≤
      (chronologicalExternalIndexList (fixedIncrementLabels z.2)
        (primedRelativeSite z.1 x)).length := by
  exact (Finset.mem_filter.mp hx).2

theorem xEastPrimedFixedAtom_inverseProfile
    {q : ℕ} (z : PrimedFixedExternalLabels q) (hq : 0 < q)
    {s : Path}
    (hs : s ∈ primedExternalPathWalkAtom z.1
      (fixedIncrementLabels z.2))
    (x : Site) (hx : x ∈ xEastPrimedFixedSites z) :
    primedInverseClockProfile s (2 * q - 1) x =
      xEastPrimedEncodedProfile z.1 (fixedIncrementLabels z.2) x := by
  rcases hs with ⟨omega, homega, rfl⟩
  obtain ⟨N, hlabels⟩ := realized_terminalPairLabelsThrough
    (fixedIncrementLabels z.2)
      (fixedIncrementLabels_nondistinguished z.2) homega.2
  have hprofile := primedInverseClockProfile_eq_chronological_length
    (fixedIncrementLabels z.2) hlabels x
      (xEastPrimedFixedSites_odd z x hx) hq
  rw [homega.1] at hprofile
  exact hprofile

def XEastPrimedFixedLabelGood (m : ℕ) {q : ℕ}
    (z : PrimedFixedExternalLabels q) : Prop :=
  ((sourceProp44Candidates (xEastPrimedFixedSites z) m
      (xEastPrimedEncodedProfile z.1
        (fixedIncrementLabels z.2))).card : ℝ) ≤
      Real.exp (16 * sourceRate m)

noncomputable def xEastPrimedGoodFixedAtoms (m q : ℕ) :
    Finset (PrimedFixedExternalLabels q) := by
  classical
  exact Finset.univ.filter (XEastPrimedFixedLabelGood m)

theorem mem_xEastPrimedGoodFixedAtoms_iff {m q : ℕ}
    {z : PrimedFixedExternalLabels q} :
    z ∈ xEastPrimedGoodFixedAtoms m q ↔
      XEastPrimedFixedLabelGood m z := by
  simp [xEastPrimedGoodFixedAtoms]

theorem xEastPrimedProp44Candidates_eq_image
    (m q : ℕ) (first : Direction) (v : FixedExternalLabels q) :
    sourceProp44Candidates (xEastPrimedFixedSites (first, v)) m
        (xEastPrimedEncodedProfile first (fixedIncrementLabels v)) =
      (sourceProp44Candidates (xEastUnprimedFixedSites v) m
        (xEastEncodedProfile (fixedIncrementLabels v))).image
          (fun x ↦ directionStep first + x) := by
  classical
  ext x
  simp only [sourceProp44Candidates, Finset.mem_filter,
    Finset.mem_image]
  constructor
  · rintro ⟨hxsite, hxprofile⟩
    rcases Finset.mem_image.mp hxsite with ⟨i, _hi, rfl⟩
    let y := fixedExternalBase (fixedIncrementLabels v) i.1
    refine ⟨y, ?_, rfl⟩
    refine ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, ?_⟩
    simpa [xEastPrimedEncodedProfile, primedRelativeSite,
      xEastEncodedProfile, y] using hxprofile
  · rintro ⟨y, ⟨hysite, hyprofile⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rcases Finset.mem_image.mp hysite with ⟨i, _hi, rfl⟩
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    · simpa [xEastPrimedEncodedProfile, primedRelativeSite,
        xEastEncodedProfile] using hyprofile

theorem xEastPrimedFixedLabelGood_iff
    (m q : ℕ) (first : Direction) (v : FixedExternalLabels q) :
    XEastPrimedFixedLabelGood m (first, v) ↔
      XEastUnprimedFixedLabelGood m v := by
  rw [XEastPrimedFixedLabelGood, XEastUnprimedFixedLabelGood,
    xEastPrimedProp44Candidates_eq_image]
  rw [Finset.card_image_of_injective]
  intro x y hxy
  exact add_left_cancel hxy

noncomputable def primedFixedAtomUnion (q : ℕ) : Set Path :=
  ⋃ z : PrimedFixedExternalLabels q,
    primedExternalPathWalkAtom z.1 (fixedIncrementLabels z.2)

theorem pairwise_primedFixedAtoms (q : ℕ) :
    (Set.univ : Set (PrimedFixedExternalLabels q)).PairwiseDisjoint
      (fun z ↦ primedExternalPathWalkAtom z.1
        (fixedIncrementLabels z.2)) := by
  intro z _ w _ hzw
  change Disjoint
    (primedExternalPathWalkAtom z.1 (fixedIncrementLabels z.2))
    (primedExternalPathWalkAtom w.1 (fixedIncrementLabels w.2))
  rw [Set.disjoint_left]
  rintro s ⟨omega, hωz, rfl⟩ ⟨eta, hωw, hs⟩
  have hωeta : omega = eta := simpleRandomWalk_injective hs.symm
  subst eta
  change omega 0 = z.1 ∧
      swappedIncrementShiftAfter primedOneShift omega ∈
        firstPairExternalPathEqFrom 0
          (externalPathFromLabels (List.ofFn (fixedIncrementLabels z.2))) at hωz
  change omega 0 = w.1 ∧
      swappedIncrementShiftAfter primedOneShift omega ∈
        firstPairExternalPathEqFrom 0
          (externalPathFromLabels (List.ofFn (fixedIncrementLabels w.2))) at hωw
  apply hzw
  apply Prod.ext
  · exact hωz.1.symm.trans hωw.1
  · funext i
    apply Subtype.ext
    have htz : swappedIncrementShiftAfter primedOneShift omega ∈
        firstPairTerminalLabelsEqFrom 0
          (List.ofFn (fixedIncrementLabels z.2)) := by
      rw [firstPairExternalPathEqFrom_reconstructed] at hωz
      exact hωz.2
    have htw : swappedIncrementShiftAfter primedOneShift omega ∈
        firstPairTerminalLabelsEqFrom 0
          (List.ofFn (fixedIncrementLabels w.2)) := by
      rw [firstPairExternalPathEqFrom_reconstructed] at hωw
      exact hωw.2
    change swappedIncrementShiftAfter primedOneShift omega ∈
        firstPairTerminalLabelsEqFrom 0
          (List.ofFn fun i ↦ (z.2 i : IncrementPair)) at htz
    change swappedIncrementShiftAfter primedOneShift omega ∈
        firstPairTerminalLabelsEqFrom 0
          (List.ofFn fun i ↦ (w.2 i : IncrementPair)) at htw
    have hterm := HLOZExternalChain.firstPairTerminalLabels_unique 0
      (fun p hp ↦ by
        rw [List.mem_ofFn] at hp
        obtain ⟨i, rfl⟩ := hp
        exact (z.2 i).property)
      (fun p hp ↦ by
        rw [List.mem_ofFn] at hp
        obtain ⟨i, rfl⟩ := hp
        exact (w.2 i).property)
      (by simp) htz htw
    exact congrFun (List.ofFn_injective hterm) i

theorem preimage_primedFixedAtomUnion (q : ℕ) :
    simpleRandomWalk ⁻¹' primedFixedAtomUnion q =
      swappedIncrementShiftAfter primedOneShift ⁻¹'
        HLOZExternalChain.selectedOriginalEvent
          (fun _ : FixedExternalLabels q ↦ True) := by
  classical
  ext omega
  simp only [primedFixedAtomUnion, Set.mem_preimage, Set.mem_iUnion,
    primedExternalPathWalkAtom, primedIncrementExternalPathAtom,
    HLOZExternalChain.selectedOriginalEvent, if_true,
    HLOZExternalChain.vectorLabels, Set.mem_image, Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨first, v⟩, eta, ⟨hfirst, hv⟩, hs⟩
    have hωeta : omega = eta := simpleRandomWalk_injective hs.symm
    subst eta
    refine ⟨v, ?_⟩
    rw [firstPairExternalPathEqFrom_reconstructed] at hv
    exact hv
  · rintro ⟨v, hv⟩
    refine ⟨⟨omega 0, v⟩, omega, ⟨rfl, ?_⟩, rfl⟩
    rw [firstPairExternalPathEqFrom_reconstructed]
    change swappedIncrementShiftAfter primedOneShift omega ∈
      firstPairTerminalLabelsEqFrom 0
        (List.ofFn fun i ↦ (v i : IncrementPair)) at hv
    exact hv

theorem swappedPrimedSuffix_hasLaw :
    HasLaw (swappedIncrementShiftAfter primedOneShift)
      incrementLaw incrementLaw := by
  have hpast : ∀ n, MeasurableSet[iidHistory (X := Direction) n]
      ((Set.univ : Set (ℕ → Direction)) ∩
        {omega | primedOneShift omega = n}) := by
    intro n
    by_cases hn : n = 1
    · subst n
      simp only [primedOneShift, Set.setOf_true, Set.inter_univ]
      exact @MeasurableSet.univ _ (iidHistory (X := Direction) 1)
    · have hempty : (Set.univ : Set (ℕ → Direction)) ∩
          {omega | primedOneShift omega = n} = ∅ := by
        ext omega
        simp [primedOneShift, Ne.symm hn]
      rw [hempty]
      exact @MeasurableSet.empty _ (iidHistory (X := Direction) n)
  have h := swappedIncrementShiftAfter_hasLaw_cond primedOneShift Set.univ
    measurable_primedOneShift hpast (by simp)
  simpa [ProbabilityTheory.cond] using h

theorem simpleRandomWalkLaw_primedFixedAtomUnion (q : ℕ) :
    simpleRandomWalkLaw (primedFixedAtomUnion q) = 1 := by
  rw [simpleRandomWalkLaw]
  change (Measure.map simpleRandomWalk incrementLaw)
    (primedFixedAtomUnion q) = 1
  have hmeas : MeasurableSet (primedFixedAtomUnion q) :=
    MeasurableSet.iUnion fun z ↦
      measurableSet_primedExternalPathWalkAtom z.1
        (fixedIncrementLabels z.2)
  rw [Measure.map_apply measurable_simpleRandomWalk hmeas,
    preimage_primedFixedAtomUnion]
  have hsel : MeasurableSet
      (HLOZExternalChain.selectedOriginalEvent
        (fun _ : FixedExternalLabels q ↦ True)) := by
    unfold HLOZExternalChain.selectedOriginalEvent
    exact MeasurableSet.iUnion fun v ↦ by
      simp only [if_true]
      exact iidTail_le 0 _
        (measurableSet_firstPairTerminalLabelsEqFrom_iidTail 0 _)
  rw [← Measure.map_apply
    (measurable_swappedIncrementShiftAfter measurable_primedOneShift) hsel,
    swappedPrimedSuffix_hasLaw.map_eq,
    incrementLaw_selectedOriginalEvent_true]

theorem simpleRandomWalkLaw_primedFixedAtomUnion_compl (q : ℕ) :
    simpleRandomWalkLaw (primedFixedAtomUnion q)ᶜ = 0 := by
  have hmeas : MeasurableSet (primedFixedAtomUnion q) :=
    MeasurableSet.iUnion fun z ↦
      measurableSet_primedExternalPathWalkAtom z.1
        (fixedIncrementLabels z.2)
  rw [measure_compl hmeas (measure_ne_top _ _),
    simpleRandomWalkLaw_primedFixedAtomUnion, measure_univ]
  simp

noncomputable def xEastPrimedBadLabelUnion (m q : ℕ) : Set Path :=
  ⋃ z : PrimedFixedExternalLabels q,
    if z ∈ xEastPrimedGoodFixedAtoms m q then ∅
    else primedExternalPathWalkAtom z.1 (fixedIncrementLabels z.2)

theorem preimage_xEastPrimedBadLabelUnion (m q : ℕ) :
    simpleRandomWalk ⁻¹' xEastPrimedBadLabelUnion m q =
      swappedIncrementShiftAfter primedOneShift ⁻¹'
        HLOZExternalChain.selectedOriginalEvent
          (xEastUnprimedBadVector m q) := by
  classical
  ext omega
  simp only [xEastPrimedBadLabelUnion, Set.mem_preimage,
    Set.mem_iUnion, primedExternalPathWalkAtom,
    primedIncrementExternalPathAtom, Set.mem_image, Set.mem_inter_iff,
    HLOZExternalChain.selectedOriginalEvent,
    HLOZExternalChain.vectorLabels]
  constructor
  · rintro ⟨⟨first, v⟩, hv⟩
    by_cases hgood : (first, v) ∈ xEastPrimedGoodFixedAtoms m q
    · simp [hgood] at hv
    · simp only [hgood, if_false] at hv
      rcases hv with ⟨eta, ⟨_hfirst, heta⟩, hwalk⟩
      have homega : omega = eta := simpleRandomWalk_injective hwalk.symm
      subst eta
      refine ⟨v, ?_⟩
      have hbad : xEastUnprimedBadVector m q v := by
        rw [xEastUnprimedBadVector]
        intro hvgood
        apply hgood
        rw [mem_xEastPrimedGoodFixedAtoms_iff,
          xEastPrimedFixedLabelGood_iff]
        exact hvgood
      simp only [hbad, if_true]
      rw [firstPairExternalPathEqFrom_reconstructed] at heta
      exact heta
  · rintro ⟨v, hv⟩
    by_cases hbad : xEastUnprimedBadVector m q v
    · simp only [hbad, if_true] at hv
      refine ⟨⟨omega 0, v⟩, ?_⟩
      have hgood : (omega 0, v) ∉ xEastPrimedGoodFixedAtoms m q := by
        rw [mem_xEastPrimedGoodFixedAtoms_iff,
          xEastPrimedFixedLabelGood_iff]
        exact hbad
      simp only [hgood, if_false]
      refine ⟨omega, ⟨rfl, ?_⟩, rfl⟩
      rw [firstPairExternalPathEqFrom_reconstructed]
      exact hv
    · simp [hbad] at hv

theorem simpleRandomWalkLaw_xEastPrimedBadLabelUnion_eq_selectedMass
    (m q : ℕ) :
    simpleRandomWalkLaw (xEastPrimedBadLabelUnion m q) =
      HLOZExternalChain.externalLabelLaw
        (HLOZExternalChain.selectedLabelEvent
          (xEastUnprimedBadVector m q)) := by
  have hmeas : MeasurableSet (xEastPrimedBadLabelUnion m q) := by
    apply MeasurableSet.iUnion
    intro z
    by_cases hz : z ∈ xEastPrimedGoodFixedAtoms m q
    · simp [hz]
    · simpa [hz] using
        measurableSet_primedExternalPathWalkAtom z.1
          (fixedIncrementLabels z.2)
  rw [simpleRandomWalkLaw, Measure.map_apply measurable_simpleRandomWalk hmeas,
    preimage_xEastPrimedBadLabelUnion]
  have hsel : MeasurableSet
      (HLOZExternalChain.selectedOriginalEvent
        (xEastUnprimedBadVector m q)) := by
    unfold HLOZExternalChain.selectedOriginalEvent
    apply MeasurableSet.iUnion
    intro v
    by_cases hv : xEastUnprimedBadVector m q v
    · simp only [hv, if_true]
      exact iidTail_le 0 _
        (measurableSet_firstPairTerminalLabelsEqFrom_iidTail 0 _)
    · simp [hv]
  rw [← Measure.map_apply
    (measurable_swappedIncrementShiftAfter measurable_primedOneShift) hsel,
    swappedPrimedSuffix_hasLaw.map_eq,
    HLOZExternalChain.measure_selected_events_eq]

theorem eventually_xEastPrimedBadLabelUnion_measure_le :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalkLaw
          (xEastPrimedBadLabelUnion m
            (HLOZExternalUpper.externalLabelCount (prop44Psi m))) ≤
        ENNReal.ofReal (Real.exp (-sourceRate m)) := by
  filter_upwards [eventually_xEastUnprimedBadLabelUnion_measure_le]
    with m hm
  rw [simpleRandomWalkLaw_xEastPrimedBadLabelUnion_eq_selectedMass,
    ← simpleRandomWalkLaw_xEastUnprimedBadLabelUnion_eq_selectedMass]
  exact hm

/-- The shifted primed label atomization has the same Proposition-4.4 tail,
again absorbed into one eventual copy of the source exceptional rate. -/
theorem eventually_xEastPrimedBadLabelUnion_measure_le_exceptional :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalkLaw
          (xEastPrimedBadLabelUnion m
            (HLOZExternalUpper.externalLabelCount (prop44Psi m))) ≤
        sourceExceptionalRateWithPrefactor m 1 kappa := by
  filter_upwards [eventually_xEastPrimedBadLabelUnion_measure_le,
    eventually_source_errors_le_exceptional] with m hlabels hsource
  exact hlabels.trans (by
    simpa [sourceExceptionalRateWithPrefactor] using hsource.1)

noncomputable def xEastPrimedSourceBadEvent
    (m q : ℕ) (H : Set Path) : Set Path :=
  Hᶜ ∪ xEastPrimedBadLabelUnion m q

noncomputable def xEastPrimedPartitionBadEvent
    (m q : ℕ) (H : Set Path) : Set Path :=
  xEastPrimedSourceBadEvent m q H ∪ (primedFixedAtomUnion q)ᶜ

theorem xEastPrimed_goodAtom_cover (m k q : ℕ) (H : Set Path) :
    xEastPrimedSourceEvent m k ⊆
      xEastPrimedPartitionBadEvent m q H ∪
        ⋃ z ∈ xEastPrimedGoodFixedAtoms m q,
          primedExternalPathWalkAtom z.1 (fixedIncrementLabels z.2) ∩
            H ∩ xEastPrimedSourceEvent m k := by
  intro s hs
  by_cases hsH : s ∈ H
  · by_cases hsU : s ∈ primedFixedAtomUnion q
    · rcases Set.mem_iUnion.mp hsU with ⟨z, hsz⟩
      by_cases hz : z ∈ xEastPrimedGoodFixedAtoms m q
      · apply Or.inr
        rw [Set.mem_iUnion]
        refine ⟨z, ?_⟩
        rw [Set.mem_iUnion]
        exact ⟨hz, ⟨⟨hsz, hsH⟩, hs⟩⟩
      · apply Or.inl
        apply Or.inl
        apply Or.inr
        rw [xEastPrimedBadLabelUnion]
        exact Set.mem_iUnion.mpr ⟨z, by simp [hz, hsz]⟩
    · exact Or.inl (Or.inr hsU)
  · exact Or.inl (Or.inl (Or.inl hsH))

theorem xEastPrimedPartitionBadEvent_measure_le
    (m q badCoeff : ℕ) (H : Set Path)
    (hbad : simpleRandomWalkLaw (xEastPrimedSourceBadEvent m q H) ≤
      sourceExceptionalRateWithPrefactor m badCoeff kappa) :
    simpleRandomWalkLaw (xEastPrimedPartitionBadEvent m q H) ≤
      sourceExceptionalRateWithPrefactor m badCoeff kappa := by
  calc
    simpleRandomWalkLaw (xEastPrimedPartitionBadEvent m q H) ≤
        simpleRandomWalkLaw (xEastPrimedSourceBadEvent m q H) +
          simpleRandomWalkLaw (primedFixedAtomUnion q)ᶜ :=
      measure_union_le _ _
    _ = simpleRandomWalkLaw (xEastPrimedSourceBadEvent m q H) := by
      rw [simpleRandomWalkLaw_primedFixedAtomUnion_compl, add_zero]
    _ ≤ _ := hbad

theorem xEastPrimedSourceBadEvent_measure_le
    (m q horizonCoeff labelCoeff : ℕ) (H : Set Path)
    (hH : simpleRandomWalkLaw Hᶜ ≤
      sourceExceptionalRateWithPrefactor m horizonCoeff kappa)
    (hlabels : simpleRandomWalkLaw (xEastPrimedBadLabelUnion m q) ≤
      sourceExceptionalRateWithPrefactor m labelCoeff kappa) :
    simpleRandomWalkLaw (xEastPrimedSourceBadEvent m q H) ≤
      sourceExceptionalRateWithPrefactor m (horizonCoeff + labelCoeff) kappa := by
  calc
    simpleRandomWalkLaw (xEastPrimedSourceBadEvent m q H) ≤
        simpleRandomWalkLaw Hᶜ +
          simpleRandomWalkLaw (xEastPrimedBadLabelUnion m q) :=
      measure_union_le _ _
    _ ≤ sourceExceptionalRateWithPrefactor m horizonCoeff kappa +
        sourceExceptionalRateWithPrefactor m labelCoeff kappa :=
      add_le_add hH hlabels
    _ = sourceExceptionalRateWithPrefactor m
        (horizonCoeff + labelCoeff) kappa := by
      simp only [sourceExceptionalRateWithPrefactor]
      push_cast
      ring

/-! ### Canonical source horizon -/

/-- The good horizon is exactly the complement of the late part of
`M_m^k` at the rounded near-critical time.  Using the complement, rather
than the bare event `T_m^k ≤ ψ_m`, is important: its exceptional part is
the event controlled by Proposition 1.3 without making any claim outside
the source threshold history. -/
noncomputable def xEastCanonicalHorizonEvent (m k : ℕ) : Set Path :=
  (HLOZNearCriticalBridge.lateOnThresholdEvent
    HLOZNearCriticalBridge.nearCriticalHorizon m k)ᶜ

/-- The apparent `k`/`k+1` offset is harmless pathwise: the source prefix
event at `k+1` implies `M_m^k` by monotonicity, and membership in the
canonical good horizon then forces `T_m^k ≤ ψ_m`. -/
theorem directCreationTime_le_prop44Psi_of_mem_canonicalHorizon
    (m k : ℕ) {s : Path}
    (hhorizon : s ∈ xEastCanonicalHorizonEvent m k)
    (hthreshold : s ∈ hlozThresholdTimeEventK m (k + 1)) :
    directCreationTime m k s ≤ prop44Psi m := by
  have hMnext := hthreshold
  change firstKSitesReachLevel m (k + 1) s <
    firstKSitesReachLevel (m + 1) 1 s at hMnext
  have hM : s ∈ HLOZNearCriticalBridge.thresholdTimeEventK m k := by
    change firstKSitesReachLevel m k s <
      firstKSitesReachLevel (m + 1) 1 s
    exact (firstKSitesReachLevel_mono_k s m (by omega)).trans_lt hMnext
  have hTle : firstKSitesReachLevel m k s ≤
      (HLOZNearCriticalBridge.nearCriticalHorizon m : WithTop ℕ) := by
    change s ∉ HLOZNearCriticalBridge.lateOnThresholdEvent
      HLOZNearCriticalBridge.nearCriticalHorizon m k at hhorizon
    by_contra hnot
    apply hhorizon
    exact ⟨lt_of_not_ge hnot, hM⟩
  rw [HLOZProp44ExternalChain.prop44Psi_eq_nearCriticalHorizon]
  exact WithTop.untopA_le hTle

/-- A site whose stopped local time is still below `m` cannot be the site
created at the `k`-th level-`m` threshold time. -/
theorem favoriteCreationHorizon_endpoint_ne_of_localTime_lt
    (m k : ℕ) {s : Path} (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hthreshold : s ∈ hlozThresholdTimeEventK m (k + 1))
    (x : Site)
    (hxlt : localTime s (favoriteCreationHorizon m k s) x < m) :
    s (favoriteCreationHorizon m k s) ≠ x := by
  have hnextFinite : firstKSitesReachLevel m (k + 1) s ≠ ⊤ :=
    ne_top_of_lt hthreshold
  have hkFinite : firstKSitesReachLevel m k s ≠ ⊤ := by
    intro hkTop
    have hmono := firstKSitesReachLevel_mono_k s m (show k ≤ k + 1 by omega)
    rw [hkTop] at hmono
    exact hnextFinite (top_unique hmono)
  have hcreated := levelCreationSite_localTime_eq s m k
    (by omega) (by omega) hkFinite
  have hcreated' : localTime s (favoriteCreationHorizon m k s)
      (s (favoriteCreationHorizon m k s)) = m := by
    rw [favoriteCreationHorizon_eq_directCreationTime s hm hk]
    simpa only [directCreationTime, levelCreationSite] using hcreated
  intro heq
  rw [heq] at hcreated'
  omega

/-- A positive-level creation horizon is strictly positive.  This tiny fact
is what lets an even off-diagonal horizon be written as `2 * R + 2`, exposing
the preceding completed primed pair. -/
theorem favoriteCreationHorizon_pos
    (m k : ℕ) {s : Path} (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hthreshold : s ∈ hlozThresholdTimeEventK m (k + 1)) :
    0 < favoriteCreationHorizon m k s := by
  have hnextFinite : firstKSitesReachLevel m (k + 1) s ≠ ⊤ :=
    ne_top_of_lt hthreshold
  have hkFinite : firstKSitesReachLevel m k s ≠ ⊤ := by
    intro hkTop
    have hmono := firstKSitesReachLevel_mono_k s m (show k ≤ k + 1 by omega)
    rw [hkTop] at hmono
    exact hnextFinite (top_unique hmono)
  have hcreated := levelCreationSite_localTime_eq s m k
    (by omega) (by omega) hkFinite
  have hcreated' : localTime s (favoriteCreationHorizon m k s)
      (s (favoriteCreationHorizon m k s)) = m := by
    rw [favoriteCreationHorizon_eq_directCreationTime s hm hk]
    simpa only [directCreationTime, levelCreationSite] using hcreated
  have hle : localTime s (favoriteCreationHorizon m k s)
      (s (favoriteCreationHorizon m k s)) ≤
        favoriteCreationHorizon m k s + 1 := by
    unfold localTime
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)
  rw [hcreated'] at hle
  omega

/-- On the canonical good horizon, a non-creation even endpoint has no more
unprimed external visits than the fixed profile.  This is the pathwise
profile half of the stopped-clock compatibility used by the capped branch. -/
theorem paperExternalLocalTime_canonicalHorizon_le_fixedProfile
    (m k : ℕ)
    (v : FixedExternalLabels
      (HLOZExternalUpper.externalLabelCount (prop44Psi m)))
    {s : Path} (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hatom : s ∈ externalPathWalkAtom
      (List.ofFn (fixedIncrementLabels v)))
    (hhorizon : s ∈ xEastCanonicalHorizonEvent m k)
    (hsource : s ∈ xEastUnprimedSourceEvent m k)
    (x : Site) (hxEven : HLOZPairing.chessEven x)
    (hxlt : localTime s (favoriteCreationHorizon m k s) x < m) :
    paperExternalLocalTime s (favoriteCreationHorizon m k s) x ≤
      inverseClockProfile s
        (2 * HLOZExternalUpper.externalLabelCount (prop44Psi m) - 1) x := by
  have hTleDirect := directCreationTime_le_prop44Psi_of_mem_canonicalHorizon
    m k hhorizon hsource.1
  have htime := favoriteCreationHorizon_eq_directCreationTime s hm hk
  have hTle : favoriteCreationHorizon m k s ≤ prop44Psi m := by
    simpa only [htime] using hTleDirect
  have hnextFinite : firstKSitesReachLevel m (k + 1) s ≠ ⊤ :=
    ne_top_of_lt hsource.1
  have hkFinite : firstKSitesReachLevel m k s ≠ ⊤ := by
    intro hkTop
    have hmono := firstKSitesReachLevel_mono_k s m (show k ≤ k + 1 by omega)
    rw [hkTop] at hmono
    exact hnextFinite (top_unique hmono)
  have hcreated := levelCreationSite_localTime_eq s m k
    (by omega) (by omega) hkFinite
  have hcreated' : localTime s (favoriteCreationHorizon m k s)
      (s (favoriteCreationHorizon m k s)) = m := by
    rw [favoriteCreationHorizon_eq_directCreationTime s hm hk]
    simpa only [directCreationTime, levelCreationSite] using hcreated
  have hendpoint : s (favoriteCreationHorizon m k s) ≠ x := by
    intro heq
    rw [heq] at hcreated'
    omega
  exact paperExternalLocalTime_le_canonicalFixedProfile
    (prop44Psi_pos m) v hatom x hxEven hTle hendpoint

/-- At an odd canonical horizon the possibly unfinished last unprimed
holding block is still bounded by the corresponding *completed* fixed-label
holding coordinate.  The strict inequality `R < q` follows from the
canonical horizon, so one more fixed pair is available beyond the active
pair. -/
theorem paperLazyLocalTime_canonicalHorizon_le_inversePrefix_of_odd
    (m k : ℕ)
    (v : FixedExternalLabels
      (HLOZExternalUpper.externalLabelCount (prop44Psi m)))
    {s : Path} (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hatom : s ∈ externalPathWalkAtom
      (List.ofFn (fixedIncrementLabels v)))
    (hhorizon : s ∈ xEastCanonicalHorizonEvent m k)
    (hsource : s ∈ xEastUnprimedSourceEvent m k)
    (x : Site) (hxEven : HLOZPairing.chessEven x)
    (hOdd : ¬ Even (favoriteCreationHorizon m k s)) :
    paperLazyLocalTime s (favoriteCreationHorizon m k s) x ≤
      inverseClockHoldingPrefix s
        (2 * HLOZExternalUpper.externalLabelCount (prop44Psi m) - 1)
        (paperExternalLocalTime s (favoriteCreationHorizon m k s) x) x := by
  rcases hatom with ⟨omega, homega, rfl⟩
  obtain ⟨R, hR⟩ := Nat.not_even_iff_odd.mp hOdd
  have htime : favoriteCreationHorizon m k (simpleRandomWalk omega) =
      2 * R + 1 := by omega
  obtain ⟨N, hlabels⟩ := realized_terminalPairLabelsThrough
    (fixedIncrementLabels v) (fixedIncrementLabels_nondistinguished v) homega
  let q := HLOZExternalUpper.externalLabelCount (prop44Psi m)
  have hq : 0 < q := externalLabelCount_prop44Psi_pos m
  have hqN : q ≤ N := by
    have hcount := distinguished_add_terminal_count omega N
    rw [hlabels, List.length_ofFn] at hcount
    dsimp only [q]
    omega
  have hTleDirect := directCreationTime_le_prop44Psi_of_mem_canonicalHorizon
    m k hhorizon hsource.1
  have hTle : favoriteCreationHorizon m k (simpleRandomWalk omega) ≤
      prop44Psi m := by
    simpa only [favoriteCreationHorizon_eq_directCreationTime
      (simpleRandomWalk omega) hm hk] using hTleDirect
  have hfit := HLOZExternalUpper.external_time_fits_labelCount (prop44Psi m)
  have hRq : R < q := by
    dsimp only [q] at hfit ⊢
    omega
  have heven := paperLazyLocalTime_even_le_inverseClockHoldingPrefix_of_lt_pair
    (fixedIncrementLabels v) hq hlabels (hRq.le.trans hqN) hRq x hxEven
  have hlazy := paperLazyLocalTime_odd_eq_even_of_chessEven omega R x hxEven
  have hext := paperExternalLocalTime_odd_eq_even_of_chessEven omega R x hxEven
  rw [htime]
  calc
    paperLazyLocalTime (simpleRandomWalk omega) (2 * R + 1) x =
        paperLazyLocalTime (simpleRandomWalk omega) (2 * R) x := hlazy
    _ ≤ inverseClockHoldingPrefix (simpleRandomWalk omega) (2 * q - 1)
        (paperExternalLocalTime (simpleRandomWalk omega) (2 * R) x) x := heven
    _ = inverseClockHoldingPrefix (simpleRandomWalk omega) (2 * q - 1)
        (paperExternalLocalTime (simpleRandomWalk omega) (2 * R + 1) x) x := by
      rw [hext]

/-- On the active odd terminal base, every *strictly earlier* external
coordinate is complete.  Hence a strict cutoff below the stopped external
count is automatically contained in the stopped lazy local time. -/
theorem inverseClockHoldingPrefix_canonicalHorizon_le_paperLazy_of_odd_of_lt
    (m k : ℕ)
    (v : FixedExternalLabels
      (HLOZExternalUpper.externalLabelCount (prop44Psi m)))
    {s : Path} (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hatom : s ∈ externalPathWalkAtom
      (List.ofFn (fixedIncrementLabels v)))
    (hhorizon : s ∈ xEastCanonicalHorizonEvent m k)
    (hsource : s ∈ xEastUnprimedSourceEvent m k)
    (x : Site) (hxEven : HLOZPairing.chessEven x)
    (hOdd : ¬ Even (favoriteCreationHorizon m k s))
    (hprevious : s (favoriteCreationHorizon m k s - 1) = x)
    {cut : ℕ}
    (hcut : cut < paperExternalLocalTime s
      (favoriteCreationHorizon m k s) x) :
    inverseClockHoldingPrefix s
        (2 * HLOZExternalUpper.externalLabelCount (prop44Psi m) - 1) cut x ≤
      paperLazyLocalTime s (favoriteCreationHorizon m k s) x := by
  rcases hatom with ⟨omega, homega, rfl⟩
  obtain ⟨R, hR⟩ := Nat.not_even_iff_odd.mp hOdd
  have htime : favoriteCreationHorizon m k (simpleRandomWalk omega) =
      2 * R + 1 := by omega
  obtain ⟨N, hlabels⟩ := realized_terminalPairLabelsThrough
    (fixedIncrementLabels v) (fixedIncrementLabels_nondistinguished v) homega
  let q := HLOZExternalUpper.externalLabelCount (prop44Psi m)
  have hq : 0 < q := externalLabelCount_prop44Psi_pos m
  have hqN : q ≤ N := by
    have hcount := distinguished_add_terminal_count omega N
    rw [hlabels, List.length_ofFn] at hcount
    dsimp only [q]
    omega
  have hTleDirect := directCreationTime_le_prop44Psi_of_mem_canonicalHorizon
    m k hhorizon hsource.1
  have hTle : favoriteCreationHorizon m k (simpleRandomWalk omega) ≤
      prop44Psi m := by
    simpa only [favoriteCreationHorizon_eq_directCreationTime
      (simpleRandomWalk omega) hm hk] using hTleDirect
  have hfit := HLOZExternalUpper.external_time_fits_labelCount (prop44Psi m)
  have hRq : R < q := by
    dsimp only [q] at hfit ⊢
    omega
  have hcurrent : simpleRandomWalk omega (2 * R) = x := by
    have hsub : favoriteCreationHorizon m k (simpleRandomWalk omega) - 1 =
        2 * R := by omega
    simpa only [hsub] using hprevious
  have hext := paperExternalLocalTime_odd_eq_even_of_chessEven omega R x hxEven
  have hlazy := paperLazyLocalTime_odd_eq_even_of_chessEven omega R x hxEven
  have hcutEven : cut <
      paperExternalLocalTime (simpleRandomWalk omega) (2 * R) x := by
    rw [htime, hext] at hcut
    exact hcut
  have hle := inverseClockHoldingPrefix_le_paperLazyLocalTime_even_of_cut_lt
    (fixedIncrementLabels v) hq hlabels (hRq.le.trans hqN) hRq x hxEven
      hcurrent hcutEven
  rw [htime]
  exact hle.trans_eq hlazy.symm

/-- On the canonical good horizon, every odd endpoint has no more primed
external visits than its shifted fixed profile.  Unlike the unprimed case,
the primed parity identity already removes the final even-time endpoint, so
no separate endpoint exclusion is needed. -/
theorem primedExternalLocalTime_canonicalHorizon_le_fixedProfile
    (m k : ℕ)
    (z : PrimedFixedExternalLabels
      (HLOZExternalUpper.externalLabelCount (prop44Psi m)))
    {s : Path} (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hatom : s ∈ primedExternalPathWalkAtom z.1
      (fixedIncrementLabels z.2))
    (hhorizon : s ∈ xEastCanonicalHorizonEvent m k)
    (hsource : s ∈ xEastPrimedSourceEvent m k)
    (x : Site) (hxOdd : ¬ HLOZPairing.chessEven x) :
    primedExternalLocalTime s (favoriteCreationHorizon m k s) x ≤
      primedInverseClockProfile s
        (2 * HLOZExternalUpper.externalLabelCount (prop44Psi m) - 1) x := by
  have hTleDirect := directCreationTime_le_prop44Psi_of_mem_canonicalHorizon
    m k hhorizon hsource.1
  have htime := favoriteCreationHorizon_eq_directCreationTime s hm hk
  have hTle : favoriteCreationHorizon m k s ≤ prop44Psi m := by
    simpa only [htime] using hTleDirect
  exact primedExternalLocalTime_le_canonicalFixedProfile
    (prop44Psi_pos m) z.1 z.2 hatom x hxOdd hTle

/-- At an even canonical horizon the final primed holding block may be
unfinished, but the fixed shifted label vector extends to the next pair and
therefore its completed holding coordinate dominates the stopped block. -/
theorem primedLazyLocalTime_canonicalHorizon_le_inversePrefix_of_even
    (m k : ℕ)
    (z : PrimedFixedExternalLabels
      (HLOZExternalUpper.externalLabelCount (prop44Psi m)))
    {s : Path} (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hatom : s ∈ primedExternalPathWalkAtom z.1
      (fixedIncrementLabels z.2))
    (hhorizon : s ∈ xEastCanonicalHorizonEvent m k)
    (hsource : s ∈ xEastPrimedSourceEvent m k)
    (x : Site) (hxOdd : ¬ HLOZPairing.chessEven x)
    (hEven : Even (favoriteCreationHorizon m k s)) :
    primedLazyLocalTime s (favoriteCreationHorizon m k s) x ≤
      primedInverseClockHoldingPrefix s
        (2 * HLOZExternalUpper.externalLabelCount (prop44Psi m) - 1)
        (primedExternalLocalTime s (favoriteCreationHorizon m k s) x) x := by
  rcases hatom with ⟨omega, homega, rfl⟩
  have hpos := favoriteCreationHorizon_pos m k hm hk hsource.1
  obtain ⟨U, hU⟩ := hEven
  obtain ⟨R, htime⟩ : ∃ R : ℕ,
      favoriteCreationHorizon m k (simpleRandomWalk omega) = 2 * R + 2 := by
    refine ⟨U - 1, ?_⟩
    omega
  let q := HLOZExternalUpper.externalLabelCount (prop44Psi m)
  have hq : 0 < q := externalLabelCount_prop44Psi_pos m
  have hTleDirect := directCreationTime_le_prop44Psi_of_mem_canonicalHorizon
    m k hhorizon hsource.1
  have hTle : favoriteCreationHorizon m k (simpleRandomWalk omega) ≤
      prop44Psi m := by
    simpa only [favoriteCreationHorizon_eq_directCreationTime
      (simpleRandomWalk omega) hm hk] using hTleDirect
  have hfit := HLOZExternalUpper.external_time_fits_labelCount (prop44Psi m)
  have hRq : R < q := by
    dsimp only [q] at hfit ⊢
    omega
  have hodd := primedLazyLocalTime_odd_le_inverseClockHoldingPrefix_of_lt_pair
    (fixedIncrementLabels z.2) (fixedIncrementLabels_nondistinguished z.2)
      hq homega.2 hRq x hxOdd
  have hlazy := primedLazyLocalTime_even_eq_odd_of_chessOdd omega R x hxOdd
  have hext := primedExternalLocalTime_even_eq_odd_of_chessOdd omega R x hxOdd
  rw [htime]
  calc
    primedLazyLocalTime (simpleRandomWalk omega) (2 * R + 2) x =
        primedLazyLocalTime (simpleRandomWalk omega) (2 * R + 1) x := hlazy
    _ ≤ primedInverseClockHoldingPrefix (simpleRandomWalk omega) (2 * q - 1)
        (primedExternalLocalTime (simpleRandomWalk omega) (2 * R + 1) x) x := hodd
    _ = primedInverseClockHoldingPrefix (simpleRandomWalk omega) (2 * q - 1)
        (primedExternalLocalTime (simpleRandomWalk omega) (2 * R + 2) x) x := by
      rw [hext]

/-- Primed counterpart of
`inverseClockHoldingPrefix_canonicalHorizon_le_paperLazy_of_odd_of_lt`:
a strict cutoff excludes the unfinished active odd base at an even terminal
horizon. -/
theorem primedInverseClockHoldingPrefix_canonicalHorizon_le_lazy_of_even_of_lt
    (m k : ℕ)
    (z : PrimedFixedExternalLabels
      (HLOZExternalUpper.externalLabelCount (prop44Psi m)))
    {s : Path} (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hatom : s ∈ primedExternalPathWalkAtom z.1
      (fixedIncrementLabels z.2))
    (hhorizon : s ∈ xEastCanonicalHorizonEvent m k)
    (hsource : s ∈ xEastPrimedSourceEvent m k)
    (x : Site) (hxOdd : ¬ HLOZPairing.chessEven x)
    (hEven : Even (favoriteCreationHorizon m k s))
    (hprevious : s (favoriteCreationHorizon m k s - 1) = x)
    {cut : ℕ}
    (hcut : cut < primedExternalLocalTime s
      (favoriteCreationHorizon m k s) x) :
    primedInverseClockHoldingPrefix s
        (2 * HLOZExternalUpper.externalLabelCount (prop44Psi m) - 1) cut x ≤
      primedLazyLocalTime s (favoriteCreationHorizon m k s) x := by
  rcases hatom with ⟨omega, homega, rfl⟩
  have hpos := favoriteCreationHorizon_pos m k hm hk hsource.1
  obtain ⟨U, hU⟩ := hEven
  obtain ⟨R, htime⟩ : ∃ R : ℕ,
      favoriteCreationHorizon m k (simpleRandomWalk omega) = 2 * R + 2 := by
    refine ⟨U - 1, ?_⟩
    omega
  let q := HLOZExternalUpper.externalLabelCount (prop44Psi m)
  have hq : 0 < q := externalLabelCount_prop44Psi_pos m
  have hTleDirect := directCreationTime_le_prop44Psi_of_mem_canonicalHorizon
    m k hhorizon hsource.1
  have hTle : favoriteCreationHorizon m k (simpleRandomWalk omega) ≤
      prop44Psi m := by
    simpa only [favoriteCreationHorizon_eq_directCreationTime
      (simpleRandomWalk omega) hm hk] using hTleDirect
  have hfit := HLOZExternalUpper.external_time_fits_labelCount (prop44Psi m)
  have hRq : R < q := by
    dsimp only [q] at hfit ⊢
    omega
  have hcurrent : simpleRandomWalk omega (2 * R + 1) = x := by
    have hsub : favoriteCreationHorizon m k (simpleRandomWalk omega) - 1 =
        2 * R + 1 := by omega
    simpa only [hsub] using hprevious
  have hext := primedExternalLocalTime_even_eq_odd_of_chessOdd omega R x hxOdd
  have hlazy := primedLazyLocalTime_even_eq_odd_of_chessOdd omega R x hxOdd
  have hcutOdd : cut <
      primedExternalLocalTime (simpleRandomWalk omega) (2 * R + 1) x := by
    rw [htime, hext] at hcut
    exact hcut
  have hle :=
    primedInverseClockHoldingPrefix_le_primedLazyLocalTime_odd_of_cut_lt
      (fixedIncrementLabels z.2) (fixedIncrementLabels_nondistinguished z.2)
        hq homega.2 hRq x hxOdd hcurrent hcutOdd
  rw [htime]
  exact hle.trans_eq hlazy.symm

/-- On an even canonical stopping horizon the unprimed lazy clock is
exactly the inverse holding prefix cut at the stopped external count. -/
theorem paperLazyLocalTime_canonicalHorizon_eq_inversePrefix_of_even
    (m k : ℕ)
    (v : FixedExternalLabels
      (HLOZExternalUpper.externalLabelCount (prop44Psi m)))
    {s : Path} (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hatom : s ∈ externalPathWalkAtom
      (List.ofFn (fixedIncrementLabels v)))
    (hhorizon : s ∈ xEastCanonicalHorizonEvent m k)
    (hsource : s ∈ xEastUnprimedSourceEvent m k)
    (x : Site) (hxEven : HLOZPairing.chessEven x)
    (hxlt : localTime s (favoriteCreationHorizon m k s) x < m)
    (hEven : Even (favoriteCreationHorizon m k s)) :
    paperLazyLocalTime s (favoriteCreationHorizon m k s) x =
      inverseClockHoldingPrefix s
        (2 * HLOZExternalUpper.externalLabelCount (prop44Psi m) - 1)
        (paperExternalLocalTime s (favoriteCreationHorizon m k s) x) x := by
  rcases hatom with ⟨omega, homega, rfl⟩
  obtain ⟨R, hR⟩ := hEven
  have htime : favoriteCreationHorizon m k (simpleRandomWalk omega) =
      2 * R := by omega
  obtain ⟨N, hlabels⟩ := realized_terminalPairLabelsThrough
    (fixedIncrementLabels v) (fixedIncrementLabels_nondistinguished v) homega
  let q := HLOZExternalUpper.externalLabelCount (prop44Psi m)
  have hq : 0 < q := externalLabelCount_prop44Psi_pos m
  have hqN : q ≤ N := by
    have hcount := distinguished_add_terminal_count omega N
    rw [hlabels, List.length_ofFn] at hcount
    dsimp only [q]
    omega
  have hTleDirect := directCreationTime_le_prop44Psi_of_mem_canonicalHorizon
    m k hhorizon hsource.1
  have hTle : favoriteCreationHorizon m k (simpleRandomWalk omega) ≤
      prop44Psi m := by
    simpa only [favoriteCreationHorizon_eq_directCreationTime
      (simpleRandomWalk omega) hm hk] using hTleDirect
  have hfit := HLOZExternalUpper.external_time_fits_labelCount (prop44Psi m)
  have hRq : R ≤ q := by
    dsimp only [q] at hfit ⊢
    omega
  have hcurrent := favoriteCreationHorizon_endpoint_ne_of_localTime_lt
    m k hm hk hsource.1 x hxlt
  rw [htime]
  exact paperLazyLocalTime_even_eq_inverseClockHoldingPrefix
    (fixedIncrementLabels v) hq hlabels (hRq.trans hqN) x hxEven
      (by simpa only [htime] using hcurrent)

/-- On an odd canonical stopping horizon the analogous exact identity is
the primed inverse holding prefix. -/
theorem primedLazyLocalTime_canonicalHorizon_eq_inversePrefix_of_odd
    (m k : ℕ)
    (z : PrimedFixedExternalLabels
      (HLOZExternalUpper.externalLabelCount (prop44Psi m)))
    {s : Path} (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hatom : s ∈ primedExternalPathWalkAtom z.1
      (fixedIncrementLabels z.2))
    (hhorizon : s ∈ xEastCanonicalHorizonEvent m k)
    (hsource : s ∈ xEastPrimedSourceEvent m k)
    (x : Site) (hxOdd : ¬ HLOZPairing.chessEven x)
    (hxlt : localTime s (favoriteCreationHorizon m k s) x < m)
    (hOdd : ¬ Even (favoriteCreationHorizon m k s)) :
    primedLazyLocalTime s (favoriteCreationHorizon m k s) x =
      primedInverseClockHoldingPrefix s
        (2 * HLOZExternalUpper.externalLabelCount (prop44Psi m) - 1)
        (primedExternalLocalTime s (favoriteCreationHorizon m k s) x) x := by
  rcases hatom with ⟨omega, homega, rfl⟩
  obtain ⟨R, hR⟩ := Nat.not_even_iff_odd.mp hOdd
  have htime : favoriteCreationHorizon m k (simpleRandomWalk omega) =
      2 * R + 1 := by omega
  let q := HLOZExternalUpper.externalLabelCount (prop44Psi m)
  have hq : 0 < q := externalLabelCount_prop44Psi_pos m
  have hTleDirect := directCreationTime_le_prop44Psi_of_mem_canonicalHorizon
    m k hhorizon hsource.1
  have hTle : favoriteCreationHorizon m k (simpleRandomWalk omega) ≤
      prop44Psi m := by
    simpa only [favoriteCreationHorizon_eq_directCreationTime
      (simpleRandomWalk omega) hm hk] using hTleDirect
  have hfit := HLOZExternalUpper.external_time_fits_labelCount (prop44Psi m)
  have hRq : R ≤ q := by
    dsimp only [q] at hfit ⊢
    omega
  have hcurrent := favoriteCreationHorizon_endpoint_ne_of_localTime_lt
    m k hm hk hsource.1 x hxlt
  rw [htime]
  exact primedLazyLocalTime_odd_eq_inverseClockHoldingPrefix
    (fixedIncrementLabels z.2) (fixedIncrementLabels_nondistinguished z.2)
      hq homega.2 hRq x hxOdd (by simpa only [htime] using hcurrent)

/-- At an odd unprimed horizon, the only possible obstruction to the same
exact prefix identity is that the selected site is the endpoint of the
unfinished terminal pair.  Away from that endpoint, parity reduction exposes
the preceding completed even pair and the identity is canonical. -/
theorem paperLazyLocalTime_canonicalHorizon_eq_inversePrefix_of_odd_of_previous_ne
    (m k : ℕ)
    (v : FixedExternalLabels
      (HLOZExternalUpper.externalLabelCount (prop44Psi m)))
    {s : Path} (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hatom : s ∈ externalPathWalkAtom
      (List.ofFn (fixedIncrementLabels v)))
    (hhorizon : s ∈ xEastCanonicalHorizonEvent m k)
    (hsource : s ∈ xEastUnprimedSourceEvent m k)
    (x : Site) (hxEven : HLOZPairing.chessEven x)
    (hOdd : ¬ Even (favoriteCreationHorizon m k s))
    (hprevious : s (favoriteCreationHorizon m k s - 1) ≠ x) :
    paperLazyLocalTime s (favoriteCreationHorizon m k s) x =
      inverseClockHoldingPrefix s
        (2 * HLOZExternalUpper.externalLabelCount (prop44Psi m) - 1)
        (paperExternalLocalTime s (favoriteCreationHorizon m k s) x) x := by
  rcases hatom with ⟨omega, homega, rfl⟩
  obtain ⟨R, hR⟩ := Nat.not_even_iff_odd.mp hOdd
  have htime : favoriteCreationHorizon m k (simpleRandomWalk omega) =
      2 * R + 1 := by omega
  obtain ⟨N, hlabels⟩ := realized_terminalPairLabelsThrough
    (fixedIncrementLabels v) (fixedIncrementLabels_nondistinguished v) homega
  let q := HLOZExternalUpper.externalLabelCount (prop44Psi m)
  have hq : 0 < q := externalLabelCount_prop44Psi_pos m
  have hqN : q ≤ N := by
    have hcount := distinguished_add_terminal_count omega N
    rw [hlabels, List.length_ofFn] at hcount
    dsimp only [q]
    omega
  have hTleDirect := directCreationTime_le_prop44Psi_of_mem_canonicalHorizon
    m k hhorizon hsource.1
  have hTle : favoriteCreationHorizon m k (simpleRandomWalk omega) ≤
      prop44Psi m := by
    simpa only [favoriteCreationHorizon_eq_directCreationTime
      (simpleRandomWalk omega) hm hk] using hTleDirect
  have hfit := HLOZExternalUpper.external_time_fits_labelCount (prop44Psi m)
  have hRq : R ≤ q := by
    dsimp only [q] at hfit ⊢
    omega
  have hprevious' : simpleRandomWalk omega (2 * R) ≠ x := by
    have hsub : favoriteCreationHorizon m k (simpleRandomWalk omega) - 1 =
        2 * R := by omega
    simpa only [hsub] using hprevious
  have heven := paperLazyLocalTime_even_eq_inverseClockHoldingPrefix
    (fixedIncrementLabels v) hq hlabels (hRq.trans hqN) x hxEven hprevious'
  have hlazy := paperLazyLocalTime_odd_eq_even_of_chessEven omega R x hxEven
  have hext := paperExternalLocalTime_odd_eq_even_of_chessEven omega R x hxEven
  rw [htime]
  calc
    paperLazyLocalTime (simpleRandomWalk omega) (2 * R + 1) x =
        paperLazyLocalTime (simpleRandomWalk omega) (2 * R) x := hlazy
    _ = inverseClockHoldingPrefix (simpleRandomWalk omega) (2 * q - 1)
        (paperExternalLocalTime (simpleRandomWalk omega) (2 * R) x) x := heven
    _ = inverseClockHoldingPrefix (simpleRandomWalk omega) (2 * q - 1)
        (paperExternalLocalTime (simpleRandomWalk omega) (2 * R + 1) x) x := by
      rw [hext]

/-- Symmetrically, an even primed horizon reduces to its preceding completed
odd pair unless the selected site is the active terminal endpoint. -/
theorem primedLazyLocalTime_canonicalHorizon_eq_inversePrefix_of_even_of_previous_ne
    (m k : ℕ)
    (z : PrimedFixedExternalLabels
      (HLOZExternalUpper.externalLabelCount (prop44Psi m)))
    {s : Path} (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hatom : s ∈ primedExternalPathWalkAtom z.1
      (fixedIncrementLabels z.2))
    (hhorizon : s ∈ xEastCanonicalHorizonEvent m k)
    (hsource : s ∈ xEastPrimedSourceEvent m k)
    (x : Site) (hxOdd : ¬ HLOZPairing.chessEven x)
    (hEven : Even (favoriteCreationHorizon m k s))
    (hprevious : s (favoriteCreationHorizon m k s - 1) ≠ x) :
    primedLazyLocalTime s (favoriteCreationHorizon m k s) x =
      primedInverseClockHoldingPrefix s
        (2 * HLOZExternalUpper.externalLabelCount (prop44Psi m) - 1)
        (primedExternalLocalTime s (favoriteCreationHorizon m k s) x) x := by
  rcases hatom with ⟨omega, homega, rfl⟩
  have hpos := favoriteCreationHorizon_pos m k hm hk hsource.1
  obtain ⟨U, hU⟩ := hEven
  obtain ⟨R, htime⟩ : ∃ R : ℕ,
      favoriteCreationHorizon m k (simpleRandomWalk omega) = 2 * R + 2 := by
    refine ⟨U - 1, ?_⟩
    omega
  let q := HLOZExternalUpper.externalLabelCount (prop44Psi m)
  have hq : 0 < q := externalLabelCount_prop44Psi_pos m
  have hTleDirect := directCreationTime_le_prop44Psi_of_mem_canonicalHorizon
    m k hhorizon hsource.1
  have hTle : favoriteCreationHorizon m k (simpleRandomWalk omega) ≤
      prop44Psi m := by
    simpa only [favoriteCreationHorizon_eq_directCreationTime
      (simpleRandomWalk omega) hm hk] using hTleDirect
  have hfit := HLOZExternalUpper.external_time_fits_labelCount (prop44Psi m)
  have hRq : R ≤ q := by
    dsimp only [q] at hfit ⊢
    omega
  have hprevious' : simpleRandomWalk omega (2 * R + 1) ≠ x := by
    have hsub : favoriteCreationHorizon m k (simpleRandomWalk omega) - 1 =
        2 * R + 1 := by omega
    simpa only [hsub] using hprevious
  have hodd := primedLazyLocalTime_odd_eq_inverseClockHoldingPrefix
    (fixedIncrementLabels z.2) (fixedIncrementLabels_nondistinguished z.2)
      hq homega.2 hRq x hxOdd hprevious'
  have hlazy := primedLazyLocalTime_even_eq_odd_of_chessOdd omega R x hxOdd
  have hext := primedExternalLocalTime_even_eq_odd_of_chessOdd omega R x hxOdd
  rw [htime]
  calc
    primedLazyLocalTime (simpleRandomWalk omega) (2 * R + 2) x =
        primedLazyLocalTime (simpleRandomWalk omega) (2 * R + 1) x := hlazy
    _ = primedInverseClockHoldingPrefix (simpleRandomWalk omega) (2 * q - 1)
        (primedExternalLocalTime (simpleRandomWalk omega) (2 * R + 1) x) x := hodd
    _ = primedInverseClockHoldingPrefix (simpleRandomWalk omega) (2 * q - 1)
        (primedExternalLocalTime (simpleRandomWalk omega) (2 * R + 2) x) x := by
      rw [hext]

theorem inverseClockProfile_eq_xEastEncodedProfile_of_mem_fixedAtom
    {q : ℕ} (v : FixedExternalLabels q) {s : Path}
    (hs : s ∈ externalPathWalkAtom
      (List.ofFn (fixedIncrementLabels v)))
    (x : Site) (hx : HLOZPairing.chessEven x) (hq : 0 < q) :
    inverseClockProfile s (2 * q - 1) x =
      xEastEncodedProfile (fixedIncrementLabels v) x := by
  rcases hs with ⟨omega, homega, rfl⟩
  obtain ⟨N, hlabels⟩ := realized_terminalPairLabelsThrough
    (fixedIncrementLabels v) (fixedIncrementLabels_nondistinguished v) homega
  exact inverseClockProfile_eq_chronological_length
    (fixedIncrementLabels v) hlabels x hx hq

theorem primedInverseClockProfile_eq_xEastEncodedProfile_of_mem_fixedAtom
    {q : ℕ} (z : PrimedFixedExternalLabels q) {s : Path}
    (hs : s ∈ primedExternalPathWalkAtom z.1
      (fixedIncrementLabels z.2))
    (x : Site) (hx : ¬ HLOZPairing.chessEven x) (hq : 0 < q) :
    primedInverseClockProfile s (2 * q - 1) x =
      xEastPrimedEncodedProfile z.1 (fixedIncrementLabels z.2) x := by
  rcases hs with ⟨omega, homega, rfl⟩
  obtain ⟨N, hlabels⟩ := realized_terminalPairLabelsThrough
    (fixedIncrementLabels z.2) (fixedIncrementLabels_nondistinguished z.2)
      homega.2
  have hprofile := primedInverseClockProfile_eq_chronological_length
    (fixedIncrementLabels z.2) hlabels x hx hq
  rw [homega.1] at hprofile
  simpa only [xEastPrimedEncodedProfile] using hprofile

/-- The unprimed endpoint cover on a canonical good atom is deterministic.
The fixed-label reconstruction above supplies membership in the canonical
site set for the one `Theta` witness; no global claim about every visited
site is required. -/
theorem xEastUnprimedCanonical_theta_subset
    (m k : ℕ)
    (v : FixedExternalLabels
      (HLOZExternalUpper.externalLabelCount (prop44Psi m)))
    (hm : 2 ≤ m) (hk : 1 ≤ k) :
    externalPathWalkAtom (List.ofFn (fixedIncrementLabels v)) ∩
        xEastCanonicalHorizonEvent m k ∩ xEastUnprimedSourceEvent m k ⊆
      externalPathWalkAtom (List.ofFn (fixedIncrementLabels v)) ∩
        xEastCanonicalHorizonEvent m k ∩ xEastUnprimedSourceEvent m k ∩
          (intervalStoppedThetaMinusCappedEvent
              (xEastUnprimedFixedSites v) m (sourceBandLowerNat m) k ∪
            intervalStoppedThetaPlusEvent (xEastUnprimedFixedSites v) m m k) := by
  classical
  intro s hs
  rcases hs with ⟨⟨hatom, hhorizon⟩, hsource⟩
  refine ⟨⟨⟨hatom, hhorizon⟩, hsource⟩, ?_⟩
  rcases hsource with ⟨hprefix, htheta⟩
  have hTle := directCreationTime_le_prop44Psi_of_mem_canonicalHorizon
    m k hhorizon hprefix
  change (stoppedThetaHalfSites paperUnprimedProfile
      HLOZPairing.chessEven false 10 s m k ∪
    stoppedThetaHalfSites paperUnprimedProfile
      HLOZPairing.chessEven true 10 s m k).Nonempty at htheta
  rcases htheta with ⟨x, hx⟩
  have hxsite : x ∈ xEastUnprimedFixedSites v :=
    xEastUnprimedThetaSite_mem_fixedSites_of_time_le m k v
      (by omega) hk hatom hTle hx
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rcases Finset.mem_union.mp hx with hx | hx
  · left
    apply Set.mem_iUnion_of_mem x
    apply Set.mem_iUnion_of_mem hxsite
    rw [intervalStoppedThetaMinusCappedAt]
    refine ⟨mem_intervalStoppedThetaMinusAt_of_mem_stoppedThetaHalfSites
      HLOZPairing.chessEven s m j hm x (by
        simpa only [paperUnprimedProfile] using hx), ?_⟩
    have hxData := hx
    simp only [stoppedThetaHalfSites, Finset.mem_filter,
      Bool.false_eq_true, ↓reduceIte] at hxData
    rcases hxData with ⟨_hxVisited, _hxFinite, _hxParity, _hxLower,
      hxUpper, _hxExternal⟩
    change localTime s (favoriteCreationHorizon m (j + 1) s) x < m
    rw [favoriteCreationHorizon_eq_directCreationTime s m j hm]
    exact_mod_cast hxUpper
  · right
    apply Set.mem_iUnion_of_mem x
    apply Set.mem_iUnion_of_mem hxsite
    exact mem_intervalStoppedThetaPlusAt_of_mem_stoppedThetaHalfSites
      HLOZPairing.chessEven s m j hm x (by
        simpa only [paperUnprimedProfile] using hx)

/-- The primed endpoint cover is automatic on the same canonical horizon.
The adjacent-pair shift reconstructs the unique odd fixed site carrying the
Theta witness, after which the source endpoint inequalities are direct. -/
theorem xEastPrimedCanonical_theta_subset
    (m k : ℕ)
    (z : PrimedFixedExternalLabels
      (HLOZExternalUpper.externalLabelCount (prop44Psi m)))
    (hm : 2 ≤ m) (hk : 1 ≤ k) :
    primedExternalPathWalkAtom z.1 (fixedIncrementLabels z.2) ∩
        xEastCanonicalHorizonEvent m k ∩ xEastPrimedSourceEvent m k ⊆
      primedExternalPathWalkAtom z.1 (fixedIncrementLabels z.2) ∩
        xEastCanonicalHorizonEvent m k ∩ xEastPrimedSourceEvent m k ∩
          (primedIntervalStoppedThetaMinusCappedEvent
              (concretePrimedShiftedDeletionClock m k
                (2 * HLOZExternalUpper.externalLabelCount (prop44Psi m) - 1))
              (xEastPrimedFixedSites z) (sourceBandLowerNat m) ∪
            primedIntervalStoppedThetaPlusEvent
              (concretePrimedShiftedDeletionClock m k
                (2 * HLOZExternalUpper.externalLabelCount (prop44Psi m) - 1))
              (xEastPrimedFixedSites z) m) := by
  classical
  intro s hs
  rcases hs with ⟨⟨hatom, hhorizon⟩, hsource⟩
  refine ⟨⟨⟨hatom, hhorizon⟩, hsource⟩, ?_⟩
  rcases hsource with ⟨hprefix, htheta⟩
  have hTle := directCreationTime_le_prop44Psi_of_mem_canonicalHorizon
    m k hhorizon hprefix
  change (stoppedThetaHalfSites paperPrimedProfile
      (fun x ↦ ¬ HLOZPairing.chessEven x) false 10 s m k ∪
    stoppedThetaHalfSites paperPrimedProfile
      (fun x ↦ ¬ HLOZPairing.chessEven x) true 10 s m k).Nonempty at htheta
  rcases htheta with ⟨x, hx⟩
  have hxsite : x ∈ xEastPrimedFixedSites z :=
    xEastPrimedThetaSite_mem_fixedSites_of_time_le m k z
      (by omega) hk hatom hTle hx
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rcases Finset.mem_union.mp hx with hx | hx
  · left
    simp only [stoppedThetaHalfSites, Finset.mem_filter, Bool.false_eq_true,
      ↓reduceIte] at hx
    rcases hx with ⟨_hxVisited, _hxFinite, _hxParity, hxLower, hxUpper,
      hxExternal⟩
    apply Set.mem_iUnion_of_mem x
    apply Set.mem_iUnion_of_mem hxsite
    rw [primedIntervalStoppedThetaMinusCappedAt]
    refine ⟨?_, ?_⟩
    · change primedExternalLocalTime s
          (favoriteCreationHorizon m (j + 1) s) x ≤
            intervalLowCut m (sourceBandLowerNat m) ∧
        sourceBandLowerNat m ≤
          localTime s (favoriteCreationHorizon m (j + 1) s) x
      rw [favoriteCreationHorizon_eq_directCreationTime s m j hm]
      refine ⟨le_intervalLowCut_of_le_sourceBandThreshold m _ ?_, ?_⟩
      · simpa only [paperPrimedProfile, Nat.cast_ofNat, one_mul] using hxExternal
      · exact (sourceBandLowerNat_le_iff m _).mpr hxLower
    · change localTime s (favoriteCreationHorizon m (j + 1) s) x < m
      rw [favoriteCreationHorizon_eq_directCreationTime s m j hm]
      exact_mod_cast hxUpper
  · right
    simp only [stoppedThetaHalfSites, Finset.mem_filter, ↓reduceIte] at hx
    rcases hx with ⟨_hxVisited, _hxFinite, _hxParity, _hxLower, hxUpper,
      hxExternal⟩
    apply Set.mem_iUnion_of_mem x
    apply Set.mem_iUnion_of_mem hxsite
    change intervalHighCut m m ≤
        primedExternalLocalTime s
          (favoriteCreationHorizon m (j + 1) s) x ∧
      localTime s (favoriteCreationHorizon m (j + 1) s) x < m
    rw [favoriteCreationHorizon_eq_directCreationTime s m j hm]
    refine ⟨intervalHighCut_top_le_of_sourceBandThreshold m _ ?_, ?_⟩
    · simpa only [paperPrimedProfile, Nat.cast_ofNat, one_mul] using hxExternal
    · exact_mod_cast hxUpper

/-- Appendix A and the Proposition-1.3 bridge supply one copy of the source
exceptional rate for the complement of the canonical horizon, uniformly in
the number `k` of creation sites. -/
theorem eventually_xEastCanonicalHorizon_compl_measure_le
    (hdisk : HLOZProp13FromAppendix.AppendixDiskEstimate) :
    ∀ᶠ m : ℕ in atTop, ∀ k : ℕ,
      simpleRandomWalkLaw (xEastCanonicalHorizonEvent m k)ᶜ ≤
        sourceExceptionalRateWithPrefactor m 1 kappa := by
  have hprop13 :=
    HLOZProp13FromAppendix.eventually_nearCritical_prop13_bound hdisk
  filter_upwards [
    HLOZNearCriticalBridge.eventually_level_lt_proposition13Threshold_nearCriticalHorizon,
    hprop13, eventually_exp_neg_le_sourceExceptionalRate]
    with m hthreshold hprop13m hrate
  intro k
  rw [xEastCanonicalHorizonEvent, compl_compl]
  calc
    simpleRandomWalkLaw
        (HLOZNearCriticalBridge.lateOnThresholdEvent
          HLOZNearCriticalBridge.nearCriticalHorizon m k) ≤
      simpleRandomWalkLaw
        (HLOZNearCriticalBridge.lowerMaxEvent
          HLOZNearCriticalBridge.nearCriticalHorizon m) :=
      measure_mono
        (HLOZNearCriticalBridge.lateOnThresholdEvent_subset_lowerMaxEvent
          HLOZNearCriticalBridge.nearCriticalHorizon m k)
    _ ≤ simpleRandomWalkLaw
        (HLOZNearCriticalBridge.proposition13LowerTailEvent
          (HLOZNearCriticalBridge.nearCriticalHorizon m)) :=
      measure_mono
        (HLOZNearCriticalBridge.lowerMaxEvent_subset_proposition13LowerTailEvent
          HLOZNearCriticalBridge.nearCriticalHorizon m hthreshold)
    _ ≤ ENNReal.ofReal (Real.exp (-(m : ℝ))) := hprop13m
    _ ≤ sourceExceptionalRateWithPrefactor m 1 kappa := hrate

/-- The irreducible stopped-clock input on one good unprimed label atom.
The site set is now the canonical fixed-label set.  Parity, both capacities,
the inverse profile, and both cardinality inequalities are theorems; only
the exact endpoint inclusion and the two one-sided stopped-prefix
comparisons remain here.  In particular this interface does not assert the
false stronger claims that *all* visited sites have one chess parity or that
an unfinished terminal holding block equals its completed inverse block. -/
structure XEastUnprimedGoodAtomClockInputs
    (m k q : ℕ) (v : FixedExternalLabels q) (H : Set Path) where
  theta_subset :
    externalPathWalkAtom (List.ofFn (fixedIncrementLabels v)) ∩ H ∩
        xEastUnprimedSourceEvent m k ⊆
      externalPathWalkAtom (List.ofFn (fixedIncrementLabels v)) ∩ H ∩
        xEastUnprimedSourceEvent m k ∩
          (intervalStoppedThetaMinusCappedEvent
              (xEastUnprimedFixedSites v) m (sourceBandLowerNat m) k ∪
            intervalStoppedThetaPlusEvent (xEastUnprimedFixedSites v) m m k)
  minus_compatible : ∀ {s x},
    s ∈ externalPathWalkAtom (List.ofFn (fixedIncrementLabels v)) ∩ H ∩
        xEastUnprimedSourceEvent m k →
    x ∈ xEastUnprimedFixedSites v →
    s ∈ intervalStoppedThetaMinusCappedAt m
        (sourceBandLowerNat m) k x →
      SourceClockPrefixCompatibleAt s (favoriteCreationHorizon m k s)
        (2 * q - 1)
          (intervalDotIndex m (sourceBandLowerNat m)
            (xEastEncodedProfile (fixedIncrementLabels v)) x) x
  plus_compatible : ∀ {s x},
    s ∈ externalPathWalkAtom (List.ofFn (fixedIncrementLabels v)) ∩ H ∩
        xEastUnprimedSourceEvent m k →
    x ∈ xEastUnprimedFixedSites v →
    s ∈ intervalStoppedThetaPlusAt m m k x →
      SourceClockInitialPrefixCompatibleAt s
        (favoriteCreationHorizon m k s) (2 * q - 1)
          (intervalPriorHighCut m m) x

noncomputable def XEastUnprimedGoodAtomClockInputs.toExternalAtomInputs
    {m k q : ℕ} {v : FixedExternalLabels q} {H : Set Path}
    (h : XEastUnprimedGoodAtomClockInputs m k q v H)
    (hq : 0 < q)
    (horizon_card : (q : ℝ) ≤
      Real.exp (16 * Real.sqrt (m : ℝ)))
    (hv : v ∈ xEastUnprimedGoodFixedAtoms m q) :
    XEastUnprimedExternalAtomInputs m k q
      (fixedIncrementLabels v) H where
  nondistinguished := fixedIncrementLabels_nondistinguished v
  positiveLength := hq
  sites := xEastUnprimedFixedSites v
  sitesEven := xEastUnprimedFixedSites_even v
  minus_capacity := fun x _ ↦ xEastUnprimed_minus_capacity v x
  plus_capacity := xEastUnprimed_plus_capacity v
  theta_subset := h.theta_subset
  minus_compatible := h.minus_compatible
  plus_compatible := h.plus_compatible
  prop44_card := by
    exact mem_xEastUnprimedGoodFixedAtoms_iff.mp hv
  horizon_card := (Nat.cast_le.mpr (card_xEastUnprimedFixedSites_le v)).trans
    horizon_card

/-- Earliest unprimed fixed-depth source input.  The atom set is the literal
definable set of good label vectors.  Its bad-label probability is no longer
an input: it is Proposition 4.4, proved above for the canonical depth.  Thus
only the source-horizon estimate remains probabilistic data here.  The
coefficient equation reserves one copy of the exceptional rate for the
internally supplied Proposition-4.4 bound. -/
structure XEastUnprimedFixedDepthInputs
    (m k q badCoeff : ℕ) where
  positiveDepth : 0 < q
  horizon : Set Path
  clockInputs : ∀ v ∈ xEastUnprimedGoodFixedAtoms m q,
    XEastUnprimedGoodAtomClockInputs m k q v horizon
  horizonBadCoeff : ℕ
  badCoeff_eq : horizonBadCoeff + 1 = badCoeff
  horizon_bad_bound : simpleRandomWalkLaw horizonᶜ ≤
    sourceExceptionalRateWithPrefactor m horizonBadCoeff kappa

theorem XEastUnprimedFixedDepthInputs.theta_measure_le_add
    {m k q badCoeff : ℕ}
    (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hs : SourceIntervalScale m (sourceBandLowerNat m) ∧
      SourceUpperScale m m)
    (horizon_card : (q : ℝ) ≤
      Real.exp (16 * Real.sqrt (m : ℝ)))
    (hlabels : simpleRandomWalkLaw (xEastUnprimedBadLabelUnion m q) ≤
      sourceExceptionalRateWithPrefactor m 1 kappa)
    (h : XEastUnprimedFixedDepthInputs m k q badCoeff) :
    simpleRandomWalkLaw (xEastUnprimedSourceEvent m k) ≤
      sourceExceptionalRateWithPrefactor m badCoeff kappa +
        sourceProp45OneSideError m := by
  exact measure_le_bad_add_of_finite_conditional_partition
    simpleRandomWalkLaw (xEastUnprimedGoodFixedAtoms m q)
    (fun v ↦ externalPathWalkAtom (List.ofFn (fixedIncrementLabels v)))
    (xEastUnprimedSourceEvent m k) h.horizon
      (xEastUnprimedPartitionBadEvent m q h.horizon)
    (sourceProp45OneSideError m)
    (sourceExceptionalRateWithPrefactor m badCoeff kappa)
    (fun v _ ↦ measurableSet_externalPathWalkAtom
      (List.ofFn (fixedIncrementLabels v)))
    (fun v _ w _ hvw ↦ pairwise_unprimedFixedAtoms q
      (Set.mem_univ v) (Set.mem_univ w) hvw)
    (xEastUnprimed_goodAtom_cover m k q h.horizon)
    (xEastUnprimedPartitionBadEvent_measure_le m q badCoeff h.horizon
      (by
        calc
          simpleRandomWalkLaw
              (xEastUnprimedSourceBadEvent m q h.horizon) ≤
              sourceExceptionalRateWithPrefactor m
                (h.horizonBadCoeff + 1) kappa :=
            xEastUnprimedSourceBadEvent_measure_le m q
              h.horizonBadCoeff 1 h.horizon
              h.horizon_bad_bound hlabels
          _ = sourceExceptionalRateWithPrefactor m badCoeff kappa :=
            congrArg (fun c ↦ sourceExceptionalRateWithPrefactor m c kappa)
              h.badCoeff_eq))
    (fun v hv ↦ ((h.clockInputs v hv).toExternalAtomInputs
      h.positiveDepth horizon_card hv).conditional_theta_le hs)

/-- Primed exact stopped-clock counterpart of
`XEastUnprimedGoodAtomClockInputs`. -/
structure XEastPrimedGoodAtomClockInputs
    (m k q : ℕ) (z : PrimedFixedExternalLabels q) (H : Set Path) where
  theta_subset :
    primedExternalPathWalkAtom z.1 (fixedIncrementLabels z.2) ∩ H ∩
        xEastPrimedSourceEvent m k ⊆
      primedExternalPathWalkAtom z.1 (fixedIncrementLabels z.2) ∩ H ∩
        xEastPrimedSourceEvent m k ∩
          (primedIntervalStoppedThetaMinusCappedEvent
              (concretePrimedShiftedDeletionClock m k (2 * q - 1))
              (xEastPrimedFixedSites z) (sourceBandLowerNat m) ∪
            primedIntervalStoppedThetaPlusEvent
              (concretePrimedShiftedDeletionClock m k (2 * q - 1))
              (xEastPrimedFixedSites z) m)
  minus_compatible : ∀ {s x},
    s ∈ primedExternalPathWalkAtom z.1 (fixedIncrementLabels z.2) ∩ H ∩
        xEastPrimedSourceEvent m k →
    x ∈ xEastPrimedFixedSites z →
    s ∈ primedIntervalStoppedThetaMinusCappedAt
        (concretePrimedShiftedDeletionClock m k (2 * q - 1))
          (sourceBandLowerNat m) x →
      let clock := concretePrimedShiftedDeletionClock m k (2 * q - 1)
      clock.stoppedExternal s x ≤ clock.inverseProfile s x ∧
        clock.stoppedLazy s x ≤ clock.inverseHoldingPrefix s
          (intervalDotIndex m (sourceBandLowerNat m)
            (xEastPrimedEncodedProfile z.1
              (fixedIncrementLabels z.2)) x) x
  plus_compatible : ∀ {s x},
    s ∈ primedExternalPathWalkAtom z.1 (fixedIncrementLabels z.2) ∩ H ∩
        xEastPrimedSourceEvent m k →
    x ∈ xEastPrimedFixedSites z →
    s ∈ primedIntervalStoppedThetaPlusAt
        (concretePrimedShiftedDeletionClock m k (2 * q - 1)) m x →
      let clock := concretePrimedShiftedDeletionClock m k (2 * q - 1)
      clock.stoppedExternal s x ≤ clock.inverseProfile s x ∧
        clock.inverseHoldingPrefix s (intervalPriorHighCut m m) x ≤
          clock.stoppedLazy s x

noncomputable def XEastPrimedGoodAtomClockInputs.toExternalAtomInputs
    {m k q : ℕ} {z : PrimedFixedExternalLabels q} {H : Set Path}
    (h : XEastPrimedGoodAtomClockInputs m k q z H)
    (hq : 0 < q)
    (horizon_card : (q : ℝ) ≤
      Real.exp (16 * Real.sqrt (m : ℝ)))
    (hz : z ∈ xEastPrimedGoodFixedAtoms m q) :
    XEastPrimedExternalAtomInputs m k q z.1
      (fixedIncrementLabels z.2) H where
  nondistinguished := fixedIncrementLabels_nondistinguished z.2
  positiveLength := hq
  sites := xEastPrimedFixedSites z
  sitesOdd := xEastPrimedFixedSites_odd z
  minus_capacity := fun x _ ↦ xEastPrimed_minus_capacity z x
  plus_capacity := xEastPrimed_plus_capacity z
  theta_subset := h.theta_subset
  minus_compatible := h.minus_compatible
  plus_compatible := h.plus_compatible
  prop44_card := by
    exact mem_xEastPrimedGoodFixedAtoms_iff.mp hz
  horizon_card := (Nat.cast_le.mpr (card_xEastPrimedFixedSites_le z)).trans
    horizon_card

/-- Primed counterpart of `XEastUnprimedFixedDepthInputs`.  Its canonical
atoms additionally fix the independent first direction.  As on the
unprimed side, Proposition 4.4 supplies the bad-label probability
internally, so the structure records only the horizon error. -/
structure XEastPrimedFixedDepthInputs
    (m k q badCoeff : ℕ) where
  positiveDepth : 0 < q
  horizon : Set Path
  clockInputs : ∀ z ∈ xEastPrimedGoodFixedAtoms m q,
    XEastPrimedGoodAtomClockInputs m k q z horizon
  horizonBadCoeff : ℕ
  badCoeff_eq : horizonBadCoeff + 1 = badCoeff
  horizon_bad_bound : simpleRandomWalkLaw horizonᶜ ≤
    sourceExceptionalRateWithPrefactor m horizonBadCoeff kappa

theorem XEastPrimedFixedDepthInputs.theta_measure_le_add
    {m k q badCoeff : ℕ}
    (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hs : SourceIntervalScale m (sourceBandLowerNat m) ∧
      SourceUpperScale m m)
    (horizon_card : (q : ℝ) ≤
      Real.exp (16 * Real.sqrt (m : ℝ)))
    (hlabels : simpleRandomWalkLaw (xEastPrimedBadLabelUnion m q) ≤
      sourceExceptionalRateWithPrefactor m 1 kappa)
    (h : XEastPrimedFixedDepthInputs m k q badCoeff) :
    simpleRandomWalkLaw (xEastPrimedSourceEvent m k) ≤
      sourceExceptionalRateWithPrefactor m badCoeff kappa +
        sourceProp45OneSideError m := by
  exact measure_le_bad_add_of_finite_conditional_partition
    simpleRandomWalkLaw (xEastPrimedGoodFixedAtoms m q)
    (fun z ↦ primedExternalPathWalkAtom z.1 (fixedIncrementLabels z.2))
    (xEastPrimedSourceEvent m k) h.horizon
      (xEastPrimedPartitionBadEvent m q h.horizon)
    (sourceProp45OneSideError m)
    (sourceExceptionalRateWithPrefactor m badCoeff kappa)
    (fun z _ ↦ measurableSet_primedExternalPathWalkAtom z.1
      (fixedIncrementLabels z.2))
    (fun z _ w _ hzw ↦ pairwise_primedFixedAtoms q
      (Set.mem_univ z) (Set.mem_univ w) hzw)
    (xEastPrimed_goodAtom_cover m k q h.horizon)
    (xEastPrimedPartitionBadEvent_measure_le m q badCoeff h.horizon
      (by
        calc
          simpleRandomWalkLaw
              (xEastPrimedSourceBadEvent m q h.horizon) ≤
              sourceExceptionalRateWithPrefactor m
                (h.horizonBadCoeff + 1) kappa :=
            xEastPrimedSourceBadEvent_measure_le m q
              h.horizonBadCoeff 1 h.horizon
              h.horizon_bad_bound hlabels
          _ = sourceExceptionalRateWithPrefactor m badCoeff kappa :=
            congrArg (fun c ↦ sourceExceptionalRateWithPrefactor m c kappa)
              h.badCoeff_eq))
    (fun z hz ↦ ((h.clockInputs z hz).toExternalAtomInputs
      h.positiveDepth horizon_card hz).conditional_theta_le hs)

/-- The full `X₁` stopped event is the union of the two separately
conditioned sides. -/
theorem stoppedThetaEvent_xEast_eq (m k : ℕ) :
    stoppedThetaEvent (canonicalProfiles ⟨0, by omega⟩)
      (canonicalCStar ⟨0, by omega⟩) m k =
        xEastUnprimedThetaEvent m k ∪ xEastPrimedThetaEvent m k := by
  rw [canonicalProfiles_xEast]
  ext s
  simp only [stoppedThetaEvent, stoppedThetaSites, canonicalCStar,
    canonicalExternalProfilePair, xEastUnprimedThetaEvent,
    xEastPrimedThetaEvent, Set.mem_setOf_eq, Set.mem_union,
    Finset.union_nonempty]
  tauto

/-- The pairing-independent threshold event splits into the two temporal
deletion phases. -/
theorem thresholdStoppedThetaEvent_xEast_eq (m k : ℕ) :
    hlozThresholdTimeEventK m (k + 1) ∩
      stoppedThetaEvent (canonicalProfiles ⟨0, by omega⟩)
        (canonicalCStar ⟨0, by omega⟩) m k =
      xEastUnprimedSourceEvent m k ∪ xEastPrimedSourceEvent m k := by
  rw [stoppedThetaEvent_xEast_eq]
  ext s
  simp only [xEastUnprimedSourceEvent, xEastPrimedSourceEvent,
    Set.mem_inter_iff, Set.mem_union]
  tauto

/-- Every X-east pairing-history event is contained in the common temporal
threshold event bounded by the two fixed-label atomizations. -/
theorem prefixStoppedThetaEvent_xEast_subset (m k : ℕ) :
    prefixPairingEvent m ⟨0, by omega⟩ (k + 1) ∩
      stoppedThetaEvent (canonicalProfiles ⟨0, by omega⟩)
        (canonicalCStar ⟨0, by omega⟩) m k ⊆
      xEastUnprimedSourceEvent m k ∪ xEastPrimedSourceEvent m k := by
  rw [← thresholdStoppedThetaEvent_xEast_eq]
  intro s hs
  exact ⟨hs.1.1, hs.2⟩

/-- The full `X₁` source decomposition contains two *different* finite
partitions, one for each pairing phase. -/
structure XEastSeparateFiniteAtomizations
    (m k unprimedBadCoeff primedBadCoeff : ℕ) where
  unprimed : XEastUnprimedFiniteAtomization m k unprimedBadCoeff
  primed : XEastPrimedFiniteAtomization m k primedBadCoeff

theorem XEastSeparateFiniteAtomizations.theta_measure_le
    {m k unprimedBadCoeff primedBadCoeff : ℕ}
    (hs : SourceIntervalScale m (sourceBandLowerNat m) ∧
      SourceUpperScale m m)
    (habsorb : sourceProp45OneSideError m ≤
      sourceExceptionalRateWithPrefactor m 3 kappa)
    (h : XEastSeparateFiniteAtomizations m k
      unprimedBadCoeff primedBadCoeff) :
    simpleRandomWalkLaw
        (prefixPairingEvent m ⟨0, by omega⟩ (k + 1) ∩
          stoppedThetaEvent (canonicalProfiles ⟨0, by omega⟩)
            (canonicalCStar ⟨0, by omega⟩) m k) ≤
      sourceExceptionalRateWithPrefactor m
        (unprimedBadCoeff + primedBadCoeff + 6) kappa := by
  calc
    simpleRandomWalkLaw
        (prefixPairingEvent m ⟨0, by omega⟩ (k + 1) ∩
          stoppedThetaEvent (canonicalProfiles ⟨0, by omega⟩)
            (canonicalCStar ⟨0, by omega⟩) m k) ≤
      simpleRandomWalkLaw
        (xEastUnprimedSourceEvent m k ∪ xEastPrimedSourceEvent m k) :=
      measure_mono (prefixStoppedThetaEvent_xEast_subset m k)
    simpleRandomWalkLaw
        (xEastUnprimedSourceEvent m k ∪ xEastPrimedSourceEvent m k) ≤
      simpleRandomWalkLaw (xEastUnprimedSourceEvent m k) +
        simpleRandomWalkLaw (xEastPrimedSourceEvent m k) := measure_union_le _ _
    _ ≤ sourceExceptionalRateWithPrefactor m (unprimedBadCoeff + 3) kappa +
        sourceExceptionalRateWithPrefactor m (primedBadCoeff + 3) kappa :=
      add_le_add (h.unprimed.theta_measure_le hs habsorb)
        (h.primed.theta_measure_le hs habsorb)
    _ = sourceExceptionalRateWithPrefactor m
        (unprimedBadCoeff + primedBadCoeff + 6) kappa := by
      simp only [sourceExceptionalRateWithPrefactor]
      push_cast
      ring

theorem XEastUnprimedFixedDepthInputs.theta_measure_le
    {m k q badCoeff : ℕ}
    (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hs : SourceIntervalScale m (sourceBandLowerNat m) ∧
      SourceUpperScale m m)
    (horizon_card : (q : ℝ) ≤
      Real.exp (16 * Real.sqrt (m : ℝ)))
    (habsorb : sourceProp45OneSideError m ≤
      sourceExceptionalRateWithPrefactor m 3 kappa)
    (hlabels : simpleRandomWalkLaw (xEastUnprimedBadLabelUnion m q) ≤
      sourceExceptionalRateWithPrefactor m 1 kappa)
    (h : XEastUnprimedFixedDepthInputs m k q badCoeff) :
    simpleRandomWalkLaw (xEastUnprimedSourceEvent m k) ≤
      sourceExceptionalRateWithPrefactor m (badCoeff + 3) kappa := by
  calc
    simpleRandomWalkLaw (xEastUnprimedSourceEvent m k) ≤
        sourceExceptionalRateWithPrefactor m badCoeff kappa +
          sourceProp45OneSideError m :=
      h.theta_measure_le_add hm hk hs horizon_card hlabels
    _ ≤ sourceExceptionalRateWithPrefactor m badCoeff kappa +
        sourceExceptionalRateWithPrefactor m 3 kappa := add_le_add le_rfl habsorb
    _ = sourceExceptionalRateWithPrefactor m (badCoeff + 3) kappa := by
      simp only [sourceExceptionalRateWithPrefactor]
      push_cast
      ring

theorem XEastPrimedFixedDepthInputs.theta_measure_le
    {m k q badCoeff : ℕ}
    (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hs : SourceIntervalScale m (sourceBandLowerNat m) ∧
      SourceUpperScale m m)
    (horizon_card : (q : ℝ) ≤
      Real.exp (16 * Real.sqrt (m : ℝ)))
    (habsorb : sourceProp45OneSideError m ≤
      sourceExceptionalRateWithPrefactor m 3 kappa)
    (hlabels : simpleRandomWalkLaw (xEastPrimedBadLabelUnion m q) ≤
      sourceExceptionalRateWithPrefactor m 1 kappa)
    (h : XEastPrimedFixedDepthInputs m k q badCoeff) :
    simpleRandomWalkLaw (xEastPrimedSourceEvent m k) ≤
      sourceExceptionalRateWithPrefactor m (badCoeff + 3) kappa := by
  calc
    simpleRandomWalkLaw (xEastPrimedSourceEvent m k) ≤
        sourceExceptionalRateWithPrefactor m badCoeff kappa +
          sourceProp45OneSideError m :=
      h.theta_measure_le_add hm hk hs horizon_card hlabels
    _ ≤ sourceExceptionalRateWithPrefactor m badCoeff kappa +
        sourceExceptionalRateWithPrefactor m 3 kappa := add_le_add le_rfl habsorb
    _ = sourceExceptionalRateWithPrefactor m (badCoeff + 3) kappa := by
      simp only [sourceExceptionalRateWithPrefactor]
      push_cast
      ring

/-- Reduced two-phase source package.  The atom index sets, their
disjointness, their full-measure covers, and all conditional laws are now
theorems.  Only the deterministic stopped compatibility/cardinality facts
and the source horizon exceptional estimate remain as fields. -/
structure XEastSeparateFixedDepthInputs
    (m k unprimedBadCoeff primedBadCoeff : ℕ) where
  unprimed : XEastUnprimedFixedDepthInputs m k
    (HLOZExternalUpper.externalLabelCount (prop44Psi m)) unprimedBadCoeff
  primed : XEastPrimedFixedDepthInputs m k
    (HLOZExternalUpper.externalLabelCount (prop44Psi m)) primedBadCoeff

theorem XEastSeparateFixedDepthInputs.theta_measure_le
    {m k unprimedBadCoeff primedBadCoeff : ℕ}
    (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hs : SourceIntervalScale m (sourceBandLowerNat m) ∧
      SourceUpperScale m m)
    (horizon_card :
      (HLOZExternalUpper.externalLabelCount (prop44Psi m) : ℝ) ≤
        Real.exp (16 * Real.sqrt (m : ℝ)))
    (habsorb : sourceProp45OneSideError m ≤
      sourceExceptionalRateWithPrefactor m 3 kappa)
    (hunprimedLabels : simpleRandomWalkLaw
        (xEastUnprimedBadLabelUnion m
          (HLOZExternalUpper.externalLabelCount (prop44Psi m))) ≤
      sourceExceptionalRateWithPrefactor m 1 kappa)
    (hprimedLabels : simpleRandomWalkLaw
        (xEastPrimedBadLabelUnion m
          (HLOZExternalUpper.externalLabelCount (prop44Psi m))) ≤
      sourceExceptionalRateWithPrefactor m 1 kappa)
    (h : XEastSeparateFixedDepthInputs m k
      unprimedBadCoeff primedBadCoeff) :
    simpleRandomWalkLaw
        (prefixPairingEvent m ⟨0, by omega⟩ (k + 1) ∩
          stoppedThetaEvent (canonicalProfiles ⟨0, by omega⟩)
            (canonicalCStar ⟨0, by omega⟩) m k) ≤
      sourceExceptionalRateWithPrefactor m
        (unprimedBadCoeff + primedBadCoeff + 6) kappa := by
  calc
    simpleRandomWalkLaw
        (prefixPairingEvent m ⟨0, by omega⟩ (k + 1) ∩
          stoppedThetaEvent (canonicalProfiles ⟨0, by omega⟩)
            (canonicalCStar ⟨0, by omega⟩) m k) ≤
      simpleRandomWalkLaw
        (xEastUnprimedSourceEvent m k ∪ xEastPrimedSourceEvent m k) :=
      measure_mono (prefixStoppedThetaEvent_xEast_subset m k)
    simpleRandomWalkLaw
        (xEastUnprimedSourceEvent m k ∪ xEastPrimedSourceEvent m k) ≤
      simpleRandomWalkLaw (xEastUnprimedSourceEvent m k) +
        simpleRandomWalkLaw (xEastPrimedSourceEvent m k) := measure_union_le _ _
    _ ≤ sourceExceptionalRateWithPrefactor m (unprimedBadCoeff + 3) kappa +
        sourceExceptionalRateWithPrefactor m (primedBadCoeff + 3) kappa :=
      add_le_add (h.unprimed.theta_measure_le hm hk hs horizon_card
          habsorb hunprimedLabels)
        (h.primed.theta_measure_le hm hk hs horizon_card habsorb
          hprimedLabels)
    _ = sourceExceptionalRateWithPrefactor m
        (unprimedBadCoeff + primedBadCoeff + 6) kappa := by
      simp only [sourceExceptionalRateWithPrefactor]
      push_cast
      ring

/-- Stronger pairing-independent form of the preceding estimate.  It keeps
only the common threshold-time history, so it applies verbatim to the two
column tilings while retaining the temporal deletion profile. -/
theorem XEastSeparateFixedDepthInputs.threshold_theta_measure_le
    {m k unprimedBadCoeff primedBadCoeff : ℕ}
    (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hs : SourceIntervalScale m (sourceBandLowerNat m) ∧
      SourceUpperScale m m)
    (horizon_card :
      (HLOZExternalUpper.externalLabelCount (prop44Psi m) : ℝ) ≤
        Real.exp (16 * Real.sqrt (m : ℝ)))
    (habsorb : sourceProp45OneSideError m ≤
      sourceExceptionalRateWithPrefactor m 3 kappa)
    (hunprimedLabels : simpleRandomWalkLaw
        (xEastUnprimedBadLabelUnion m
          (HLOZExternalUpper.externalLabelCount (prop44Psi m))) ≤
      sourceExceptionalRateWithPrefactor m 1 kappa)
    (hprimedLabels : simpleRandomWalkLaw
        (xEastPrimedBadLabelUnion m
          (HLOZExternalUpper.externalLabelCount (prop44Psi m))) ≤
      sourceExceptionalRateWithPrefactor m 1 kappa)
    (h : XEastSeparateFixedDepthInputs m k
      unprimedBadCoeff primedBadCoeff) :
    simpleRandomWalkLaw
        (hlozThresholdTimeEventK m (k + 1) ∩
          stoppedThetaEvent (canonicalProfiles ⟨0, by omega⟩)
            (canonicalCStar ⟨0, by omega⟩) m k) ≤
      sourceExceptionalRateWithPrefactor m
        (unprimedBadCoeff + primedBadCoeff + 6) kappa := by
  rw [thresholdStoppedThetaEvent_xEast_eq]
  calc
    simpleRandomWalkLaw
        (xEastUnprimedSourceEvent m k ∪ xEastPrimedSourceEvent m k) ≤
      simpleRandomWalkLaw (xEastUnprimedSourceEvent m k) +
        simpleRandomWalkLaw (xEastPrimedSourceEvent m k) := measure_union_le _ _
    _ ≤ sourceExceptionalRateWithPrefactor m (unprimedBadCoeff + 3) kappa +
        sourceExceptionalRateWithPrefactor m (primedBadCoeff + 3) kappa :=
      add_le_add (h.unprimed.theta_measure_le hm hk hs horizon_card
          habsorb hunprimedLabels)
        (h.primed.theta_measure_le hm hk hs horizon_card habsorb
          hprimedLabels)
    _ = sourceExceptionalRateWithPrefactor m
        (unprimedBadCoeff + primedBadCoeff + 6) kappa := by
      simp only [sourceExceptionalRateWithPrefactor]
      push_cast
      ring

def HasXEastSeparateFiniteAtomizations
    (unprimedBadCoeff primedBadCoeff : ℕ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
    Nonempty (XEastSeparateFixedDepthInputs m (stageNumber r)
      unprimedBadCoeff primedBadCoeff)

/-- No additional input is needed on a canonical unprimed good atom.  The
upper event uses `intervalHighCut - 1`, so every requested holding block is
complete even when the stopping time ends inside the active odd block. -/
def XEastUnprimedCanonicalGoodAtomClockInputs
    (m k : ℕ)
    (v : FixedExternalLabels
      (HLOZExternalUpper.externalLabelCount (prop44Psi m))) : Prop := True

theorem XEastUnprimedCanonicalGoodAtomClockInputs.toGoodAtomClockInputs
    {m k : ℕ}
    {v : FixedExternalLabels
      (HLOZExternalUpper.externalLabelCount (prop44Psi m))}
    (_h : XEastUnprimedCanonicalGoodAtomClockInputs m k v)
    (hm : 2 ≤ m) (hk : 1 ≤ k) :
    XEastUnprimedGoodAtomClockInputs m k
      (HLOZExternalUpper.externalLabelCount (prop44Psi m)) v
        (xEastCanonicalHorizonEvent m k) where
  theta_subset := xEastUnprimedCanonical_theta_subset m k v hm hk
  minus_compatible := by
    intro s x hs hxsite hxTheta
    have hxEven := xEastUnprimedFixedSites_even v x hxsite
    have hext := paperExternalLocalTime_canonicalHorizon_le_fixedProfile
      m k v hm hk hs.1.1 hs.1.2 hs.2 x
        hxEven hxTheta.2
    refine ⟨hext, ?_⟩
    by_cases hEven : Even (favoriteCreationHorizon m k s)
    · have heq := paperLazyLocalTime_canonicalHorizon_eq_inversePrefix_of_even
        m k v hm hk hs.1.1 hs.1.2 hs.2 x hxEven hxTheta.2 hEven
      rw [heq]
      apply inverseClockHoldingPrefix_mono_cut
      rw [intervalDotIndex]
      apply le_min
      · have hprofile := inverseClockProfile_eq_xEastEncodedProfile_of_mem_fixedAtom
          v hs.1.1 x hxEven (externalLabelCount_prop44Psi_pos m)
        rwa [← hprofile]
      · exact hxTheta.1.1
    · by_cases hprevious :
          s (favoriteCreationHorizon m k s - 1) = x
      · have hlazy :=
          paperLazyLocalTime_canonicalHorizon_le_inversePrefix_of_odd
            m k v hm hk hs.1.1 hs.1.2 hs.2 x hxEven hEven
        calc
          paperLazyLocalTime s (favoriteCreationHorizon m k s) x ≤
              inverseClockHoldingPrefix s
                (2 * HLOZExternalUpper.externalLabelCount (prop44Psi m) - 1)
                (paperExternalLocalTime s
                  (favoriteCreationHorizon m k s) x) x := hlazy
          _ ≤ inverseClockHoldingPrefix s
                (2 * HLOZExternalUpper.externalLabelCount (prop44Psi m) - 1)
                (intervalDotIndex m (sourceBandLowerNat m)
                  (xEastEncodedProfile (fixedIncrementLabels v)) x) x := by
            apply inverseClockHoldingPrefix_mono_cut
            rw [intervalDotIndex]
            apply le_min
            · have hprofile :=
                inverseClockProfile_eq_xEastEncodedProfile_of_mem_fixedAtom
                  v hs.1.1 x hxEven (externalLabelCount_prop44Psi_pos m)
              exact hext.trans_eq hprofile
            · exact hxTheta.1.1
      · have heq :=
          paperLazyLocalTime_canonicalHorizon_eq_inversePrefix_of_odd_of_previous_ne
            m k v hm hk hs.1.1 hs.1.2 hs.2 x hxEven hEven hprevious
        rw [heq]
        apply inverseClockHoldingPrefix_mono_cut
        rw [intervalDotIndex]
        apply le_min
        · have hprofile := inverseClockProfile_eq_xEastEncodedProfile_of_mem_fixedAtom
            v hs.1.1 x hxEven (externalLabelCount_prop44Psi_pos m)
          rwa [← hprofile]
        · exact hxTheta.1.1
  plus_compatible := by
    intro s x hs hxsite hxTheta
    have hxEven := xEastUnprimedFixedSites_even v x hxsite
    have hext := paperExternalLocalTime_canonicalHorizon_le_fixedProfile
      m k v hm hk hs.1.1 hs.1.2 hs.2 x
        hxEven hxTheta.2
    refine ⟨hext, ?_⟩
    by_cases hEven : Even (favoriteCreationHorizon m k s)
    · have heq := paperLazyLocalTime_canonicalHorizon_eq_inversePrefix_of_even
        m k v hm hk hs.1.1 hs.1.2 hs.2 x hxEven hxTheta.2 hEven
      rw [heq]
      exact inverseClockHoldingPrefix_mono_cut s _ _ _ x
        ((Nat.sub_le (intervalHighCut m m) 1).trans hxTheta.1)
    · by_cases hprevious :
          s (favoriteCreationHorizon m k s - 1) = x
      · have hpriorLt : intervalPriorHighCut m m < intervalHighCut m m := by
          rw [intervalPriorHighCut]
          have htwo := intervalHighCut_two_le m m (by omega) (by omega)
          omega
        exact
          inverseClockHoldingPrefix_canonicalHorizon_le_paperLazy_of_odd_of_lt
            m k v hm hk hs.1.1 hs.1.2 hs.2 x hxEven hEven hprevious
              (hpriorLt.trans_le hxTheta.1)
      · have heq :=
          paperLazyLocalTime_canonicalHorizon_eq_inversePrefix_of_odd_of_previous_ne
            m k v hm hk hs.1.1 hs.1.2 hs.2 x hxEven hEven hprevious
        rw [heq]
        exact inverseClockHoldingPrefix_mono_cut s _ _ _ x
          ((Nat.sub_le (intervalHighCut m m) 1).trans hxTheta.1)

/-- No additional input is needed on a canonical primed good atom; the prior
upper prefix excludes the possibly unfinished active even block. -/
def XEastPrimedCanonicalGoodAtomClockInputs
    (m k : ℕ)
    (z : PrimedFixedExternalLabels
      (HLOZExternalUpper.externalLabelCount (prop44Psi m))) : Prop := True

theorem XEastPrimedCanonicalGoodAtomClockInputs.toGoodAtomClockInputs
    {m k : ℕ}
    {z : PrimedFixedExternalLabels
      (HLOZExternalUpper.externalLabelCount (prop44Psi m))}
    (_h : XEastPrimedCanonicalGoodAtomClockInputs m k z)
    (hm : 2 ≤ m) (hk : 1 ≤ k) :
    XEastPrimedGoodAtomClockInputs m k
      (HLOZExternalUpper.externalLabelCount (prop44Psi m)) z
        (xEastCanonicalHorizonEvent m k) where
  theta_subset := xEastPrimedCanonical_theta_subset m k z hm hk
  minus_compatible := by
    intro s x hs hxsite hxTheta
    have hxOdd := xEastPrimedFixedSites_odd z x hxsite
    have hext := primedExternalLocalTime_canonicalHorizon_le_fixedProfile
      m k z hm hk hs.1.1 hs.1.2 hs.2 x hxOdd
    refine ⟨?_, ?_⟩
    · simpa only [concretePrimed_stoppedExternal,
        concretePrimed_inverseProfile] using hext
    · by_cases hEven : Even (favoriteCreationHorizon m k s)
      · by_cases hprevious :
            s (favoriteCreationHorizon m k s - 1) = x
        · simp only [concretePrimed_stoppedLazy,
            concretePrimed_inverseHoldingPrefix]
          have hlazy :=
            primedLazyLocalTime_canonicalHorizon_le_inversePrefix_of_even
              m k z hm hk hs.1.1 hs.1.2 hs.2 x hxOdd hEven
          calc
            primedLazyLocalTime s (favoriteCreationHorizon m k s) x ≤
                primedInverseClockHoldingPrefix s
                  (2 * HLOZExternalUpper.externalLabelCount (prop44Psi m) - 1)
                  (primedExternalLocalTime s
                    (favoriteCreationHorizon m k s) x) x := hlazy
            _ ≤ primedInverseClockHoldingPrefix s
                  (2 * HLOZExternalUpper.externalLabelCount (prop44Psi m) - 1)
                  (intervalDotIndex m (sourceBandLowerNat m)
                    (xEastPrimedEncodedProfile z.1
                      (fixedIncrementLabels z.2)) x) x := by
              apply primedInverseClockHoldingPrefix_mono_cut
              rw [intervalDotIndex]
              apply le_min
              · have hprofile :=
                  primedInverseClockProfile_eq_xEastEncodedProfile_of_mem_fixedAtom
                    z hs.1.1 x hxOdd (externalLabelCount_prop44Psi_pos m)
                exact hext.trans_eq hprofile
              · simpa only [concretePrimed_stoppedExternal] using hxTheta.1.1
        · simp only [concretePrimed_stoppedLazy,
            concretePrimed_inverseHoldingPrefix]
          have heq :=
            primedLazyLocalTime_canonicalHorizon_eq_inversePrefix_of_even_of_previous_ne
              m k z hm hk hs.1.1 hs.1.2 hs.2 x hxOdd hEven hprevious
          rw [heq]
          apply primedInverseClockHoldingPrefix_mono_cut
          rw [intervalDotIndex]
          apply le_min
          · have hprofile :=
              primedInverseClockProfile_eq_xEastEncodedProfile_of_mem_fixedAtom
                z hs.1.1 x hxOdd (externalLabelCount_prop44Psi_pos m)
            rwa [← hprofile]
          · simpa only [concretePrimed_stoppedExternal] using hxTheta.1.1
      · simp only [concretePrimed_stoppedLazy,
          concretePrimed_inverseHoldingPrefix]
        have heq :=
          primedLazyLocalTime_canonicalHorizon_eq_inversePrefix_of_odd
            m k z hm hk hs.1.1 hs.1.2 hs.2 x hxOdd hxTheta.2 hEven
        rw [heq]
        apply primedInverseClockHoldingPrefix_mono_cut
        rw [intervalDotIndex]
        apply le_min
        · have hprofile :=
            primedInverseClockProfile_eq_xEastEncodedProfile_of_mem_fixedAtom
              z hs.1.1 x hxOdd (externalLabelCount_prop44Psi_pos m)
          rwa [← hprofile]
        · simpa only [concretePrimed_stoppedExternal] using hxTheta.1.1
  plus_compatible := by
    intro s x hs hxsite hxTheta
    have hxOdd := xEastPrimedFixedSites_odd z x hxsite
    have hext := primedExternalLocalTime_canonicalHorizon_le_fixedProfile
      m k z hm hk hs.1.1 hs.1.2 hs.2 x hxOdd
    refine ⟨?_, ?_⟩
    · simpa only [concretePrimed_stoppedExternal,
        concretePrimed_inverseProfile] using hext
    · by_cases hEven : Even (favoriteCreationHorizon m k s)
      · by_cases hprevious :
            s (favoriteCreationHorizon m k s - 1) = x
        · simp only [concretePrimed_stoppedLazy,
              concretePrimed_inverseHoldingPrefix]
          have hcutLe : intervalHighCut m m ≤
              primedExternalLocalTime s (favoriteCreationHorizon m k s) x := by
            simpa only [concretePrimed_stoppedExternal] using hxTheta.1
          have hpriorLt : intervalPriorHighCut m m < intervalHighCut m m := by
            rw [intervalPriorHighCut]
            have htwo := intervalHighCut_two_le m m (by omega) (by omega)
            omega
          exact
            primedInverseClockHoldingPrefix_canonicalHorizon_le_lazy_of_even_of_lt
              m k z hm hk hs.1.1 hs.1.2 hs.2 x hxOdd hEven hprevious
                (hpriorLt.trans_le hcutLe)
        · simp only [concretePrimed_stoppedLazy,
            concretePrimed_inverseHoldingPrefix]
          have heq :=
            primedLazyLocalTime_canonicalHorizon_eq_inversePrefix_of_even_of_previous_ne
              m k z hm hk hs.1.1 hs.1.2 hs.2 x hxOdd hEven hprevious
          rw [heq]
          apply primedInverseClockHoldingPrefix_mono_cut
          exact (Nat.sub_le (intervalHighCut m m) 1).trans (by
            simpa only [concretePrimed_stoppedExternal] using hxTheta.1)
      · simp only [concretePrimed_stoppedLazy,
          concretePrimed_inverseHoldingPrefix]
        have heq :=
          primedLazyLocalTime_canonicalHorizon_eq_inversePrefix_of_odd
            m k z hm hk hs.1.1 hs.1.2 hs.2 x hxOdd hxTheta.2 hEven
        rw [heq]
        apply primedInverseClockHoldingPrefix_mono_cut
        exact (Nat.sub_le (intervalHighCut m m) 1).trans (by
          simpa only [concretePrimed_stoppedExternal] using hxTheta.1)

/-- The former residual compatibility package is retained as an API boundary,
but its atom fields are now propositionally trivial: the prior upper prefix
proves the incomplete-terminal cases internally. -/
structure XEastCanonicalStoppedCompatibilityInputs (m k : ℕ) where
  unprimed : ∀ v ∈ xEastUnprimedGoodFixedAtoms m
      (HLOZExternalUpper.externalLabelCount (prop44Psi m)),
    XEastUnprimedCanonicalGoodAtomClockInputs m k v
  primed : ∀ z ∈ xEastPrimedGoodFixedAtoms m
      (HLOZExternalUpper.externalLabelCount (prop44Psi m)),
    XEastPrimedCanonicalGoodAtomClockInputs m k z

def HasXEastCanonicalStoppedCompatibility : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
    Nonempty (XEastCanonicalStoppedCompatibilityInputs m (stageNumber r))

/-- The canonical stopped-clock compatibility package has no remaining
source premise. -/
theorem canonical_hasXEastCanonicalStoppedCompatibility :
    HasXEastCanonicalStoppedCompatibility := by
  apply Filter.Eventually.of_forall
  intro m r
  exact ⟨{
    unprimed := fun _ _ ↦ True.intro
    primed := fun _ _ ↦ True.intro
  }⟩

/-- With Appendix A available, the canonical near-critical horizon and
Proposition 4.4 each cost one exceptional-rate copy. -/
theorem hasXEastSeparateFiniteAtomizations_of_canonicalCompatibility
    (hdisk : HLOZProp13FromAppendix.AppendixDiskEstimate)
    (hcompat : HasXEastCanonicalStoppedCompatibility) :
    HasXEastSeparateFiniteAtomizations 2 2 := by
  filter_upwards [hcompat,
    eventually_xEastCanonicalHorizon_compl_measure_le hdisk,
    eventually_ge_atTop (2 : ℕ)]
    with m hcompat hHorizon hm
  intro r
  rcases hcompat r with ⟨hcompat⟩
  refine ⟨{
    unprimed := {
      positiveDepth := externalLabelCount_prop44Psi_pos m
      horizon := xEastCanonicalHorizonEvent m (stageNumber r)
      clockInputs := fun v hv ↦
        (hcompat.unprimed v hv).toGoodAtomClockInputs hm (by
          simp [stageNumber])
      horizonBadCoeff := 1
      badCoeff_eq := rfl
      horizon_bad_bound := hHorizon (stageNumber r) }
    primed := {
      positiveDepth := externalLabelCount_prop44Psi_pos m
      horizon := xEastCanonicalHorizonEvent m (stageNumber r)
      clockInputs := fun z hz ↦
        (hcompat.primed z hz).toGoodAtomClockInputs hm (by
          simp [stageNumber])
      horizonBadCoeff := 1
      badCoeff_eq := rfl
      horizon_bad_bound := hHorizon (stageNumber r) }
  }⟩

/-- Appendix A suffices for the canonical X-east atomizations; all
stopped-clock compatibility is derived internally. -/
theorem hasXEastSeparateFiniteAtomizations_canonical
    (hdisk : HLOZProp13FromAppendix.AppendixDiskEstimate) :
    HasXEastSeparateFiniteAtomizations 2 2 :=
  hasXEastSeparateFiniteAtomizations_of_canonicalCompatibility hdisk
    canonical_hasXEastCanonicalStoppedCompatibility

/-- The separate atomizations estimate the source-correct stopped `X₁`
event intersected with its pairing history. -/
theorem xEast_stoppedThetaEstimate_of_separateAtomizations
    {unprimedBadCoeff primedBadCoeff : ℕ}
    (hatoms : HasXEastSeparateFiniteAtomizations
      unprimedBadCoeff primedBadCoeff) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
      simpleRandomWalkLaw
          (prefixPairingEvent m ⟨0, by omega⟩ (stageNumber r + 1) ∩
            stoppedThetaEvent (canonicalProfiles ⟨0, by omega⟩)
              (canonicalCStar ⟨0, by omega⟩) m (stageNumber r)) ≤
        sourceExceptionalRateWithPrefactor m
          (unprimedBadCoeff + primedBadCoeff + 6) kappa := by
  filter_upwards [hatoms, eventually_sourceEndpointScales,
    eventually_sourceProp45OneSideError_le,
    HLOZProp44ExternalChain.eventually_externalLabelCount_prop44Psi_le_exp_sixteen_sqrt,
    eventually_xEastUnprimedBadLabelUnion_measure_le_exceptional,
    eventually_xEastPrimedBadLabelUnion_measure_le_exceptional,
    eventually_ge_atTop (2 : ℕ)]
    with m hatoms hs habsorb horizon_card hunprimedLabels hprimedLabels
      hm
  intro r
  rcases hatoms r with ⟨hatom⟩
  exact hatom.theta_measure_le hm (by simp [stageNumber]) hs horizon_card
    habsorb hunprimedLabels hprimedLabels

/-- Eventual estimate on the common temporal threshold event.  This is the
form used for `Y` and `Y'`: their domino relations change the `PairFree`
history, not the time-parity deletion profile. -/
theorem temporalThreshold_stoppedThetaEstimate_of_separateAtomizations
    {unprimedBadCoeff primedBadCoeff : ℕ}
    (hatoms : HasXEastSeparateFiniteAtomizations
      unprimedBadCoeff primedBadCoeff) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex,
      simpleRandomWalkLaw
          (hlozThresholdTimeEventK m (stageNumber r + 1) ∩
            stoppedThetaEvent (canonicalProfiles ⟨0, by omega⟩)
              (canonicalCStar ⟨0, by omega⟩) m (stageNumber r)) ≤
        sourceExceptionalRateWithPrefactor m
          (unprimedBadCoeff + primedBadCoeff + 6) kappa := by
  filter_upwards [hatoms, eventually_sourceEndpointScales,
    eventually_sourceProp45OneSideError_le,
    HLOZProp44ExternalChain.eventually_externalLabelCount_prop44Psi_le_exp_sixteen_sqrt,
    eventually_xEastUnprimedBadLabelUnion_measure_le_exceptional,
    eventually_xEastPrimedBadLabelUnion_measure_le_exceptional,
    eventually_ge_atTop (2 : ℕ)]
    with m hatoms hs habsorb horizon_card hunprimedLabels hprimedLabels hm
  intro r
  rcases hatoms r with ⟨hatom⟩
  exact hatom.threshold_theta_measure_le hm (by simp [stageNumber]) hs
    horizon_card habsorb hunprimedLabels hprimedLabels

/-- The exact low-distance Proposition-4.5 estimate for the `X₁` tiling,
assembled from the two independent finite atomizations. -/
theorem xEast_prop45Estimate_of_separateAtomizations
    {unprimedBadCoeff primedBadCoeff : ℕ}
    (hatoms : HasXEastSeparateFiniteAtomizations
      unprimedBadCoeff primedBadCoeff) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo →
      simpleRandomWalkLaw
          (prop45FailureEvent canonicalProfiles canonicalCStar m
            ⟨0, by omega⟩ r (alphaValue a)) ≤
        sourceExceptionalRateWithPrefactor m
          (unprimedBadCoeff + primedBadCoeff + 6) kappa := by
  filter_upwards [xEast_stoppedThetaEstimate_of_separateAtomizations hatoms]
    with m htheta
  intro r a _ha
  exact (measure_mono (by
    intro s hsFailure
    exact ⟨hsFailure.1.1.1, hsFailure.2⟩)).trans (htheta r)

/-- Direct source-facing X-east Proposition-4.5 estimate: Appendix A
supplies the canonical horizon and Proposition 4.4 is already internal, so
the only separate hypothesis is the exact stopped-clock compatibility
package. -/
theorem xEast_prop45Estimate_of_canonicalCompatibility
    (hdisk : HLOZProp13FromAppendix.AppendixDiskEstimate)
    (hcompat : HasXEastCanonicalStoppedCompatibility) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo →
      simpleRandomWalkLaw
          (prop45FailureEvent canonicalProfiles canonicalCStar m
            ⟨0, by omega⟩ r (alphaValue a)) ≤
        sourceExceptionalRateWithPrefactor m 10 kappa := by
  simpa using xEast_prop45Estimate_of_separateAtomizations
    (hasXEastSeparateFiniteAtomizations_of_canonicalCompatibility
      hdisk hcompat)

/-- Fully internal canonical X-east Proposition-4.5 estimate. -/
theorem xEast_prop45Estimate_canonical
    (hdisk : HLOZProp13FromAppendix.AppendixDiskEstimate) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo →
      simpleRandomWalkLaw
          (prop45FailureEvent canonicalProfiles canonicalCStar m
            ⟨0, by omega⟩ r (alphaValue a)) ≤
        sourceExceptionalRateWithPrefactor m 10 kappa :=
  xEast_prop45Estimate_of_canonicalCompatibility hdisk
    canonical_hasXEastCanonicalStoppedCompatibility

end Erdos1166.HLOZProp47Prop45XEastPrimed
