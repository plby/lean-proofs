/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1166.Erdos1166HLOZProp42InverseLaw
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47Prop45Connector

/-!
# The source-faithful `X₁` external-path atoms in Proposition 4.5

The four branches in HLOZ Proposition 4.5 are conditioned separately.  In
particular, an atom fixing the unprimed deleted path must not also be treated
as an atom for the one-step-shifted primed deletion: that extra conditioning
would destroy the direct Proposition-4.2 product-law argument.

This file therefore closes the *unprimed* `X₁` atom calculation.  On a
fixed finite external-label path, Proposition 4.2 is already formalized by
`inverseClockHoldingPrefix_hasLaw_fixedExternalPath`; the inverse-clock
profile and prefix identities are derived rather than assumed below.  The
only remaining per-atom inputs are stopped-clock inclusions and the
Proposition-4.4 cardinality bounds.  The primed
`X₁`, the rotated `Xₗ`, and the two column encodings `Y,Y'` are explicitly
kept as distinct obligations at the end of the file.
-/

namespace Erdos1166.HLOZProp47Prop45XEast

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

open HLOZFoundation HLOZDecomposition HLOZUrn
open HLOZProp47Parameters HLOZProp47SourceObjects
open HLOZProp45SourceClock HLOZProp45SourceInterval
open HLOZProp45SourceMirrors HLOZProp45SourceEndpoints
open HLOZProp45SourceAbsorption HLOZProp47Canonical
open HLOZSourceInstantiation HLOZProp42InverseLaw
open HLOZProp47Prop45Connector
open HLOZProp47SourceAssembly
open HLOZPairing.ScreeningBridge

abbrev Path := ℕ → Site

/-- The external profile encoded by a fixed list of non-lazy terminal pair
labels.  Its value at `x` is exactly the number of completed external visits
to `x` in the encoded prefix. -/
noncomputable def xEastEncodedProfile {q : ℕ}
    (labels : Fin q → IncrementPair) (x : Site) : ℕ :=
  (chronologicalExternalIndexList labels x).length

/-- A longer initial segment of a list of natural holding times has at least
the mass of a shorter one. -/
theorem sum_take_mono_nat (l : List ℕ) {a b : ℕ} (hab : a ≤ b) :
    (l.take a).sum ≤ (l.take b).sum := by
  induction l generalizing a b with
  | nil => simp
  | cons y ys ih =>
      cases a with
      | zero => simp
      | succ a =>
          cases b with
          | zero => omega
          | succ b =>
              simp only [List.take_succ_cons, List.sum_cons]
              exact Nat.add_le_add_left (ih (Nat.le_of_succ_le_succ hab)) y

theorem inverseClockHoldingPrefix_mono_cut
    (s : Path) (q xCut yCut : ℕ) (x : Site) (hxy : xCut ≤ yCut) :
    inverseClockHoldingPrefix s q xCut x ≤
      inverseClockHoldingPrefix s q yCut x := by
  unfold inverseClockHoldingPrefix
  simpa only [List.map_take] using
    sum_take_mono_nat ((externalVisitIndexList s q x).map
      (paperHoldingNat s)) hxy

/-- The two unprimed branches of the paper's `X₁` stopped event. -/
noncomputable def xEastUnprimedThetaEvent (m k : ℕ) : Set Path :=
  {s | (stoppedThetaHalfSites paperUnprimedProfile
        HLOZPairing.chessEven false 10 s m k ∪
      stoppedThetaHalfSites paperUnprimedProfile
        HLOZPairing.chessEven true 10 s m k).Nonempty}

/-- A pairing-independent enlargement of the unprimed source event.

The HLOZ proof uses the temporal deletion from (2.12) for every one of the
six domino tilings.  The tiling only changes the `PairFree` conjunct of
`prefixPairingEvent`; the threshold-time conjunct is common.  We therefore
prove the stopped-clock estimate on this larger threshold event.  Every
pairing-specific source event is a subset of it. -/
noncomputable def xEastUnprimedSourceEvent (m k : ℕ) : Set Path :=
  hlozThresholdTimeEventK m (k + 1) ∩
    xEastUnprimedThetaEvent m k

/-- The source-faithful lower branch retains the strict upper local-time
bound from `stoppedThetaHalfSites`.  The older auxiliary minus event records
only the lower and external inequalities; this capped version is what rules
out the level-`m` creation endpoint. -/
def intervalStoppedThetaMinusCappedAt
    (m a k : ℕ) (x : Site) : Set Path :=
  intervalStoppedThetaMinusAt m a k x ∩
    {s | localTime s (favoriteCreationHorizon m k s) x < m}

def intervalStoppedThetaMinusCappedEvent
    (sites : Finset Site) (m a k : ℕ) : Set Path :=
  ⋃ x ∈ sites, intervalStoppedThetaMinusCappedAt m a k x

/-- The exact fixed-external-path input for the unprimed `X₁` branches.

The inverse-clock profile and holding-prefix identifications are now supplied
by `HLOZInverseClockProfile`; they are therefore not fields of this source
input.  The atom only records the genuinely source-specific stopped-event
inclusions and Proposition-4.4 cardinality bounds. -/
structure XEastUnprimedExternalAtomInputs
    (m k q : ℕ) (labels : Fin q → IncrementPair) (H : Set Path) where
  nondistinguished : ∀ i, labels i ≠ distinguishedIncrementPair
  positiveLength : 0 < q
  sites : Finset Site
  sitesEven : ∀ x ∈ sites, HLOZPairing.chessEven x
  minus_capacity : ∀ x ∈ sites,
    intervalDotIndex m (sourceBandLowerNat m)
      (xEastEncodedProfile labels) x ≤
        (chronologicalExternalIndexList labels x).length
  plus_capacity : ∀ x ∈ intervalPlusCandidates sites m m
      (xEastEncodedProfile labels),
    intervalHighCut m m ≤
      (chronologicalExternalIndexList labels x).length
  theta_subset :
    externalPathWalkAtom (List.ofFn labels) ∩ H ∩
        xEastUnprimedSourceEvent m k ⊆
      externalPathWalkAtom (List.ofFn labels) ∩ H ∩
        xEastUnprimedSourceEvent m k ∩
          (intervalStoppedThetaMinusCappedEvent sites m
              (sourceBandLowerNat m) k ∪
            intervalStoppedThetaPlusEvent sites m m k)
  minus_compatible : ∀ {s x},
    s ∈ externalPathWalkAtom (List.ofFn labels) ∩ H ∩
        xEastUnprimedSourceEvent m k →
    x ∈ sites → s ∈ intervalStoppedThetaMinusCappedAt m
        (sourceBandLowerNat m) k x →
      SourceClockPrefixCompatibleAt s (favoriteCreationHorizon m k s)
        (2 * q - 1)
          (intervalDotIndex m (sourceBandLowerNat m)
            (xEastEncodedProfile labels) x) x
  plus_compatible : ∀ {s x},
    s ∈ externalPathWalkAtom (List.ofFn labels) ∩ H ∩
        xEastUnprimedSourceEvent m k →
    x ∈ sites → s ∈ intervalStoppedThetaPlusAt m m k x →
      SourceClockInitialPrefixCompatibleAt s
        (favoriteCreationHorizon m k s) (2 * q - 1)
          (intervalPriorHighCut m m) x
  prop44_card :
    ((sourceProp44Candidates sites m
      (xEastEncodedProfile labels)).card : ℝ) ≤
        Real.exp (16 * sourceRate m)
  horizon_card : (sites.card : ℝ) ≤
    Real.exp (16 * Real.sqrt (m : ℝ))

theorem XEastUnprimedExternalAtomInputs.profile_atom
    {m k q : ℕ} {labels : Fin q → IncrementPair} {H : Set Path}
    (h : XEastUnprimedExternalAtomInputs m k q labels H) :
    externalPathWalkAtom (List.ofFn labels) ⊆
      inverseClockProfileAtom (2 * q - 1) h.sites
        (xEastEncodedProfile labels) := by
  rintro s ⟨ω, hω, rfl⟩ x hx
  obtain ⟨N, hlabels⟩ := realized_terminalPairLabelsThrough
    labels h.nondistinguished hω
  exact inverseClockProfile_eq_chronological_length labels hlabels x
    (h.sitesEven x hx) h.positiveLength

theorem XEastUnprimedExternalAtomInputs.holdingPrefix_hasLaw
    {m k q : ℕ} {labels : Fin q → IncrementPair} {H : Set Path}
    (h : XEastUnprimedExternalAtomInputs m k q labels H)
    (x : Site) (cut : ℕ)
    (hx : HLOZPairing.chessEven x)
    (hcut : cut ≤ (chronologicalExternalIndexList labels x).length) :
    HasLaw (fun s ↦ inverseClockHoldingPrefix s (2 * q - 1) cut x)
      (negBinMeasure cut)
      simpleRandomWalkLaw[|externalPathWalkAtom (List.ofFn labels)] := by
  exact inverseClockHoldingPrefix_hasLaw_fixedExternalPath labels
    h.nondistinguished x hx h.positiveLength hcut

private theorem XEastUnprimedExternalAtomInputs.minus_law
    {m k q : ℕ} {labels : Fin q → IncrementPair} {H : Set Path}
    (h : XEastUnprimedExternalAtomInputs m k q labels H)
    (x : Site) (hx : x ∈ h.sites) :
    HasLaw (fun s ↦ inverseClockHoldingPrefix s (2 * q - 1)
      (intervalDotIndex m (sourceBandLowerNat m)
        (xEastEncodedProfile labels) x) x)
      (negBinMeasure (intervalDotIndex m (sourceBandLowerNat m)
        (xEastEncodedProfile labels) x))
      simpleRandomWalkLaw[|externalPathWalkAtom (List.ofFn labels)] := by
  apply h.holdingPrefix_hasLaw x _ (h.sitesEven x hx)
  exact h.minus_capacity x hx

private theorem XEastUnprimedExternalAtomInputs.plus_law
    {m k q : ℕ} {labels : Fin q → IncrementPair} {H : Set Path}
    (h : XEastUnprimedExternalAtomInputs m k q labels H)
    (x : Site)
    (hx : x ∈ intervalPlusCandidates h.sites m m
      (xEastEncodedProfile labels)) :
    HasLaw (fun s ↦ inverseClockHoldingPrefix s (2 * q - 1)
      (intervalPriorHighCut m m) x)
      (negBinMeasure (intervalPriorHighCut m m))
      simpleRandomWalkLaw[|externalPathWalkAtom (List.ofFn labels)] := by
  apply h.holdingPrefix_hasLaw x _
  · exact h.sitesEven x (Finset.mem_filter.mp hx).1
  exact (Nat.sub_le (intervalHighCut m m) 1).trans (h.plus_capacity x hx)

/-- The exact one-side error: two copies of the `m^(8/25)` error and one
copy of the square-root error. -/
noncomputable def sourceProp45OneSideError (m : ℕ) : ℝ≥0∞ :=
  (ENNReal.ofReal (Real.exp (-sourceRate m)) +
    ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ)))) +
      ENNReal.ofReal (Real.exp (-sourceRate m))

/-- On one fixed unprimed external-path atom, the complete `X₁` one-side
estimate is unconditional on any further probabilistic premise. -/
theorem XEastUnprimedExternalAtomInputs.conditional_theta_le
    {m k q : ℕ} {labels : Fin q → IncrementPair} {H : Set Path}
    (hs : SourceIntervalScale m (sourceBandLowerNat m) ∧
      SourceUpperScale m m)
    (h : XEastUnprimedExternalAtomInputs m k q labels H) :
    simpleRandomWalkLaw[|externalPathWalkAtom (List.ofFn labels)]
        (externalPathWalkAtom (List.ofFn labels) ∩ H ∩
          xEastUnprimedSourceEvent m k) ≤
      sourceProp45OneSideError m := by
  let C := externalPathWalkAtom (List.ofFn labels)
  let minusEvent := intervalStoppedThetaMinusCappedEvent h.sites m
    (sourceBandLowerNat m) k
  let plusEvent := intervalStoppedThetaPlusEvent h.sites m m k
  have hminusSubset : (C ∩ H ∩ xEastUnprimedSourceEvent m k) ∩
      minusEvent ⊆
      intervalCanonicalDotThetaEvent (2 * q - 1) h.sites m
        (sourceBandLowerNat m) (xEastEncodedProfile labels) := by
    intro s hs'
    have hsTheta := hs'.2
    simp only [minusEvent, intervalStoppedThetaMinusCappedEvent,
      Set.mem_iUnion] at hsTheta
    rcases hsTheta with ⟨x, hxsite, hxTheta⟩
    rw [intervalCanonicalDotThetaEvent, intervalDotThetaEvent]
    simp only [Set.mem_iUnion]
    refine ⟨x, hxsite, ?_⟩
    change sourceBandLowerNat m ≤
      intervalDotIndex m (sourceBandLowerNat m)
          (xEastEncodedProfile labels) x +
        inverseClockHoldingPrefix s (2 * q - 1)
          (intervalDotIndex m (sourceBandLowerNat m)
            (xEastEncodedProfile labels) x) x
    have hprofile : inverseClockProfile s (2 * q - 1) x =
        xEastEncodedProfile labels x :=
      h.profile_atom hs'.1.1.1 x hxsite
    have hcompat := h.minus_compatible hs'.1 hxsite hxTheta
    have hext : paperExternalLocalTime s
        (favoriteCreationHorizon m k s) x ≤
      intervalDotIndex m (sourceBandLowerNat m)
        (xEastEncodedProfile labels) x := by
      rw [intervalDotIndex]
      apply le_min
      · simpa only [hprofile] using hcompat.1
      · exact hxTheta.1.1
    have hdecomp := localTime_eq_paperExternal_add_paperLazy
      s (favoriteCreationHorizon m k s) x
    calc
      sourceBandLowerNat m ≤
          localTime s (favoriteCreationHorizon m k s) x := hxTheta.1.2
      _ = paperExternalLocalTime s (favoriteCreationHorizon m k s) x +
          paperLazyLocalTime s (favoriteCreationHorizon m k s) x := hdecomp
      _ ≤ intervalDotIndex m (sourceBandLowerNat m)
            (xEastEncodedProfile labels) x +
          inverseClockHoldingPrefix s (2 * q - 1)
            (intervalDotIndex m (sourceBandLowerNat m)
              (xEastEncodedProfile labels) x) x :=
        Nat.add_le_add hext hcompat.2
  have hplusSubset : (C ∩ H ∩ xEastUnprimedSourceEvent m k) ∩
      plusEvent ⊆
      intervalCanonicalPriorDotThetaPlusEvent (2 * q - 1) h.sites m m
        (xEastEncodedProfile labels) := by
    intro s hs'
    have hsTheta := hs'.2
    simp only [plusEvent, intervalStoppedThetaPlusEvent,
      Set.mem_iUnion] at hsTheta
    rcases hsTheta with ⟨x, hxsite, hxTheta⟩
    rw [intervalCanonicalPriorDotThetaPlusEvent]
    simp only [Set.mem_iUnion]
    have hprofile : inverseClockProfile s (2 * q - 1) x =
        xEastEncodedProfile labels x :=
      h.profile_atom hs'.1.1.1 x hxsite
    have hcompat := h.plus_compatible hs'.1 hxsite hxTheta
    have hcandidate : x ∈ intervalPlusCandidates h.sites m m
        (xEastEncodedProfile labels) := by
      rw [intervalPlusCandidates, Finset.mem_filter]
      exact ⟨hxsite, hxTheta.1.trans (by simpa only [hprofile] using hcompat.1)⟩
    refine ⟨x, hcandidate, ?_⟩
    change intervalHighCut m m +
      inverseClockHoldingPrefix s (2 * q - 1)
        (intervalPriorHighCut m m) x < m
    have hdecomp := localTime_eq_paperExternal_add_paperLazy
      s (favoriteCreationHorizon m k s) x
    calc
      intervalHighCut m m +
          inverseClockHoldingPrefix s (2 * q - 1)
            (intervalPriorHighCut m m) x ≤
        paperExternalLocalTime s (favoriteCreationHorizon m k s) x +
          paperLazyLocalTime s (favoriteCreationHorizon m k s) x :=
        Nat.add_le_add hxTheta.1 hcompat.2
      _ = localTime s (favoriteCreationHorizon m k s) x := hdecomp.symm
      _ < m := hxTheta.2
  have hminus : simpleRandomWalkLaw[|C]
      ((C ∩ H ∩ xEastUnprimedSourceEvent m k) ∩ minusEvent) ≤
      ENNReal.ofReal (Real.exp (-sourceRate m)) +
        ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ))) := by
    exact (measure_mono hminusSubset).trans
      (cond_intervalDotTheta_le_two_scale m (sourceBandLowerNat m) hs.1
        simpleRandomWalkLaw C h.sites (xEastEncodedProfile labels)
        (fun s x ↦ inverseClockHoldingPrefix s (2 * q - 1)
          (intervalDotIndex m (sourceBandLowerNat m)
            (xEastEncodedProfile labels) x) x)
        h.prop44_card h.horizon_card h.minus_law)
  have hplus : simpleRandomWalkLaw[|C]
      ((C ∩ H ∩ xEastUnprimedSourceEvent m k) ∩ plusEvent) ≤
      ENNReal.ofReal (Real.exp (-sourceRate m)) := by
    exact (measure_mono hplusSubset).trans
      (cond_intervalPriorDotThetaPlus_le_exp m m hs.2 simpleRandomWalkLaw C
        h.sites (xEastEncodedProfile labels)
        (fun s x ↦ inverseClockHoldingPrefix s (2 * q - 1)
          (intervalPriorHighCut m m) x) h.prop44_card h.plus_law)
  calc
    simpleRandomWalkLaw[|C] (C ∩ H ∩ xEastUnprimedSourceEvent m k) ≤
        simpleRandomWalkLaw[|C]
          ((C ∩ H ∩ xEastUnprimedSourceEvent m k) ∩
            (minusEvent ∪ plusEvent)) :=
      measure_mono h.theta_subset
    _ ≤ simpleRandomWalkLaw[|C]
          ((C ∩ H ∩ xEastUnprimedSourceEvent m k) ∩ minusEvent) +
        simpleRandomWalkLaw[|C]
          ((C ∩ H ∩ xEastUnprimedSourceEvent m k) ∩ plusEvent) := by
      have hsource :
          (C ∩ H ∩ xEastUnprimedSourceEvent m k) ∩
            (minusEvent ∪ plusEvent) ⊆
          ((C ∩ H ∩ xEastUnprimedSourceEvent m k) ∩ minusEvent) ∪
          ((C ∩ H ∩ xEastUnprimedSourceEvent m k) ∩ plusEvent) := by
        intro s hs'
        have hsSource : s ∈ xEastUnprimedSourceEvent m k := hs'.1.2
        rcases hs'.2 with hsMinus | hsPlus
        · exact Or.inl ⟨⟨hs'.1.1, hsSource⟩, hsMinus⟩
        · exact Or.inr ⟨⟨hs'.1.1, hsSource⟩, hsPlus⟩
      calc
        simpleRandomWalkLaw[|C]
            ((C ∩ H ∩ xEastUnprimedSourceEvent m k) ∩
              (minusEvent ∪ plusEvent)) ≤
            simpleRandomWalkLaw[|C]
              (((C ∩ H ∩ xEastUnprimedSourceEvent m k) ∩ minusEvent) ∪
               ((C ∩ H ∩ xEastUnprimedSourceEvent m k) ∩ plusEvent)) :=
          measure_mono hsource
        _ ≤ _ := measure_union_le _ _
    _ ≤ sourceProp45OneSideError m := by
      exact add_le_add hminus hplus

/-- Finite disintegration of the unprimed `X₁` event into literal fixed
external-path atoms.  Variable atom lengths are retained because the source
conditions at a stopped external horizon. -/
structure XEastUnprimedFiniteAtomization
    (m k badCoeff : ℕ) where
  atoms : Finset ℕ
  q : ℕ → ℕ
  labels : ∀ j, Fin (q j) → IncrementPair
  horizon : Set Path
  bad : Set Path
  atomInputs : ∀ j ∈ atoms,
    XEastUnprimedExternalAtomInputs m k (q j) (labels j) horizon
  pairwise : (atoms : Set ℕ).PairwiseDisjoint
    (fun j ↦ externalPathWalkAtom (List.ofFn (labels j)))
  cover : xEastUnprimedSourceEvent m k ⊆ bad ∪
    ⋃ j ∈ atoms,
      externalPathWalkAtom (List.ofFn (labels j)) ∩ horizon ∩
        xEastUnprimedSourceEvent m k
  bad_bound : simpleRandomWalkLaw bad ≤
    sourceExceptionalRateWithPrefactor m badCoeff kappa

theorem eventually_sourceProp45OneSideError_le :
    ∀ᶠ m : ℕ in atTop,
      sourceProp45OneSideError m ≤
        sourceExceptionalRateWithPrefactor m 3 kappa := by
  filter_upwards [eventually_source_errors_le_exceptional] with m hm
  rw [sourceProp45OneSideError]
  calc
    (ENNReal.ofReal (Real.exp (-sourceRate m)) +
        ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ)))) +
        ENNReal.ofReal (Real.exp (-sourceRate m)) ≤
      (sourceExceptionalRate m kappa + sourceExceptionalRate m kappa) +
        sourceExceptionalRate m kappa := add_le_add (add_le_add hm.1 hm.2) hm.1
    _ = sourceExceptionalRateWithPrefactor m 3 kappa := by
      simp only [sourceExceptionalRateWithPrefactor, Nat.cast_ofNat]
      ring

/-- The finite-atom source disintegration, Proposition-4.2 law, both
Chernoff/union estimates, and conditional-to-unconditional summation. -/
theorem XEastUnprimedFiniteAtomization.theta_measure_le
    {m k badCoeff : ℕ}
    (hs : SourceIntervalScale m (sourceBandLowerNat m) ∧
      SourceUpperScale m m)
    (habsorb : sourceProp45OneSideError m ≤
      sourceExceptionalRateWithPrefactor m 3 kappa)
    (h : XEastUnprimedFiniteAtomization m k badCoeff) :
    simpleRandomWalkLaw (xEastUnprimedSourceEvent m k) ≤
      sourceExceptionalRateWithPrefactor m (badCoeff + 3) kappa := by
  have hcore := measure_le_bad_add_of_finite_conditional_partition
    simpleRandomWalkLaw h.atoms
    (fun j ↦ externalPathWalkAtom (List.ofFn (h.labels j)))
    (xEastUnprimedSourceEvent m k) h.horizon h.bad
    (sourceProp45OneSideError m)
    (sourceExceptionalRateWithPrefactor m badCoeff kappa)
    (fun j _ ↦ measurableSet_externalPathWalkAtom (List.ofFn (h.labels j)))
    h.pairwise h.cover h.bad_bound
    (fun j hj ↦ (h.atomInputs j hj).conditional_theta_le hs)
  calc
    simpleRandomWalkLaw (xEastUnprimedSourceEvent m k) ≤
      sourceExceptionalRateWithPrefactor m badCoeff kappa +
        sourceProp45OneSideError m := hcore
    _ ≤ sourceExceptionalRateWithPrefactor m badCoeff kappa +
        sourceExceptionalRateWithPrefactor m 3 kappa := by gcongr
    _ = sourceExceptionalRateWithPrefactor m (badCoeff + 3) kappa := by
      simp only [sourceExceptionalRateWithPrefactor]
      push_cast
      ring

end Erdos1166.HLOZProp47Prop45XEast
