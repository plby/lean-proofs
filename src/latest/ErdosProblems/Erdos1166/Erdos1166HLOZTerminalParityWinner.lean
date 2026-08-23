/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1166.Erdos1166HLOZStoppedMapLawReduced
import ErdosProblems.Erdos1166.Erdos1166HLOZPrimedOddRightWinner

/-!
# The two full-terminal stopped parity branches

The unprimed-odd and primed-even atoms observe a complete increment pair
through time `T + 1`, although the level-creation time is `T`.  Consequently
the increment at `T` is part of the atom and cannot be declared independent.
This file uses the completion clock `T + 1`; its retained direction is the
first genuinely fresh coordinate, at `T + 1`.

The deterministic grouped-event identities for the two terminal source
constraints are derived below from an explicit reconstruction of local times
along the terminal prefix.  The resulting source-facing theorems therefore
need no grouped-event identity premise: they prove the geometric vector law,
grouping, fresh-direction restart, capped profile, winner truncation, and
path-space transport from the literal stopped-source data.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

namespace Erdos1166.HLOZTerminalParityWinner

open HLOZDecomposition HLOZReconstruction HLOZActualStopped
  HLOZPrimedStopped HLOZIncompleteStoppedBlocks HLOZMixedCreationBlocks
  HLOZStoppedSourcePartition HLOZStoppedMixedReconstruction
  HLOZStoppedMapLaw HLOZStoppedMapLawReduced HLOZStoppedShape
  HLOZPrimedOddMixedReconstruction HLOZPrimedOddRightWinner
  HLOZProp48Truncated

noncomputable def stoppedCompletionTime (m k : ℕ)
    (omega : ℕ → Direction) : ℕ :=
  stoppedCreationTime m k omega + 1

theorem measurable_stoppedCompletionTime (m k : ℕ) :
    Measurable (stoppedCompletionTime m k) := by
  exact (measurable_of_countable (fun n : ℕ ↦ n + 1)).comp
    (measurable_stoppedCreationTime m k)

@[simp] theorem incrementShiftAfter_completion_zero
    (m k : ℕ) (omega : ℕ → Direction) :
    incrementShiftAfter (stoppedCompletionTime m k) omega 0 =
      incrementShiftAfter (stoppedCreationTime m k) omega 1 := by
  simp [stoppedCompletionTime, incrementShiftAfter]

theorem actualOddStoppedVector_fiber_inter_event {q : ℕ}
    (m k : ℕ) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (terminal : IncrementPair) (E : Finset (Fin (q + 1) → ℕ))
    (v : Fin (q + 1) → ℕ) :
    actualOddStoppedVectorEvent m k labels terminal E ∩
        (actualOddStoppedVector m k labels terminal E) ⁻¹' {v} =
      if v ∈ actualAdmissibleOddStoppedVectors m k labels terminal E then
        stoppedPrefixAtom (reconstructedOddStoppedPrefix labels v terminal)
      else ∅ := by
  classical
  let A := actualAdmissibleOddStoppedVectors m k labels terminal E
  let atom := fun w : Fin (q + 1) → ℕ ↦
    stoppedPrefixAtom (reconstructedOddStoppedPrefix labels w terminal)
  have hd : ∀ {u w}, u ∈ A → w ∈ A → u ≠ w →
      Disjoint (atom u) (atom w) := by
    intro u w hu hw huw
    apply stoppedPrefixAtoms_disjoint_of_firstKPrefixAt
      m k A (fun z ↦ reconstructedOddStoppedPrefix labels z terminal)
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
    · intro z z' hlen
      rw [reconstructedOddStoppedPrefix_length,
        reconstructedOddStoppedPrefix_length] at hlen ⊢
      omega
    · exact reconstructedOddStoppedPrefix_injective labels hnondist terminal
    · exact hu
    · exact hw
    · exact huw
  change finiteAtomEvent A atom ∩
      {omega | finiteAtomDecoder A atom omega = v} = _
  simpa only [A, atom] using
    finiteAtomDecoder_fiber_inter_event A atom hd v

theorem measurable_actualOddStoppedVector {q : ℕ}
    (m k : ℕ) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (terminal : IncrementPair) (E : Finset (Fin (q + 1) → ℕ)) :
    Measurable (actualOddStoppedVector m k labels terminal E) := by
  classical
  let A := actualAdmissibleOddStoppedVectors m k labels terminal E
  let atom := fun w : Fin (q + 1) → ℕ ↦
    stoppedPrefixAtom (reconstructedOddStoppedPrefix labels w terminal)
  have hd : ∀ {u w}, u ∈ A → w ∈ A → u ≠ w →
      Disjoint (atom u) (atom w) := by
    intro u w hu hw huw
    apply stoppedPrefixAtoms_disjoint_of_firstKPrefixAt
      m k A (fun z ↦ reconstructedOddStoppedPrefix labels z terminal)
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
    · intro z z' hlen
      rw [reconstructedOddStoppedPrefix_length,
        reconstructedOddStoppedPrefix_length] at hlen ⊢
      omega
    · exact reconstructedOddStoppedPrefix_injective labels hnondist terminal
    · exact hu
    · exact hw
    · exact huw
  apply measurable_finiteAtomDecoder A atom hd
  intro w _
  exact measurableSet_stoppedPrefixAtom _

theorem actualPrimedTerminalVector_fiber_inter_event {q : ℕ}
    (m k : ℕ) (first : Direction) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (terminal : IncrementPair) (E : Finset (Fin (q + 1) → ℕ))
    (v : Fin (q + 1) → ℕ) :
    actualPrimedTerminalVectorEvent m k first labels terminal E ∩
        (actualPrimedTerminalVector m k first labels terminal E) ⁻¹' {v} =
      if v ∈ actualAdmissiblePrimedTerminalVectors
          m k first labels terminal E then
        stoppedPrefixAtom
          (reconstructedPrimedTerminalStoppedPrefix first labels v terminal)
      else ∅ := by
  classical
  let A := actualAdmissiblePrimedTerminalVectors
    m k first labels terminal E
  let atom := fun w : Fin (q + 1) → ℕ ↦ stoppedPrefixAtom
    (reconstructedPrimedTerminalStoppedPrefix first labels w terminal)
  have hd : ∀ {u w}, u ∈ A → w ∈ A → u ≠ w →
      Disjoint (atom u) (atom w) := by
    intro u w hu hw huw
    apply stoppedPrefixAtoms_disjoint_of_firstKPrefixAt
      m k A (fun z ↦
        reconstructedPrimedTerminalStoppedPrefix first labels z terminal)
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
    · intro z z' hlen
      rw [reconstructedPrimedTerminalStoppedPrefix_length,
        reconstructedPrimedTerminalStoppedPrefix_length] at hlen ⊢
      omega
    · exact reconstructedPrimedTerminalStoppedPrefix_injective
        first labels hnondist terminal
    · exact hu
    · exact hw
    · exact huw
  change finiteAtomEvent A atom ∩
      {omega | finiteAtomDecoder A atom omega = v} = _
  simpa only [A, atom] using
    finiteAtomDecoder_fiber_inter_event A atom hd v

theorem measurable_actualPrimedTerminalVector {q : ℕ}
    (m k : ℕ) (first : Direction) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (terminal : IncrementPair) (E : Finset (Fin (q + 1) → ℕ)) :
    Measurable
      (actualPrimedTerminalVector m k first labels terminal E) := by
  classical
  let A := actualAdmissiblePrimedTerminalVectors
    m k first labels terminal E
  let atom := fun w : Fin (q + 1) → ℕ ↦ stoppedPrefixAtom
    (reconstructedPrimedTerminalStoppedPrefix first labels w terminal)
  have hd : ∀ {u w}, u ∈ A → w ∈ A → u ≠ w →
      Disjoint (atom u) (atom w) := by
    intro u w hu hw huw
    apply stoppedPrefixAtoms_disjoint_of_firstKPrefixAt
      m k A (fun z ↦
        reconstructedPrimedTerminalStoppedPrefix first labels z terminal)
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
    · intro z z' hlen
      rw [reconstructedPrimedTerminalStoppedPrefix_length,
        reconstructedPrimedTerminalStoppedPrefix_length] at hlen ⊢
      omega
    · exact reconstructedPrimedTerminalStoppedPrefix_injective
        first labels hnondist terminal
    · exact hu
    · exact hw
    · exact huw
  apply measurable_finiteAtomDecoder A atom hd
  intro w _
  exact measurableSet_stoppedPrefixAtom _

private theorem oddPrefix_completionTime_eq {q : ℕ}
    (m k : ℕ) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair) (v : Fin (q + 1) → ℕ)
    {E : Finset (Fin (q + 1) → ℕ)}
    (hv : v ∈ actualAdmissibleOddStoppedVectors m k labels terminal E)
    {omega : ℕ → Direction}
    (homega : omega ∈
      stoppedPrefixAtom (reconstructedOddStoppedPrefix labels v terminal)) :
    stoppedCompletionTime m k omega =
      (reconstructedOddStoppedPrefix labels v terminal).1 := by
  classical
  have hstop := (Finset.mem_filter.mp hv).2
  have hT := prefixAtom_subset_firstKSitesReachLevel_fiber_at
    (T := (reconstructedOddStoppedPrefix labels v terminal).1 - 1)
    (n := (reconstructedOddStoppedPrefix labels v terminal).1)
    (by omega) hstop homega
  unfold stoppedCompletionTime stoppedCreationTime
  rw [hT]
  change (reconstructedOddStoppedPrefix labels v terminal).1 - 1 + 1 =
    (reconstructedOddStoppedPrefix labels v terminal).1
  rw [reconstructedOddStoppedPrefix_length]
  omega

private theorem primedTerminalPrefix_completionTime_eq {q : ℕ}
    (m k : ℕ) (first : Direction) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair) (v : Fin (q + 1) → ℕ)
    {E : Finset (Fin (q + 1) → ℕ)}
    (hv : v ∈ actualAdmissiblePrimedTerminalVectors
      m k first labels terminal E) {omega : ℕ → Direction}
    (homega : omega ∈ stoppedPrefixAtom
      (reconstructedPrimedTerminalStoppedPrefix first labels v terminal)) :
    stoppedCompletionTime m k omega =
      (reconstructedPrimedTerminalStoppedPrefix
        first labels v terminal).1 := by
  classical
  have hstop := (Finset.mem_filter.mp hv).2
  have hT := prefixAtom_subset_firstKSitesReachLevel_fiber_at
    (T := (reconstructedPrimedTerminalStoppedPrefix
      first labels v terminal).1 - 1)
    (n := (reconstructedPrimedTerminalStoppedPrefix
      first labels v terminal).1) (by omega) hstop homega
  unfold stoppedCompletionTime stoppedCreationTime
  rw [hT]
  change (reconstructedPrimedTerminalStoppedPrefix
      first labels v terminal).1 - 1 + 1 =
    (reconstructedPrimedTerminalStoppedPrefix
      first labels v terminal).1
  rw [reconstructedPrimedTerminalStoppedPrefix_length]
  omega

theorem unprimedOdd_vectorFiberPastAfterCompletion {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (terminal : IncrementPair) (hm : 0 < m) (hk : 0 < k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (v : Fin (q + 1) → ℕ) (n : ℕ) :
    MeasurableSet[iidHistory (X := Direction) n]
      (((actualOddStoppedVectorEvent m k labels terminal
            (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C) ∩
          (actualOddStoppedVector m k labels terminal
            (unprimedOddSourceConstraint m k C labels terminal)) ⁻¹' {v}) ∩
        {omega | stoppedCompletionTime m k omega = n}) := by
  classical
  rw [unprimedOdd_source_partition m k C labels terminal hm hk hfree]
  let E := unprimedOddSourceConstraint m k C labels terminal
  let p := reconstructedOddStoppedPrefix labels v terminal
  change MeasurableSet[iidHistory (X := Direction) n]
    ((actualOddStoppedVectorEvent m k labels terminal E ∩
        (actualOddStoppedVector m k labels terminal E) ⁻¹' {v}) ∩
      {omega | stoppedCompletionTime m k omega = n})
  rw [actualOddStoppedVector_fiber_inter_event
    m k labels hnondist terminal E v]
  by_cases hv : v ∈ actualAdmissibleOddStoppedVectors
      m k labels terminal E
  · rw [if_pos hv]
    by_cases hpn : p.1 = n
    · have hsubset : stoppedPrefixAtom p ⊆
          {omega | stoppedCompletionTime m k omega = n} := by
        intro omega homega
        exact (oddPrefix_completionTime_eq
          m k labels terminal v hv homega).trans hpn
      rw [Set.inter_eq_left.mpr hsubset, ← hpn]
      exact measurableSet_stoppedPrefixAtom_iidHistory p
    · have hempty : stoppedPrefixAtom p ∩
          {omega | stoppedCompletionTime m k omega = n} = ∅ := by
        ext omega
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq,
          Set.mem_empty_iff_false, iff_false]
        rintro ⟨homega, hn⟩
        exact hpn ((oddPrefix_completionTime_eq
          m k labels terminal v hv homega).symm.trans hn)
      rw [hempty]
      exact @MeasurableSet.empty _ (iidHistory (X := Direction) n)
  · rw [if_neg hv, Set.empty_inter]
    exact @MeasurableSet.empty _ (iidHistory (X := Direction) n)

theorem primedEven_vectorFiberPastAfterCompletion {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (terminal : IncrementPair) (hm : 0 < m) (hk : 0 < k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (v : Fin (q + 1) → ℕ) (n : ℕ) :
    MeasurableSet[iidHistory (X := Direction) n]
      (((actualPrimedTerminalVectorEvent m k first labels terminal
            (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C) ∩
          (actualPrimedTerminalVector m k first labels terminal
            (primedEvenSourceConstraint m k C first labels terminal)) ⁻¹' {v}) ∩
        {omega | stoppedCompletionTime m k omega = n}) := by
  classical
  rw [primedEven_source_partition
    m k C first labels terminal hm hk hfree]
  let E := primedEvenSourceConstraint m k C first labels terminal
  let p := reconstructedPrimedTerminalStoppedPrefix first labels v terminal
  change MeasurableSet[iidHistory (X := Direction) n]
    ((actualPrimedTerminalVectorEvent m k first labels terminal E ∩
        (actualPrimedTerminalVector m k first labels terminal E) ⁻¹' {v}) ∩
      {omega | stoppedCompletionTime m k omega = n})
  rw [actualPrimedTerminalVector_fiber_inter_event
    m k first labels hnondist terminal E v]
  by_cases hv : v ∈ actualAdmissiblePrimedTerminalVectors
      m k first labels terminal E
  · rw [if_pos hv]
    by_cases hpn : p.1 = n
    · have hsubset : stoppedPrefixAtom p ⊆
          {omega | stoppedCompletionTime m k omega = n} := by
        intro omega homega
        exact (primedTerminalPrefix_completionTime_eq
          m k first labels terminal v hv homega).trans hpn
      rw [Set.inter_eq_left.mpr hsubset, ← hpn]
      exact measurableSet_stoppedPrefixAtom_iidHistory p
    · have hempty : stoppedPrefixAtom p ∩
          {omega | stoppedCompletionTime m k omega = n} = ∅ := by
        ext omega
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq,
          Set.mem_empty_iff_false, iff_false]
        rintro ⟨homega, hn⟩
        exact hpn ((primedTerminalPrefix_completionTime_eq
          m k first labels terminal v hv homega).symm.trans hn)
      rw [hempty]
      exact @MeasurableSet.empty _ (iidHistory (X := Direction) n)
  · rw [if_neg hv, Set.empty_inter]
    exact @MeasurableSet.empty _ (iidHistory (X := Direction) n)

theorem unprimedOdd_sourcePastAfterCompletion {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (terminal : IncrementPair) (hm : 0 < m) (hk : 0 < k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C) (n : ℕ) :
    MeasurableSet[iidHistory (X := Direction) n]
      ((actualOddStoppedVectorEvent m k labels terminal
          (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C) ∩
        {omega | stoppedCompletionTime m k omega = n}) := by
  let A := actualOddStoppedVectorEvent m k labels terminal
    (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C
  let X := actualOddStoppedVector m k labels terminal
    (unprimedOddSourceConstraint m k C labels terminal)
  have heq : A ∩ {omega | stoppedCompletionTime m k omega = n} =
      ⋃ v : Fin (q + 1) → ℕ,
        ((A ∩ X ⁻¹' {v}) ∩
          {omega | stoppedCompletionTime m k omega = n}) := by
    ext omega
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_preimage,
      Set.mem_singleton_iff, A, X]
    constructor
    · intro h
      exact ⟨actualOddStoppedVector m k labels terminal
        (unprimedOddSourceConstraint m k C labels terminal) omega,
        ⟨h.1, rfl⟩, h.2⟩
    · rintro ⟨v, ⟨hA, _⟩, hn⟩
      exact ⟨hA, hn⟩
  rw [show (actualOddStoppedVectorEvent m k labels terminal
      (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C) ∩
        {omega | stoppedCompletionTime m k omega = n} =
      A ∩ {omega | stoppedCompletionTime m k omega = n} by rfl, heq]
  exact MeasurableSet.iUnion fun v ↦
    unprimedOdd_vectorFiberPastAfterCompletion
      m k C labels hnondist terminal hm hk hfree v n

theorem primedEven_sourcePastAfterCompletion {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (terminal : IncrementPair) (hm : 0 < m) (hk : 0 < k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C) (n : ℕ) :
    MeasurableSet[iidHistory (X := Direction) n]
      ((actualPrimedTerminalVectorEvent m k first labels terminal
          (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C) ∩
        {omega | stoppedCompletionTime m k omega = n}) := by
  let A := actualPrimedTerminalVectorEvent m k first labels terminal
    (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C
  let X := actualPrimedTerminalVector m k first labels terminal
    (primedEvenSourceConstraint m k C first labels terminal)
  have heq : A ∩ {omega | stoppedCompletionTime m k omega = n} =
      ⋃ v : Fin (q + 1) → ℕ,
        ((A ∩ X ⁻¹' {v}) ∩
          {omega | stoppedCompletionTime m k omega = n}) := by
    ext omega
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_preimage,
      Set.mem_singleton_iff, A, X]
    constructor
    · intro h
      exact ⟨actualPrimedTerminalVector m k first labels terminal
        (primedEvenSourceConstraint m k C first labels terminal) omega,
        ⟨h.1, rfl⟩, h.2⟩
    · rintro ⟨v, ⟨hA, _⟩, hn⟩
      exact ⟨hA, hn⟩
  rw [show (actualPrimedTerminalVectorEvent m k first labels terminal
      (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C) ∩
        {omega | stoppedCompletionTime m k omega = n} =
      A ∩ {omega | stoppedCompletionTime m k omega = n} by rfl, heq]
  exact MeasurableSet.iUnion fun v ↦
    primedEven_vectorFiberPastAfterCompletion
      m k C first labels hnondist terminal hm hk hfree v n

private theorem activeFree_capped_hasLaw_of_joint {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (m : ℕ)
    (C : Finset Site)
    (activeBases : Finset (StoppedExternalBase a labels))
    (externalLeft externalRight : StoppedExternalBase a labels → ℕ)
    (V : Finset (Fin (q + 1) → ℕ))
    (P : Measure (ℕ → Direction))
    (X : (ℕ → Direction) → (Fin (q + 1) → ℕ))
    (D : (ℕ → Direction) → Direction)
    (hjoint : HasLaw (fun omega ↦ (X omega, D omega))
      (((HLOZUrn.runVectorMeasure (q + 1))[|(V : Set _)]).prod
        directionLaw) P)
    (hGroupedEvent : (V : Set (Fin (q + 1) → ℕ)) =
      (fun v ↦ stoppedPaperBlockSums a labels
        (stoppedPaperBlockVector a labels v)) ⁻¹'
        stoppedMixedBlockSumEvent a labels m C
          externalLeft externalRight)
    (hMixedCoordinatePos : ∀ b, HLOZUrn.negBinMeasure
      (Fintype.card (StoppedExternalIndex a labels b))
        (stoppedMixedBlockValues a labels m C
          externalLeft externalRight b : Set ℕ) ≠ 0) :
    HasLaw
      (fun omega ↦
        (restrictActiveFreeStoppedBase a labels C activeBases
          (stoppedPaperBlockSums a labels
            (stoppedPaperBlockVector a labels (X omega))), D omega))
      ((sourceCappedProfileMeasure m
        (activeFreeStoppedShape a labels C activeBases)
        (activeFreeCapProfile a labels C activeBases
          externalLeft externalRight)).prod directionLaw) P := by
  let S := fun v : Fin (q + 1) → ℕ ↦ stoppedPaperBlockSums a labels
    (stoppedPaperBlockVector a labels v)
  let R := restrictActiveFreeStoppedBase a labels C activeBases
  have hgrouped := stoppedPaperBlockSums_hasLaw_mixed_finset
    a labels m C externalLeft externalRight V hGroupedEvent
  have hmapS :
      ((HLOZUrn.runVectorMeasure (q + 1))[|(V : Set _)]).map S =
        (stoppedBlockNegBinMeasure a labels)[|
          stoppedMixedBlockSumEvent a labels m C
            externalLeft externalRight] := by
    simpa only [S] using hgrouped.map_eq
  have hCappedLaw := stoppedBlockNegBinMeasure_cond_mixed_map_activeFree
    a labels m C activeBases externalLeft externalRight hMixedCoordinatePos
  have hmapRS :
      ((HLOZUrn.runVectorMeasure (q + 1))[|(V : Set _)]).map
          (fun v ↦ R (S v)) =
        sourceCappedProfileMeasure m
          (activeFreeStoppedShape a labels C activeBases)
          (activeFreeCapProfile a labels C activeBases
            externalLeft externalRight) := by
    change ((HLOZUrn.runVectorMeasure (q + 1))[|(V : Set _)]).map
      (R ∘ S) = _
    have hR : Measurable R :=
      measurable_restrictActiveFreeStoppedBase a labels C activeBases
    have hS : Measurable S :=
      (measurable_stoppedPaperBlockSums a labels).comp
        (measurable_stoppedPaperBlockVector a labels)
    rw [← Measure.map_map hR hS, hmapS]
    exact hCappedLaw
  have hRS : Measurable (fun v ↦ R (S v)) :=
    (measurable_restrictActiveFreeStoppedBase
      a labels C activeBases).comp
      ((measurable_stoppedPaperBlockSums a labels).comp
        (measurable_stoppedPaperBlockVector a labels))
  simpa only [S, R] using
    hasLaw_map_fst_prod_direction hjoint (fun v ↦ R (S v)) hRS hmapRS

theorem unprimedOdd_activeFreeWinning_capped_map_law {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (terminal : IncrementPair) (hm : 0 < m) (hk : 0 < k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (externalLeft externalRight :
      StoppedExternalBase (0, 0) labels → ℕ)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels))
    (hGroupedEvent :
      (actualAdmissibleOddStoppedVectors m k labels terminal
          (unprimedOddSourceConstraint m k C labels terminal) : Set _) =
        (fun v ↦ stoppedPaperBlockSums (0, 0) labels
          (stoppedPaperBlockVector (0, 0) labels v)) ⁻¹'
          stoppedMixedBlockSumEvent (0, 0) labels m C
            externalLeft externalRight)
    (hMixedCoordinatePos : ∀ b, HLOZUrn.negBinMeasure
      (Fintype.card (StoppedExternalIndex (0, 0) labels b))
        (stoppedMixedBlockValues (0, 0) labels m C
          externalLeft externalRight b : Set ℕ) ≠ 0) :
    HasLaw
      (fun omega ↦
        (restrictActiveFreeStoppedBase (0, 0) labels C activeBases
            (stoppedPaperBlockSums (0, 0) labels
              (stoppedPaperBlockVector (0, 0) labels
                (actualOddStoppedVector m k labels terminal
                  (unprimedOddSourceConstraint m k C labels terminal)
                    omega))),
          incrementShiftAfter (stoppedCompletionTime m k) omega 0))
      ((sourceCappedProfileMeasure m
          (activeFreeStoppedShape (0, 0) labels C activeBases)
          (activeFreeCapProfile (0, 0) labels C activeBases
            externalLeft externalRight)).prod directionLaw)
      incrementLaw[|
        actualOddStoppedVectorEvent m k labels terminal
            (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C] := by
  let E := unprimedOddSourceConstraint m k C labels terminal
  let A := actualOddStoppedVectorEvent m k labels terminal
    (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C
  let X := actualOddStoppedVector m k labels terminal E
  let tau := stoppedCompletionTime m k
  have hX : Measurable X :=
    measurable_actualOddStoppedVector m k labels hnondist terminal E
  have hsource : HasLaw X
      ((HLOZUrn.runVectorMeasure (q + 1))[|
        (actualAdmissibleOddStoppedVectors m k labels terminal E : Set _)])
      incrementLaw[|A] := by
    simpa only [E, A, X] using unprimedOdd_source_hasLaw
      m k C labels hnondist terminal hm hk hfree
  have hjoint : HasLaw
      (fun omega ↦ (X omega, incrementShiftAfter tau omega 0))
      (((HLOZUrn.runVectorMeasure (q + 1))[|
          (actualAdmissibleOddStoppedVectors m k labels terminal E : Set _)]).prod
        directionLaw) incrementLaw[|A] := by
    apply hasLaw_prod_direction_after tau A X _
      (measurable_stoppedCompletionTime m k)
    · intro n
      simpa only [A, tau] using unprimedOdd_sourcePastAfterCompletion
        m k C labels hnondist terminal hm hk hfree n
    · exact hX
    · intro v n
      simpa only [A, X, tau, Set.inter_assoc] using
        unprimedOdd_vectorFiberPastAfterCompletion
          m k C labels hnondist terminal hm hk hfree v n
    · exact hsource
  exact activeFree_capped_hasLaw_of_joint
    (0, 0) labels m C activeBases externalLeft externalRight
    (actualAdmissibleOddStoppedVectors m k labels terminal E)
    incrementLaw[|A] X (fun omega ↦ incrementShiftAfter tau omega 0)
    hjoint (by simpa only [E] using hGroupedEvent) hMixedCoordinatePos

theorem primedEven_activeFreeWinning_capped_map_law {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (terminal : IncrementPair) (hm : 0 < m) (hk : 0 < k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (externalLeft externalRight :
      StoppedExternalBase (primedInitialBase first) labels → ℕ)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels))
    (hGroupedEvent :
      (actualAdmissiblePrimedTerminalVectors m k first labels terminal
          (primedEvenSourceConstraint m k C first labels terminal) : Set _) =
        (fun v ↦ stoppedPaperBlockSums (primedInitialBase first) labels
          (stoppedPaperBlockVector (primedInitialBase first) labels v)) ⁻¹'
          stoppedMixedBlockSumEvent (primedInitialBase first) labels m C
            externalLeft externalRight)
    (hMixedCoordinatePos : ∀ b, HLOZUrn.negBinMeasure
      (Fintype.card
        (StoppedExternalIndex (primedInitialBase first) labels b))
        (stoppedMixedBlockValues (primedInitialBase first) labels m C
          externalLeft externalRight b : Set ℕ) ≠ 0) :
    HasLaw
      (fun omega ↦
        (restrictActiveFreeStoppedBase (primedInitialBase first) labels C
            activeBases
            (stoppedPaperBlockSums (primedInitialBase first) labels
              (stoppedPaperBlockVector (primedInitialBase first) labels
                (actualPrimedTerminalVector m k first labels terminal
                  (primedEvenSourceConstraint m k C first labels terminal)
                    omega))),
          incrementShiftAfter (stoppedCompletionTime m k) omega 0))
      ((sourceCappedProfileMeasure m
          (activeFreeStoppedShape (primedInitialBase first) labels C
            activeBases)
          (activeFreeCapProfile (primedInitialBase first) labels C
            activeBases externalLeft externalRight)).prod directionLaw)
      incrementLaw[|
        actualPrimedTerminalVectorEvent m k first labels terminal
            (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C] := by
  let E := primedEvenSourceConstraint m k C first labels terminal
  let A := actualPrimedTerminalVectorEvent m k first labels terminal
    (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C
  let X := actualPrimedTerminalVector m k first labels terminal E
  let tau := stoppedCompletionTime m k
  have hX : Measurable X := measurable_actualPrimedTerminalVector
    m k first labels hnondist terminal E
  have hsource : HasLaw X
      ((HLOZUrn.runVectorMeasure (q + 1))[|
        (actualAdmissiblePrimedTerminalVectors
          m k first labels terminal E : Set _)]) incrementLaw[|A] := by
    simpa only [E, A, X] using primedEven_source_hasLaw
      m k C first labels hnondist terminal hm hk hfree
  have hjoint : HasLaw
      (fun omega ↦ (X omega, incrementShiftAfter tau omega 0))
      (((HLOZUrn.runVectorMeasure (q + 1))[|
          (actualAdmissiblePrimedTerminalVectors
            m k first labels terminal E : Set _)]).prod directionLaw)
        incrementLaw[|A] := by
    apply hasLaw_prod_direction_after tau A X _
      (measurable_stoppedCompletionTime m k)
    · intro n
      simpa only [A, tau] using primedEven_sourcePastAfterCompletion
        m k C first labels hnondist terminal hm hk hfree n
    · exact hX
    · intro v n
      simpa only [A, X, tau, Set.inter_assoc] using
        primedEven_vectorFiberPastAfterCompletion
          m k C first labels hnondist terminal hm hk hfree v n
    · exact hsource
  exact activeFree_capped_hasLaw_of_joint
    (primedInitialBase first) labels m C activeBases externalLeft externalRight
    (actualAdmissiblePrimedTerminalVectors m k first labels terminal E)
    incrementLaw[|A] X (fun omega ↦ incrementShiftAfter tau omega 0)
    hjoint (by simpa only [E] using hGroupedEvent) hMixedCoordinatePos

/-! ### The two missing winner filters

The terminal source reconstruction determines the opposite external profile.
The shape-bearing side is fixed by the stopped index family: left in the
unprimed-odd branch and right in the primed-even branch.  We therefore keep
only that genuinely terminal-dependent opposite profile as an argument. -/

noncomputable def unprimedOddTieLeftWinnerBases {q : ℕ}
    (labels : Fin q → IncrementPair)
    (externalRight : StoppedExternalBase (0, 0) labels → ℕ)
    (candidateBases : Finset (StoppedExternalBase (0, 0) labels)) :
    Finset (StoppedExternalBase (0, 0) labels) :=
  candidateBases.filter fun b ↦
    externalRight b ≤ stoppedExternalLeft (0, 0) labels b

theorem unprimedOddTieLeftWinnerBases_left {q : ℕ}
    (labels : Fin q → IncrementPair)
    (externalRight : StoppedExternalBase (0, 0) labels → ℕ)
    (candidateBases : Finset (StoppedExternalBase (0, 0) labels))
    (b : ActiveFreeStoppedBase (0, 0) labels C
      (unprimedOddTieLeftWinnerBases labels externalRight candidateBases)) :
    externalRight b.1 ≤ stoppedExternalLeft (0, 0) labels b.1 := by
  exact (Finset.mem_filter.mp b.2.1).2

theorem unprimedOddTieLeftWinnerBases_cap_eq_shape {q : ℕ}
    (labels : Fin q → IncrementPair) (C : Finset Site)
    (externalRight : StoppedExternalBase (0, 0) labels → ℕ)
    (candidateBases : Finset (StoppedExternalBase (0, 0) labels))
    (b : ActiveFreeStoppedBase (0, 0) labels C
      (unprimedOddTieLeftWinnerBases labels externalRight candidateBases)) :
    activeFreeCapProfile (0, 0) labels C
        (unprimedOddTieLeftWinnerBases labels externalRight candidateBases)
        (stoppedExternalLeft (0, 0) labels) externalRight b =
      activeFreeStoppedShape (0, 0) labels C
        (unprimedOddTieLeftWinnerBases labels externalRight candidateBases) b := by
  unfold activeFreeCapProfile activeFreeStoppedShape
  rw [max_eq_left
    (unprimedOddTieLeftWinnerBases_left labels externalRight candidateBases b)]
  exact (card_stoppedExternalIndex_eq_stoppedExternalLeft
    (0, 0) labels (by norm_num [HLOZPairing.chessEven]) b.1
      (stoppedExternalBase_chessEven labels b.1)).symm

noncomputable def primedEvenStrictRightWinnerBases {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (externalLeft :
      StoppedExternalBase (primedInitialBase first) labels → ℕ)
    (candidateBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    Finset (StoppedExternalBase (primedInitialBase first) labels) :=
  candidateBases.filter fun b ↦
    externalLeft b < primedStoppedExternalRight first labels b

theorem primedEvenStrictRightWinnerBases_right {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (externalLeft :
      StoppedExternalBase (primedInitialBase first) labels → ℕ)
    (candidateBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels))
    (b : ActiveFreeStoppedBase (primedInitialBase first) labels C
      (primedEvenStrictRightWinnerBases
        first labels externalLeft candidateBases)) :
    externalLeft b.1 ≤ primedStoppedExternalRight first labels b.1 := by
  exact (Finset.mem_filter.mp b.2.1).2.le

theorem primedEvenStrictRightWinnerBases_cap_eq_shape {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (C : Finset Site)
    (externalLeft :
      StoppedExternalBase (primedInitialBase first) labels → ℕ)
    (candidateBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels))
    (b : ActiveFreeStoppedBase (primedInitialBase first) labels C
      (primedEvenStrictRightWinnerBases
        first labels externalLeft candidateBases)) :
    activeFreeCapProfile (primedInitialBase first) labels C
        (primedEvenStrictRightWinnerBases
          first labels externalLeft candidateBases)
        externalLeft (primedStoppedExternalRight first labels) b =
      activeFreeStoppedShape (primedInitialBase first) labels C
        (primedEvenStrictRightWinnerBases
          first labels externalLeft candidateBases) b := by
  unfold activeFreeCapProfile activeFreeStoppedShape
  rw [max_eq_right
    (primedEvenStrictRightWinnerBases_right
      first labels externalLeft candidateBases b)]
  exact (card_stoppedExternalIndex_eq_primedStoppedExternalRight
    first labels b.1).symm

private theorem mixedCoordinatePos_of_grouped_nonempty {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (m : ℕ)
    (C : Finset Site)
    (externalLeft externalRight : StoppedExternalBase a labels → ℕ)
    (V : Finset (Fin (q + 1) → ℕ))
    (hGroupedEvent : (V : Set (Fin (q + 1) → ℕ)) =
      (fun v ↦ stoppedPaperBlockSums a labels
        (stoppedPaperBlockVector a labels v)) ⁻¹'
        stoppedMixedBlockSumEvent a labels m C
          externalLeft externalRight)
    (hne : V.Nonempty) :
    ∀ b, HLOZUrn.negBinMeasure
      (Fintype.card (StoppedExternalIndex a labels b))
        (stoppedMixedBlockValues a labels m C
          externalLeft externalRight b : Set ℕ) ≠ 0 := by
  obtain ⟨v, hv⟩ := hne
  apply stoppedMixedCoordinatePos_of_event_nonempty
    a labels m C externalLeft externalRight
  refine ⟨stoppedPaperBlockSums a labels
    (stoppedPaperBlockVector a labels v), ?_⟩
  have hvSet : v ∈ (V : Set (Fin (q + 1) → ℕ)) := hv
  rw [hGroupedEvent] at hvSet
  exact hvSet

theorem unprimedOdd_activeFreeWinning_capped_map_law_reduced {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (terminal : IncrementPair) (hm : 0 < m) (hk : 0 < k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (externalRight : StoppedExternalBase (0, 0) labels → ℕ)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels))
    (hGroupedEvent :
      (actualAdmissibleOddStoppedVectors m k labels terminal
          (unprimedOddSourceConstraint m k C labels terminal) : Set _) =
        (fun v ↦ stoppedPaperBlockSums (0, 0) labels
          (stoppedPaperBlockVector (0, 0) labels v)) ⁻¹'
          stoppedMixedBlockSumEvent (0, 0) labels m C
            (stoppedExternalLeft (0, 0) labels) externalRight)
    (hne : (actualAdmissibleOddStoppedVectors m k labels terminal
      (unprimedOddSourceConstraint m k C labels terminal)).Nonempty) :
    HasLaw
      (fun omega ↦
        (restrictActiveFreeStoppedBase (0, 0) labels C activeBases
            (stoppedPaperBlockSums (0, 0) labels
              (stoppedPaperBlockVector (0, 0) labels
                (actualOddStoppedVector m k labels terminal
                  (unprimedOddSourceConstraint m k C labels terminal)
                    omega))),
          incrementShiftAfter (stoppedCompletionTime m k) omega 0))
      ((sourceCappedProfileMeasure m
          (activeFreeStoppedShape (0, 0) labels C activeBases)
          (activeFreeCapProfile (0, 0) labels C activeBases
            (stoppedExternalLeft (0, 0) labels) externalRight)).prod
        directionLaw)
      incrementLaw[|
        actualOddStoppedVectorEvent m k labels terminal
            (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C] := by
  apply unprimedOdd_activeFreeWinning_capped_map_law
    m k C labels hnondist terminal hm hk hfree
      (stoppedExternalLeft (0, 0) labels) externalRight activeBases
  · exact hGroupedEvent
  · exact mixedCoordinatePos_of_grouped_nonempty
      (0, 0) labels m C (stoppedExternalLeft (0, 0) labels)
        externalRight
        (actualAdmissibleOddStoppedVectors m k labels terminal
          (unprimedOddSourceConstraint m k C labels terminal))
        hGroupedEvent hne

theorem primedEven_activeFreeWinning_capped_map_law_reduced {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (terminal : IncrementPair) (hm : 0 < m) (hk : 0 < k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (externalLeft :
      StoppedExternalBase (primedInitialBase first) labels → ℕ)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels))
    (hGroupedEvent :
      (actualAdmissiblePrimedTerminalVectors m k first labels terminal
          (primedEvenSourceConstraint m k C first labels terminal) : Set _) =
        (fun v ↦ stoppedPaperBlockSums (primedInitialBase first) labels
          (stoppedPaperBlockVector (primedInitialBase first) labels v)) ⁻¹'
          stoppedMixedBlockSumEvent (primedInitialBase first) labels m C
            externalLeft (primedStoppedExternalRight first labels))
    (hne : (actualAdmissiblePrimedTerminalVectors m k first labels terminal
      (primedEvenSourceConstraint m k C first labels terminal)).Nonempty) :
    HasLaw
      (fun omega ↦
        (restrictActiveFreeStoppedBase (primedInitialBase first) labels C
            activeBases
            (stoppedPaperBlockSums (primedInitialBase first) labels
              (stoppedPaperBlockVector (primedInitialBase first) labels
                (actualPrimedTerminalVector m k first labels terminal
                  (primedEvenSourceConstraint m k C first labels terminal)
                    omega))),
          incrementShiftAfter (stoppedCompletionTime m k) omega 0))
      ((sourceCappedProfileMeasure m
          (activeFreeStoppedShape (primedInitialBase first) labels C
            activeBases)
          (activeFreeCapProfile (primedInitialBase first) labels C
            activeBases externalLeft
              (primedStoppedExternalRight first labels))).prod directionLaw)
      incrementLaw[|
        actualPrimedTerminalVectorEvent m k first labels terminal
            (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C] := by
  apply primedEven_activeFreeWinning_capped_map_law
    m k C first labels hnondist terminal hm hk hfree
      externalLeft (primedStoppedExternalRight first labels) activeBases
  · exact hGroupedEvent
  · exact mixedCoordinatePos_of_grouped_nonempty
      (primedInitialBase first) labels m C externalLeft
        (primedStoppedExternalRight first labels)
        (actualAdmissiblePrimedTerminalVectors
          m k first labels terminal
            (primedEvenSourceConstraint m k C first labels terminal))
        hGroupedEvent hne

/-! ### Measurable path statistics at the completion clock -/

noncomputable def unprimedOddActiveFreeStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    (ℕ → Direction) →
      (ActiveFreeStoppedBase (0, 0) labels C activeBases → ℕ) × Direction :=
  fun omega ↦
    (restrictActiveFreeStoppedBase (0, 0) labels C activeBases
        (stoppedPaperBlockSums (0, 0) labels
          (stoppedPaperBlockVector (0, 0) labels
            (actualOddStoppedVector m k labels terminal
              (unprimedOddSourceConstraint m k C labels terminal) omega))),
      incrementShiftAfter (stoppedCompletionTime m k) omega 0)

noncomputable def primedEvenActiveFreeStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair) (terminal : IncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    (ℕ → Direction) →
      (ActiveFreeStoppedBase (primedInitialBase first) labels C activeBases →
        ℕ) × Direction :=
  fun omega ↦
    (restrictActiveFreeStoppedBase (primedInitialBase first) labels C
        activeBases
        (stoppedPaperBlockSums (primedInitialBase first) labels
          (stoppedPaperBlockVector (primedInitialBase first) labels
            (actualPrimedTerminalVector m k first labels terminal
              (primedEvenSourceConstraint m k C first labels terminal)
                omega))),
      incrementShiftAfter (stoppedCompletionTime m k) omega 0)

theorem measurable_unprimedOddActiveFreeStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (terminal : IncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    Measurable
      (unprimedOddActiveFreeStatistic
        m k C labels terminal activeBases) := by
  apply Measurable.prodMk
  · exact (measurable_restrictActiveFreeStoppedBase
      (0, 0) labels C activeBases).comp
        ((measurable_stoppedPaperBlockSums (0, 0) labels).comp
          ((measurable_stoppedPaperBlockVector (0, 0) labels).comp
            (measurable_actualOddStoppedVector m k labels hnondist terminal
              (unprimedOddSourceConstraint m k C labels terminal))))
  · exact (measurable_pi_apply 0).comp
      (measurable_incrementShiftAfter (measurable_stoppedCompletionTime m k))

theorem measurable_primedEvenActiveFreeStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (terminal : IncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    Measurable
      (primedEvenActiveFreeStatistic
        m k C first labels terminal activeBases) := by
  apply Measurable.prodMk
  · exact (measurable_restrictActiveFreeStoppedBase
      (primedInitialBase first) labels C activeBases).comp
        ((measurable_stoppedPaperBlockSums
          (primedInitialBase first) labels).comp
          ((measurable_stoppedPaperBlockVector
            (primedInitialBase first) labels).comp
            (measurable_actualPrimedTerminalVector
              m k first labels hnondist terminal
                (primedEvenSourceConstraint m k C first labels terminal))))
  · exact (measurable_pi_apply 0).comp
      (measurable_incrementShiftAfter (measurable_stoppedCompletionTime m k))

noncomputable def unprimedOddActiveFreePathLazy {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    (ℕ → Site) → ActiveFreeStoppedBase (0, 0) labels C activeBases → ℕ :=
  fun s ↦ (liftIncrementStatisticToPath
    (unprimedOddActiveFreeStatistic
      m k C labels terminal activeBases) s).1

noncomputable def unprimedOddActiveFreePathNext {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    (ℕ → Site) → Direction :=
  fun s ↦ (liftIncrementStatisticToPath
    (unprimedOddActiveFreeStatistic
      m k C labels terminal activeBases) s).2

noncomputable def primedEvenActiveFreePathLazy {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair) (terminal : IncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    (ℕ → Site) →
      ActiveFreeStoppedBase (primedInitialBase first) labels C activeBases → ℕ :=
  fun s ↦ (liftIncrementStatisticToPath
    (primedEvenActiveFreeStatistic
      m k C first labels terminal activeBases) s).1

noncomputable def primedEvenActiveFreePathNext {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair) (terminal : IncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    (ℕ → Site) → Direction :=
  fun s ↦ (liftIncrementStatisticToPath
    (primedEvenActiveFreeStatistic
      m k C first labels terminal activeBases) s).2

theorem measurable_unprimedOddActiveFreePathLazy {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (terminal : IncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    Measurable
      (unprimedOddActiveFreePathLazy
        m k C labels terminal activeBases) :=
  measurable_fst.comp (measurable_liftIncrementStatisticToPath
    (measurable_unprimedOddActiveFreeStatistic
      m k C labels hnondist terminal activeBases))

theorem measurable_unprimedOddActiveFreePathNext {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (terminal : IncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    Measurable
      (unprimedOddActiveFreePathNext
        m k C labels terminal activeBases) :=
  measurable_snd.comp (measurable_liftIncrementStatisticToPath
    (measurable_unprimedOddActiveFreeStatistic
      m k C labels hnondist terminal activeBases))

theorem measurable_primedEvenActiveFreePathLazy {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (terminal : IncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    Measurable
      (primedEvenActiveFreePathLazy
        m k C first labels terminal activeBases) :=
  measurable_fst.comp (measurable_liftIncrementStatisticToPath
    (measurable_primedEvenActiveFreeStatistic
      m k C first labels hnondist terminal activeBases))

theorem measurable_primedEvenActiveFreePathNext {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (terminal : IncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    Measurable
      (primedEvenActiveFreePathNext
        m k C first labels terminal activeBases) :=
  measurable_snd.comp (measurable_liftIncrementStatisticToPath
    (measurable_primedEvenActiveFreeStatistic
      m k C first labels hnondist terminal activeBases))

theorem unprimedOdd_activeFreeWinning_capped_path_map_law_reduced {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (terminal : IncrementPair) (hm : 0 < m) (hk : 0 < k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (externalRight : StoppedExternalBase (0, 0) labels → ℕ)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels))
    (hGroupedEvent :
      (actualAdmissibleOddStoppedVectors m k labels terminal
          (unprimedOddSourceConstraint m k C labels terminal) : Set _) =
        (fun v ↦ stoppedPaperBlockSums (0, 0) labels
          (stoppedPaperBlockVector (0, 0) labels v)) ⁻¹'
          stoppedMixedBlockSumEvent (0, 0) labels m C
            (stoppedExternalLeft (0, 0) labels) externalRight)
    (hne : (actualAdmissibleOddStoppedVectors m k labels terminal
      (unprimedOddSourceConstraint m k C labels terminal)).Nonempty) :
    (simpleRandomWalkLaw.restrict
        (simpleRandomWalk ''
          (actualOddStoppedVectorEvent m k labels terminal
              (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C))).map
        (liftIncrementStatisticToPath
          (unprimedOddActiveFreeStatistic
            m k C labels terminal activeBases)) =
      simpleRandomWalkLaw
          (simpleRandomWalk ''
            (actualOddStoppedVectorEvent m k labels terminal
                (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C)) •
        ((sourceCappedProfileMeasure m
          (activeFreeStoppedShape (0, 0) labels C activeBases)
          (activeFreeCapProfile (0, 0) labels C activeBases
            (stoppedExternalLeft (0, 0) labels) externalRight)).prod
              directionLaw) := by
  have hEvent : MeasurableSet
      (actualOddStoppedVectorEvent m k labels terminal
        (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C) := by
    rw [unprimedOdd_source_partition
      m k C labels terminal hm hk hfree]
    unfold actualOddStoppedVectorEvent
    exact MeasurableSet.iUnion fun v ↦ MeasurableSet.iUnion fun _ ↦
      measurableSet_stoppedPrefixAtom
        (reconstructedOddStoppedPrefix labels v terminal)
  apply liftIncrementStatistic_path_map_law hEvent
    (measurable_unprimedOddActiveFreeStatistic
      m k C labels hnondist terminal activeBases)
  exact unprimedOdd_activeFreeWinning_capped_map_law_reduced
    m k C labels hnondist terminal hm hk hfree externalRight activeBases
      hGroupedEvent hne

theorem primedEven_activeFreeWinning_capped_path_map_law_reduced {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (terminal : IncrementPair) (hm : 0 < m) (hk : 0 < k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (externalLeft :
      StoppedExternalBase (primedInitialBase first) labels → ℕ)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels))
    (hGroupedEvent :
      (actualAdmissiblePrimedTerminalVectors m k first labels terminal
          (primedEvenSourceConstraint m k C first labels terminal) : Set _) =
        (fun v ↦ stoppedPaperBlockSums (primedInitialBase first) labels
          (stoppedPaperBlockVector (primedInitialBase first) labels v)) ⁻¹'
          stoppedMixedBlockSumEvent (primedInitialBase first) labels m C
            externalLeft (primedStoppedExternalRight first labels))
    (hne : (actualAdmissiblePrimedTerminalVectors m k first labels terminal
      (primedEvenSourceConstraint m k C first labels terminal)).Nonempty) :
    (simpleRandomWalkLaw.restrict
        (simpleRandomWalk ''
          (actualPrimedTerminalVectorEvent m k first labels terminal
              (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C))).map
        (liftIncrementStatisticToPath
          (primedEvenActiveFreeStatistic
            m k C first labels terminal activeBases)) =
      simpleRandomWalkLaw
          (simpleRandomWalk ''
            (actualPrimedTerminalVectorEvent m k first labels terminal
                (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C)) •
        ((sourceCappedProfileMeasure m
          (activeFreeStoppedShape (primedInitialBase first) labels C
            activeBases)
          (activeFreeCapProfile (primedInitialBase first) labels C
            activeBases externalLeft
              (primedStoppedExternalRight first labels))).prod directionLaw) := by
  have hEvent : MeasurableSet
      (actualPrimedTerminalVectorEvent m k first labels terminal
        (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C) := by
    rw [primedEven_source_partition
      m k C first labels terminal hm hk hfree]
    unfold actualPrimedTerminalVectorEvent
    exact MeasurableSet.iUnion fun v ↦ MeasurableSet.iUnion fun _ ↦
      measurableSet_stoppedPrefixAtom
        (reconstructedPrimedTerminalStoppedPrefix first labels v terminal)
  apply liftIncrementStatistic_path_map_law hEvent
    (measurable_primedEvenActiveFreeStatistic
      m k C first labels hnondist terminal activeBases)
  exact primedEven_activeFreeWinning_capped_map_law_reduced
    m k C first labels hnondist terminal hm hk hfree externalLeft activeBases
      hGroupedEvent hne

/-! The two field-ready equation-(4.47) laws.  Their `PathNext` fields are
the first direction after the full terminal pair, not its already-conditioned
second half. -/

theorem unprimedOdd_tieLeftWinner_StoppedEquation447Atom_map_law {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (terminal : IncrementPair) (hm : 0 < m) (hk : 0 < k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (externalRight : StoppedExternalBase (0, 0) labels → ℕ)
    (candidateBases : Finset (StoppedExternalBase (0, 0) labels))
    (hGroupedEvent :
      (actualAdmissibleOddStoppedVectors m k labels terminal
          (unprimedOddSourceConstraint m k C labels terminal) : Set _) =
        (fun v ↦ stoppedPaperBlockSums (0, 0) labels
          (stoppedPaperBlockVector (0, 0) labels v)) ⁻¹'
          stoppedMixedBlockSumEvent (0, 0) labels m C
            (stoppedExternalLeft (0, 0) labels) externalRight)
    (hne : (actualAdmissibleOddStoppedVectors m k labels terminal
      (unprimedOddSourceConstraint m k C labels terminal)).Nonempty) :
    (simpleRandomWalkLaw.restrict
        (simpleRandomWalk ''
          (actualOddStoppedVectorEvent m k labels terminal
              (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C))).map
        (fun s ↦
          (unprimedOddActiveFreePathLazy m k C labels terminal
              (unprimedOddTieLeftWinnerBases
                labels externalRight candidateBases) s,
            unprimedOddActiveFreePathNext m k C labels terminal
              (unprimedOddTieLeftWinnerBases
                labels externalRight candidateBases) s)) =
      simpleRandomWalkLaw
          (simpleRandomWalk ''
            (actualOddStoppedVectorEvent m k labels terminal
                (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C)) •
        ((sourceTruncatedProfileMeasure m
          (activeFreeStoppedShape (0, 0) labels C
            (unprimedOddTieLeftWinnerBases
              labels externalRight candidateBases))).prod directionLaw) := by
  rw [← sourceCappedProfileMeasure_eq_truncated m
    (activeFreeStoppedShape (0, 0) labels C
      (unprimedOddTieLeftWinnerBases labels externalRight candidateBases))
    (activeFreeCapProfile (0, 0) labels C
      (unprimedOddTieLeftWinnerBases labels externalRight candidateBases)
      (stoppedExternalLeft (0, 0) labels) externalRight)
    (unprimedOddTieLeftWinnerBases_cap_eq_shape
      labels C externalRight candidateBases)]
  simpa only [unprimedOddActiveFreePathLazy,
    unprimedOddActiveFreePathNext, Prod.eta] using
      unprimedOdd_activeFreeWinning_capped_path_map_law_reduced
        m k C labels hnondist terminal hm hk hfree externalRight
          (unprimedOddTieLeftWinnerBases labels externalRight candidateBases)
          hGroupedEvent hne

theorem primedEven_strictRightWinner_StoppedEquation447Atom_map_law {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (terminal : IncrementPair) (hm : 0 < m) (hk : 0 < k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (externalLeft :
      StoppedExternalBase (primedInitialBase first) labels → ℕ)
    (candidateBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels))
    (hGroupedEvent :
      (actualAdmissiblePrimedTerminalVectors m k first labels terminal
          (primedEvenSourceConstraint m k C first labels terminal) : Set _) =
        (fun v ↦ stoppedPaperBlockSums (primedInitialBase first) labels
          (stoppedPaperBlockVector (primedInitialBase first) labels v)) ⁻¹'
          stoppedMixedBlockSumEvent (primedInitialBase first) labels m C
            externalLeft (primedStoppedExternalRight first labels))
    (hne : (actualAdmissiblePrimedTerminalVectors m k first labels terminal
      (primedEvenSourceConstraint m k C first labels terminal)).Nonempty) :
    (simpleRandomWalkLaw.restrict
        (simpleRandomWalk ''
          (actualPrimedTerminalVectorEvent m k first labels terminal
              (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C))).map
        (fun s ↦
          (primedEvenActiveFreePathLazy m k C first labels terminal
              (primedEvenStrictRightWinnerBases
                first labels externalLeft candidateBases) s,
            primedEvenActiveFreePathNext m k C first labels terminal
              (primedEvenStrictRightWinnerBases
                first labels externalLeft candidateBases) s)) =
      simpleRandomWalkLaw
          (simpleRandomWalk ''
            (actualPrimedTerminalVectorEvent m k first labels terminal
                (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C)) •
        ((sourceTruncatedProfileMeasure m
          (activeFreeStoppedShape (primedInitialBase first) labels C
            (primedEvenStrictRightWinnerBases
              first labels externalLeft candidateBases))).prod directionLaw) := by
  rw [← sourceCappedProfileMeasure_eq_truncated m
    (activeFreeStoppedShape (primedInitialBase first) labels C
      (primedEvenStrictRightWinnerBases
        first labels externalLeft candidateBases))
    (activeFreeCapProfile (primedInitialBase first) labels C
      (primedEvenStrictRightWinnerBases
        first labels externalLeft candidateBases)
      externalLeft (primedStoppedExternalRight first labels))
    (primedEvenStrictRightWinnerBases_cap_eq_shape
      first labels C externalLeft candidateBases)]
  simpa only [primedEvenActiveFreePathLazy,
    primedEvenActiveFreePathNext, Prod.eta] using
      primedEven_activeFreeWinning_capped_path_map_law_reduced
        m k C first labels hnondist terminal hm hk hfree externalLeft
          (primedEvenStrictRightWinnerBases
            first labels externalLeft candidateBases)
          hGroupedEvent hne

/-! ### Terminal-prefix local-time reconstruction

At the threshold time the full-terminal prefix is the matching nonterminal
stopped prefix followed by the first direction of `terminal`. -/

private theorem flattenPairs_append (pairs qs : List IncrementPair) :
    flattenPairs (pairs ++ qs) = flattenPairs pairs ++ flattenPairs qs := by
  induction pairs with
  | nil => rfl
  | cons p ps ih => simp [flattenPairs]

private theorem unprimedOdd_direction_before {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ)
    (terminal : IncrementPair) (r : ℕ)
    (hr : r < (reconstructedStoppedPrefix labels v).1) :
    extendPrefix (reconstructedOddStoppedPrefix labels v terminal).2 r =
      extendPrefix (reconstructedStoppedPrefix labels v).2 r := by
  unfold reconstructedOddStoppedPrefix reconstructedStoppedPrefix
  unfold stoppedPrefixOfDirectionList stoppedDirectionList
  unfold extendPrefix prefixOfDirectionList
  change r < (flattenPairs (stoppedPairList labels v)).length at hr
  have hfull : r < (flattenPairs (stoppedPairList labels v)).length +
      (flattenPairs [terminal]).length := by
    simpa using hr.trans_le (Nat.le_add_right _ _)
  simp [flattenPairs_append, hr, hfull]

private theorem unprimedOdd_terminal_direction {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ)
    (terminal : IncrementPair) :
    extendPrefix (reconstructedOddStoppedPrefix labels v terminal).2
        (reconstructedStoppedPrefix labels v).1 = terminal 0 := by
  unfold reconstructedOddStoppedPrefix reconstructedStoppedPrefix
  unfold stoppedPrefixOfDirectionList stoppedDirectionList
  unfold extendPrefix prefixOfDirectionList
  simp [flattenPairs, HLOZReconstruction.pairDirections]

private theorem primedEven_direction_before {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ) (terminal : IncrementPair)
    (r : ℕ)
    (hr : r < (reconstructedPrimedStoppedPrefix first labels v).1) :
    extendPrefix
        (reconstructedPrimedTerminalStoppedPrefix
          first labels v terminal).2 r =
      extendPrefix (reconstructedPrimedStoppedPrefix first labels v).2 r := by
  cases r with
  | zero =>
      simp [reconstructedPrimedTerminalStoppedPrefix,
        reconstructedPrimedStoppedPrefix, stoppedPrefixOfDirectionList,
        extendPrefix, prefixOfDirectionList]
  | succ r =>
      unfold reconstructedPrimedTerminalStoppedPrefix
        reconstructedPrimedStoppedPrefix
      unfold stoppedPrefixOfDirectionList primedStoppedDirectionList
      unfold extendPrefix prefixOfDirectionList
      change r + 1 < (first :: flattenPairs
        (primedStoppedPairList labels v)).length at hr
      have hr' : r < (flattenPairs
          (primedStoppedPairList labels v)).length := by simpa using hr
      have hfull : r < (flattenPairs
          (primedStoppedPairList labels v)).length +
          (flattenPairs [terminal]).length :=
        hr'.trans_le (Nat.le_add_right _ _)
      simp [flattenPairs_append, hr', hfull]

private theorem primedEven_terminal_direction {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ) (terminal : IncrementPair) :
    extendPrefix
        (reconstructedPrimedTerminalStoppedPrefix
          first labels v terminal).2
        (reconstructedPrimedStoppedPrefix first labels v).1 = terminal 0 := by
  unfold reconstructedPrimedTerminalStoppedPrefix
    reconstructedPrimedStoppedPrefix
  unfold stoppedPrefixOfDirectionList primedStoppedDirectionList
  unfold extendPrefix prefixOfDirectionList
  simp [flattenPairs, HLOZReconstruction.pairDirections]

private theorem unprimedOdd_position_before {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ)
    (terminal : IncrementPair) (j : ℕ)
    (hj : j ≤ (reconstructedStoppedPrefix labels v).1) :
    simpleRandomWalk
        (extendPrefix (reconstructedOddStoppedPrefix labels v terminal).2) j =
      simpleRandomWalk
        (extendPrefix (reconstructedStoppedPrefix labels v).2) j := by
  unfold simpleRandomWalk
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  apply unprimedOdd_direction_before labels v terminal
  have := Finset.mem_range.mp hr
  omega

private theorem primedEven_position_before {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ) (terminal : IncrementPair)
    (j : ℕ)
    (hj : j ≤ (reconstructedPrimedStoppedPrefix first labels v).1) :
    simpleRandomWalk (extendPrefix
        (reconstructedPrimedTerminalStoppedPrefix
          first labels v terminal).2) j =
      simpleRandomWalk
        (extendPrefix (reconstructedPrimedStoppedPrefix first labels v).2) j := by
  unfold simpleRandomWalk
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  apply primedEven_direction_before first labels v terminal
  have := Finset.mem_range.mp hr
  omega

private theorem unprimedOdd_threshold_eq {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ)
    (terminal : IncrementPair) :
    (reconstructedOddStoppedPrefix labels v terminal).1 - 1 =
      (reconstructedStoppedPrefix labels v).1 + 1 := by
  rw [reconstructedOddStoppedPrefix_length]
  change 2 * (q + ∑ i, v i + 1) - 1 =
    (stoppedDirectionList labels v).length + 1
  rw [stoppedDirectionList_length]
  omega

private theorem primedEven_threshold_eq {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ) (terminal : IncrementPair) :
    (reconstructedPrimedTerminalStoppedPrefix
        first labels v terminal).1 - 1 =
      (reconstructedPrimedStoppedPrefix first labels v).1 + 1 := by
  rw [reconstructedPrimedTerminalStoppedPrefix_length,
    reconstructedPrimedStoppedPrefix_length]
  omega

private theorem unprimedOdd_terminal_position {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ)
    (terminal : IncrementPair) :
    simpleRandomWalk
        (extendPrefix (reconstructedOddStoppedPrefix labels v terminal).2)
        ((reconstructedStoppedPrefix labels v).1 + 1) =
      stoppedTerminalBase labels + directionStep (terminal 0) := by
  rw [simpleRandomWalk_succ']
  rw [unprimedOdd_position_before labels v terminal _ le_rfl,
    reconstructedStoppedPrefix_current,
    unprimedOdd_terminal_direction]

private theorem primedEven_terminal_position {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ) (terminal : IncrementPair) :
    simpleRandomWalk (extendPrefix
        (reconstructedPrimedTerminalStoppedPrefix
          first labels v terminal).2)
        ((reconstructedPrimedStoppedPrefix first labels v).1 + 1) =
      primedStoppedTerminalSite first labels +
        directionStep (terminal 0) := by
  rw [simpleRandomWalk_succ']
  rw [primedEven_position_before first labels v terminal _ le_rfl,
    reconstructedPrimedStoppedPrefix_current,
    primedEven_terminal_direction]

theorem localTime_reconstructedOddStoppedPrefix_reduce {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ)
    (terminal : IncrementPair) (x : Site) :
    localTime
        (simpleRandomWalk
          (extendPrefix (reconstructedOddStoppedPrefix labels v terminal).2))
        ((reconstructedOddStoppedPrefix labels v terminal).1 - 1) x =
      localTime
          (simpleRandomWalk
            (extendPrefix (reconstructedStoppedPrefix labels v).2))
          (reconstructedStoppedPrefix labels v).1 x +
        if stoppedTerminalBase labels + directionStep (terminal 0) = x then
          1 else 0 := by
  rw [unprimedOdd_threshold_eq, localTime_succ]
  rw [localTime_congr_prefix
    (unprimedOdd_position_before labels v terminal) x]
  rw [unprimedOdd_terminal_position]

theorem localTime_reconstructedPrimedTerminalStoppedPrefix_reduce {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ) (terminal : IncrementPair) (x : Site) :
    localTime
        (simpleRandomWalk (extendPrefix
          (reconstructedPrimedTerminalStoppedPrefix
            first labels v terminal).2))
        ((reconstructedPrimedTerminalStoppedPrefix
          first labels v terminal).1 - 1) x =
      localTime
          (simpleRandomWalk (extendPrefix
            (reconstructedPrimedStoppedPrefix first labels v).2))
          (reconstructedPrimedStoppedPrefix first labels v).1 x +
        if primedStoppedTerminalSite first labels +
            directionStep (terminal 0) = x then 1 else 0 := by
  rw [primedEven_threshold_eq, localTime_succ]
  rw [localTime_congr_prefix
    (primedEven_position_before first labels v terminal) x]
  rw [primedEven_terminal_position]

/-! ### Literal terminal-source specializations

These are the opposite fixed profiles read from the zero-run reference path
used by `unprimedOddPairMax` and `primedEvenPairMax`.  The terminal-prefix
local-time reconstruction below then identifies each literal source
constraint with the required mixed-block preimage. -/

noncomputable def unprimedOddTerminalExternalLocalTime {q : ℕ}
    (labels : Fin q → IncrementPair) (terminal : IncrementPair) :
    Site → ℕ :=
  fun x ↦ localTime
    (simpleRandomWalk (unprimedOddReference labels terminal))
    ((reconstructedOddStoppedPrefix labels
      (zeroStoppedVector q) terminal).1 - 1) x

noncomputable def unprimedOddTerminalExternalRight {q : ℕ}
    (labels : Fin q → IncrementPair) (terminal : IncrementPair) :
    StoppedExternalBase (0, 0) labels → ℕ :=
  fun b ↦ unprimedOddTerminalExternalLocalTime
    labels terminal (b.1 + paperE1)

noncomputable def primedEvenTerminalExternalLocalTime {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair) : Site → ℕ :=
  fun x ↦ localTime
    (simpleRandomWalk (primedEvenReference first labels terminal))
    ((reconstructedPrimedTerminalStoppedPrefix first labels
      (zeroStoppedVector q) terminal).1 - 1) x

noncomputable def primedEvenTerminalExternalLeft {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair) :
    StoppedExternalBase (primedInitialBase first) labels → ℕ :=
  fun b ↦ primedEvenTerminalExternalLocalTime
    first labels terminal b.1

private theorem chessEven_terminalBase_iff
    (a : Site) (labels : List IncrementPair) :
    HLOZPairing.chessEven (terminalBase a labels) ↔
      HLOZPairing.chessEven a := by
  induction labels generalizing a with
  | nil => rfl
  | cons p labels ih =>
      simp only [terminalBase]
      rw [ih, chessEven_pairEndpoint_iff]

private theorem unprimedOdd_terminalMidpoint_not_chessEven {q : ℕ}
    (labels : Fin q → IncrementPair) (terminal : IncrementPair) :
    ¬ HLOZPairing.chessEven
      (stoppedTerminalBase labels + directionStep (terminal 0)) := by
  have hbase : HLOZPairing.chessEven (stoppedTerminalBase labels) := by
    unfold stoppedTerminalBase
    exact (chessEven_terminalBase_iff (0, 0) (List.ofFn labels)).mpr
      (by norm_num [HLOZPairing.chessEven])
  exact fun hmid ↦
    (chessEven_add_directionStep_iff
      (stoppedTerminalBase labels) (terminal 0)).mp hmid hbase

private theorem primedEven_terminalMidpoint_chessEven {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair) :
    HLOZPairing.chessEven
      (primedStoppedTerminalSite first labels +
        directionStep (terminal 0)) := by
  have hzero : HLOZPairing.chessEven (0, 0) := by
    norm_num [HLOZPairing.chessEven]
  have hstart : ¬ HLOZPairing.chessEven (primedInitialStart first) := by
    have h := chessEven_add_directionStep_iff (0, 0) first
    have hadd : (0, 0) + directionStep first =
        primedInitialStart first := by
      ext <;> simp [primedInitialStart]
    rw [hadd] at h
    exact fun hs ↦ h.mp hs hzero
  have hterminal : ¬ HLOZPairing.chessEven
      (primedStoppedTerminalSite first labels) := by
    unfold primedStoppedTerminalSite
    exact fun ht ↦ hstart
      ((chessEven_terminalBase_iff
        (primedInitialStart first) (List.ofFn labels)).mp ht)
  exact (chessEven_add_directionStep_iff
    (primedStoppedTerminalSite first labels) (terminal 0)).mpr hterminal

theorem unprimedOddTerminalExternalLeft_eq_stoppedExternalLeft {q : ℕ}
    (labels : Fin q → IncrementPair) (terminal : IncrementPair)
    (b : StoppedExternalBase (0, 0) labels) :
    unprimedOddTerminalExternalLocalTime labels terminal b.1 =
      stoppedExternalLeft (0, 0) labels b := by
  unfold unprimedOddTerminalExternalLocalTime unprimedOddReference
  rw [localTime_reconstructedOddStoppedPrefix_reduce]
  rw [localTime_reconstructedStoppedPrefix_base]
  have hne : stoppedTerminalBase labels + directionStep (terminal 0) ≠
      b.1 := by
    intro heq
    exact unprimedOdd_terminalMidpoint_not_chessEven labels terminal
      (heq ▸ stoppedExternalBase_chessEven labels b)
  simp [hne, stoppedPaperBlockSums, stoppedPaperBlockVector,
    zeroStoppedVector]

theorem primedEvenTerminalExternalRight_eq_primedStoppedExternalRight
    {q : ℕ} (first : Direction) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair)
    (b : StoppedExternalBase (primedInitialBase first) labels) :
    primedEvenTerminalExternalLocalTime
        first labels terminal (b.1 + paperE1) =
      primedStoppedExternalRight first labels b := by
  unfold primedEvenTerminalExternalLocalTime primedEvenReference
  rw [localTime_reconstructedPrimedTerminalStoppedPrefix_reduce]
  rw [localTime_reconstructedPrimedStoppedPrefix_partner]
  have hpartnerOdd : ¬ HLOZPairing.chessEven (b.1 + paperE1) :=
    not_chessEven_add_paperE1
      (primedStoppedExternalBase_chessEven first labels b)
  have hne : primedStoppedTerminalSite first labels +
      directionStep (terminal 0) ≠ b.1 + paperE1 := by
    intro heq
    exact hpartnerOdd
      (heq ▸ primedEven_terminalMidpoint_chessEven first labels terminal)
  simp [hne, stoppedPaperBlockSums, stoppedPaperBlockVector,
    zeroStoppedVector]

theorem localTime_reconstructedOddStoppedPrefix_base {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ)
    (terminal : IncrementPair)
    (b : StoppedExternalBase (0, 0) labels) :
    localTime
        (simpleRandomWalk
          (extendPrefix (reconstructedOddStoppedPrefix labels v terminal).2))
        ((reconstructedOddStoppedPrefix labels v terminal).1 - 1) b.1 =
      stoppedExternalLeft (0, 0) labels b +
        stoppedPaperBlockSums (0, 0) labels
          (stoppedPaperBlockVector (0, 0) labels v) b := by
  rw [localTime_reconstructedOddStoppedPrefix_reduce,
    HLOZStoppedMixedReconstruction.localTime_reconstructedStoppedPrefix_base]
  have hne : stoppedTerminalBase labels + directionStep (terminal 0) ≠
      b.1 := by
    intro heq
    exact unprimedOdd_terminalMidpoint_not_chessEven labels terminal
      (heq ▸ stoppedExternalBase_chessEven labels b)
  rw [if_neg hne, add_zero]

theorem localTime_reconstructedOddStoppedPrefix_partner {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ)
    (terminal : IncrementPair)
    (b : StoppedExternalBase (0, 0) labels) :
    localTime
        (simpleRandomWalk
          (extendPrefix (reconstructedOddStoppedPrefix labels v terminal).2))
        ((reconstructedOddStoppedPrefix labels v terminal).1 - 1)
          (b.1 + paperE1) =
      unprimedOddTerminalExternalRight labels terminal b +
        stoppedPaperBlockSums (0, 0) labels
          (stoppedPaperBlockVector (0, 0) labels v) b := by
  rw [localTime_reconstructedOddStoppedPrefix_reduce,
    HLOZStoppedMixedReconstruction.localTime_reconstructedStoppedPrefix_partner]
  unfold unprimedOddTerminalExternalRight
    unprimedOddTerminalExternalLocalTime unprimedOddReference
  rw [localTime_reconstructedOddStoppedPrefix_reduce,
    HLOZStoppedMixedReconstruction.localTime_reconstructedStoppedPrefix_partner]
  simp only [stoppedPaperBlockSums, stoppedPaperBlockVector,
    zeroStoppedVector, Pi.zero_apply, Finset.sum_const_zero, add_zero]
  omega

theorem localTime_reconstructedPrimedTerminalStoppedPrefix_base {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ) (terminal : IncrementPair)
    (b : StoppedExternalBase (primedInitialBase first) labels) :
    localTime
        (simpleRandomWalk (extendPrefix
          (reconstructedPrimedTerminalStoppedPrefix
            first labels v terminal).2))
        ((reconstructedPrimedTerminalStoppedPrefix
          first labels v terminal).1 - 1) b.1 =
      primedEvenTerminalExternalLeft first labels terminal b +
        stoppedPaperBlockSums (primedInitialBase first) labels
          (stoppedPaperBlockVector
            (primedInitialBase first) labels v) b := by
  rw [localTime_reconstructedPrimedTerminalStoppedPrefix_reduce,
    HLOZPrimedOddMixedReconstruction.localTime_reconstructedPrimedStoppedPrefix_base]
  unfold primedEvenTerminalExternalLeft
    primedEvenTerminalExternalLocalTime primedEvenReference
  rw [localTime_reconstructedPrimedTerminalStoppedPrefix_reduce,
    HLOZPrimedOddMixedReconstruction.localTime_reconstructedPrimedStoppedPrefix_base]
  simp only [stoppedPaperBlockSums, stoppedPaperBlockVector,
    zeroStoppedVector, Pi.zero_apply, Finset.sum_const_zero, add_zero]
  omega

theorem localTime_reconstructedPrimedTerminalStoppedPrefix_partner {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ) (terminal : IncrementPair)
    (b : StoppedExternalBase (primedInitialBase first) labels) :
    localTime
        (simpleRandomWalk (extendPrefix
          (reconstructedPrimedTerminalStoppedPrefix
            first labels v terminal).2))
        ((reconstructedPrimedTerminalStoppedPrefix
          first labels v terminal).1 - 1) (b.1 + paperE1) =
      primedStoppedExternalRight first labels b +
        stoppedPaperBlockSums (primedInitialBase first) labels
          (stoppedPaperBlockVector
            (primedInitialBase first) labels v) b := by
  rw [localTime_reconstructedPrimedTerminalStoppedPrefix_reduce,
    HLOZPrimedOddMixedReconstruction.localTime_reconstructedPrimedStoppedPrefix_partner]
  have hpartnerOdd : ¬ HLOZPairing.chessEven (b.1 + paperE1) :=
    not_chessEven_add_paperE1
      (primedStoppedExternalBase_chessEven first labels b)
  have hne : primedStoppedTerminalSite first labels +
      directionStep (terminal 0) ≠ b.1 + paperE1 := by
    intro heq
    exact hpartnerOdd
      (heq ▸ primedEven_terminalMidpoint_chessEven first labels terminal)
  rw [if_neg hne, add_zero]

theorem localTime_reconstructedOddStoppedPrefix_offBase {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ)
    (terminal : IncrementPair) (x : Site)
    (hx : x ∉ stoppedExternalBaseSet (0, 0) labels)
    (heven : HLOZPairing.chessEven x) :
    localTime
        (simpleRandomWalk
          (extendPrefix (reconstructedOddStoppedPrefix labels v terminal).2))
        ((reconstructedOddStoppedPrefix labels v terminal).1 - 1) x =
      unprimedOddTerminalExternalLocalTime labels terminal x := by
  rw [localTime_reconstructedOddStoppedPrefix_reduce,
    HLOZStoppedMixedReconstruction.localTime_reconstructedStoppedPrefix_offBase
      labels v x hx heven]
  unfold unprimedOddTerminalExternalLocalTime unprimedOddReference
  rw [localTime_reconstructedOddStoppedPrefix_reduce,
    HLOZStoppedMixedReconstruction.localTime_reconstructedStoppedPrefix_offBase
      labels (zeroStoppedVector q) x hx heven]

theorem localTime_reconstructedOddStoppedPrefix_offBase_partner {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ)
    (terminal : IncrementPair) (x : Site)
    (hx : x ∉ stoppedExternalBaseSet (0, 0) labels)
    (heven : HLOZPairing.chessEven x) :
    localTime
        (simpleRandomWalk
          (extendPrefix (reconstructedOddStoppedPrefix labels v terminal).2))
        ((reconstructedOddStoppedPrefix labels v terminal).1 - 1)
          (x + paperE1) =
      unprimedOddTerminalExternalLocalTime
        labels terminal (x + paperE1) := by
  rw [localTime_reconstructedOddStoppedPrefix_reduce,
    HLOZStoppedMixedReconstruction.localTime_reconstructedStoppedPrefix_offBase_partner
      labels v x hx heven]
  unfold unprimedOddTerminalExternalLocalTime unprimedOddReference
  rw [localTime_reconstructedOddStoppedPrefix_reduce,
    HLOZStoppedMixedReconstruction.localTime_reconstructedStoppedPrefix_offBase_partner
      labels (zeroStoppedVector q) x hx heven]

theorem localTime_reconstructedPrimedTerminalStoppedPrefix_offBase {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ) (terminal : IncrementPair) (x : Site)
    (hx : x ∉ stoppedExternalBaseSet (primedInitialBase first) labels)
    (heven : HLOZPairing.chessEven x) :
    localTime
        (simpleRandomWalk (extendPrefix
          (reconstructedPrimedTerminalStoppedPrefix
            first labels v terminal).2))
        ((reconstructedPrimedTerminalStoppedPrefix
          first labels v terminal).1 - 1) x =
      primedEvenTerminalExternalLocalTime first labels terminal x := by
  rw [localTime_reconstructedPrimedTerminalStoppedPrefix_reduce,
    HLOZPrimedOddMixedReconstruction.localTime_reconstructedPrimedStoppedPrefix_offBase
      first labels v x hx heven]
  unfold primedEvenTerminalExternalLocalTime primedEvenReference
  rw [localTime_reconstructedPrimedTerminalStoppedPrefix_reduce,
    HLOZPrimedOddMixedReconstruction.localTime_reconstructedPrimedStoppedPrefix_offBase
      first labels (zeroStoppedVector q) x hx heven]

theorem localTime_reconstructedPrimedTerminalStoppedPrefix_offBase_partner
    {q : ℕ} (first : Direction) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ) (terminal : IncrementPair) (x : Site)
    (hx : x ∉ stoppedExternalBaseSet (primedInitialBase first) labels)
    (heven : HLOZPairing.chessEven x) :
    localTime
        (simpleRandomWalk (extendPrefix
          (reconstructedPrimedTerminalStoppedPrefix
            first labels v terminal).2))
        ((reconstructedPrimedTerminalStoppedPrefix
          first labels v terminal).1 - 1) (x + paperE1) =
      primedEvenTerminalExternalLocalTime
        first labels terminal (x + paperE1) := by
  rw [localTime_reconstructedPrimedTerminalStoppedPrefix_reduce,
    HLOZPrimedOddMixedReconstruction.localTime_reconstructedPrimedStoppedPrefix_offBase_partner
      first labels v x hx heven]
  unfold primedEvenTerminalExternalLocalTime primedEvenReference
  rw [localTime_reconstructedPrimedTerminalStoppedPrefix_reduce,
    HLOZPrimedOddMixedReconstruction.localTime_reconstructedPrimedStoppedPrefix_offBase_partner
      first labels (zeroStoppedVector q) x hx heven]

def UnprimedOddOffBaseMixedCondition {q : ℕ}
    (labels : Fin q → IncrementPair) (terminal : IncrementPair)
    (m : ℕ) (C : Finset Site) : Prop :=
  ∀ x, HLOZPairing.chessEven x →
    x ∉ stoppedExternalBaseSet (0, 0) labels →
      if _hC : x ∈ C ∨ x + paperE1 ∈ C then
        max (unprimedOddTerminalExternalLocalTime labels terminal x)
            (unprimedOddTerminalExternalLocalTime
              labels terminal (x + paperE1)) = m ∧
          (unprimedOddTerminalExternalLocalTime labels terminal x = m ↔
            x ∈ C) ∧
          (unprimedOddTerminalExternalLocalTime
              labels terminal (x + paperE1) = m ↔ x + paperE1 ∈ C)
      else
        max (unprimedOddTerminalExternalLocalTime labels terminal x)
          (unprimedOddTerminalExternalLocalTime
            labels terminal (x + paperE1)) < m

def PrimedEvenOffBaseMixedCondition {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair) (m : ℕ) (C : Finset Site) : Prop :=
  ∀ x, HLOZPairing.chessEven x →
    x ∉ stoppedExternalBaseSet (primedInitialBase first) labels →
      if _hC : x ∈ C ∨ x + paperE1 ∈ C then
        max (primedEvenTerminalExternalLocalTime
              first labels terminal x)
            (primedEvenTerminalExternalLocalTime
              first labels terminal (x + paperE1)) = m ∧
          (primedEvenTerminalExternalLocalTime
              first labels terminal x = m ↔ x ∈ C) ∧
          (primedEvenTerminalExternalLocalTime
              first labels terminal (x + paperE1) = m ↔
            x + paperE1 ∈ C)
      else
        max (primedEvenTerminalExternalLocalTime
            first labels terminal x)
          (primedEvenTerminalExternalLocalTime
            first labels terminal (x + paperE1)) < m

theorem mixedX1DominoCondition_reconstructedOddStoppedPrefix_iff {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ)
    (terminal : IncrementPair) (m : ℕ) (C : Finset Site) :
    MixedX1DominoCondition
        (simpleRandomWalk
          (extendPrefix (reconstructedOddStoppedPrefix labels v terminal).2))
        ((reconstructedOddStoppedPrefix labels v terminal).1 - 1) m C ↔
      HLOZPairing.PairFree
          (HLOZPairing.XPair HLOZPairing.east) C ∧
        UnprimedOddOffBaseMixedCondition labels terminal m C ∧
        stoppedPaperBlockSums (0, 0) labels
            (stoppedPaperBlockVector (0, 0) labels v) ∈
          stoppedMixedBlockSumEvent (0, 0) labels m C
            (stoppedExternalLeft (0, 0) labels)
            (unprimedOddTerminalExternalRight labels terminal) := by
  constructor
  · rintro ⟨hfree, hmix⟩
    refine ⟨hfree, ?_, ?_⟩
    · intro x hxEven hxOff
      specialize hmix x hxEven
      rw [localTime_reconstructedOddStoppedPrefix_offBase
          labels v terminal x hxOff hxEven,
        localTime_reconstructedOddStoppedPrefix_offBase_partner
          labels v terminal x hxOff hxEven] at hmix
      exact hmix
    · intro b
      specialize hmix b.1 (stoppedExternalBase_chessEven labels b)
      rw [localTime_reconstructedOddStoppedPrefix_base labels v terminal b,
        localTime_reconstructedOddStoppedPrefix_partner
          labels v terminal b] at hmix
      exact hmix
  · rintro ⟨hfree, hoff, hblocks⟩
    refine ⟨hfree, ?_⟩
    intro x hxEven
    by_cases hxBase : x ∈ stoppedExternalBaseSet (0, 0) labels
    · let b : StoppedExternalBase (0, 0) labels := ⟨x, hxBase⟩
      have hb := hblocks b
      rw [localTime_reconstructedOddStoppedPrefix_base labels v terminal b,
        localTime_reconstructedOddStoppedPrefix_partner
          labels v terminal b]
      exact hb
    · have hx := hoff x hxEven hxBase
      rw [localTime_reconstructedOddStoppedPrefix_offBase
          labels v terminal x hxBase hxEven,
        localTime_reconstructedOddStoppedPrefix_offBase_partner
          labels v terminal x hxBase hxEven]
      exact hx

theorem mixedX1DominoCondition_reconstructedPrimedTerminalStoppedPrefix_iff
    {q : ℕ} (first : Direction) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ) (terminal : IncrementPair)
    (m : ℕ) (C : Finset Site) :
    MixedX1DominoCondition
        (simpleRandomWalk (extendPrefix
          (reconstructedPrimedTerminalStoppedPrefix
            first labels v terminal).2))
        ((reconstructedPrimedTerminalStoppedPrefix
          first labels v terminal).1 - 1) m C ↔
      HLOZPairing.PairFree
          (HLOZPairing.XPair HLOZPairing.east) C ∧
        PrimedEvenOffBaseMixedCondition first labels terminal m C ∧
        stoppedPaperBlockSums (primedInitialBase first) labels
            (stoppedPaperBlockVector
              (primedInitialBase first) labels v) ∈
          stoppedMixedBlockSumEvent (primedInitialBase first) labels m C
            (primedEvenTerminalExternalLeft first labels terminal)
            (primedStoppedExternalRight first labels) := by
  constructor
  · rintro ⟨hfree, hmix⟩
    refine ⟨hfree, ?_, ?_⟩
    · intro x hxEven hxOff
      specialize hmix x hxEven
      rw [localTime_reconstructedPrimedTerminalStoppedPrefix_offBase
          first labels v terminal x hxOff hxEven,
        localTime_reconstructedPrimedTerminalStoppedPrefix_offBase_partner
          first labels v terminal x hxOff hxEven] at hmix
      exact hmix
    · intro b
      specialize hmix b.1
        (primedStoppedExternalBase_chessEven first labels b)
      rw [localTime_reconstructedPrimedTerminalStoppedPrefix_base
          first labels v terminal b,
        localTime_reconstructedPrimedTerminalStoppedPrefix_partner
          first labels v terminal b] at hmix
      exact hmix
  · rintro ⟨hfree, hoff, hblocks⟩
    refine ⟨hfree, ?_⟩
    intro x hxEven
    by_cases hxBase :
        x ∈ stoppedExternalBaseSet (primedInitialBase first) labels
    · let b : StoppedExternalBase (primedInitialBase first) labels :=
        ⟨x, hxBase⟩
      have hb := hblocks b
      rw [localTime_reconstructedPrimedTerminalStoppedPrefix_base
          first labels v terminal b,
        localTime_reconstructedPrimedTerminalStoppedPrefix_partner
          first labels v terminal b]
      exact hb
    · have hx := hoff x hxEven hxBase
      rw [localTime_reconstructedPrimedTerminalStoppedPrefix_offBase
          first labels v terminal x hxBase hxEven,
        localTime_reconstructedPrimedTerminalStoppedPrefix_offBase_partner
          first labels v terminal x hxBase hxEven]
      exact hx

theorem unprimedOddSourceConstraint_eq_mixedBlockPreimage {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : UnprimedOddOffBaseMixedCondition labels terminal m C) :
    (unprimedOddSourceConstraint m k C labels terminal :
        Set (Fin (q + 1) → ℕ)) =
      (fun v ↦ stoppedPaperBlockSums (0, 0) labels
        (stoppedPaperBlockVector (0, 0) labels v)) ⁻¹'
        stoppedMixedBlockSumEvent (0, 0) labels m C
          (stoppedExternalLeft (0, 0) labels)
          (unprimedOddTerminalExternalRight labels terminal) := by
  ext v
  change v ∈ unprimedOddSourceConstraint m k C labels terminal ↔ _
  simp only [unprimedOddSourceConstraint, mixedPrefixConstraint,
    Finset.mem_filter]
  constructor
  · rintro ⟨_, hmixed⟩
    exact (mixedX1DominoCondition_reconstructedOddStoppedPrefix_iff
      labels v terminal m C).mp hmixed |>.2.2
  · intro hblocks
    refine ⟨mem_stoppedRunVectorBox_of_mem_mixedBlockSumEvent
      labels v m C _ _ hblocks, ?_⟩
    exact (mixedX1DominoCondition_reconstructedOddStoppedPrefix_iff
      labels v terminal m C).mpr ⟨hfree, hoff, hblocks⟩

theorem primedEvenSourceConstraint_eq_mixedBlockPreimage {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair) (terminal : IncrementPair)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : PrimedEvenOffBaseMixedCondition
      first labels terminal m C) :
    (primedEvenSourceConstraint m k C first labels terminal :
        Set (Fin (q + 1) → ℕ)) =
      (fun v ↦ stoppedPaperBlockSums (primedInitialBase first) labels
        (stoppedPaperBlockVector (primedInitialBase first) labels v)) ⁻¹'
        stoppedMixedBlockSumEvent (primedInitialBase first) labels m C
          (primedEvenTerminalExternalLeft first labels terminal)
          (primedStoppedExternalRight first labels) := by
  ext v
  change v ∈ primedEvenSourceConstraint m k C first labels terminal ↔ _
  simp only [primedEvenSourceConstraint, mixedPrefixConstraint,
    Finset.mem_filter]
  constructor
  · rintro ⟨_, hmixed⟩
    exact
      (mixedX1DominoCondition_reconstructedPrimedTerminalStoppedPrefix_iff
        first labels v terminal m C).mp hmixed |>.2.2
  · intro hblocks
    refine ⟨mem_stoppedRunVectorBox_of_mem_mixedBlockSumEvent_from
      (primedInitialBase first) labels v m C _ _ hblocks, ?_⟩
    exact
      (mixedX1DominoCondition_reconstructedPrimedTerminalStoppedPrefix_iff
        first labels v terminal m C).mpr ⟨hfree, hoff, hblocks⟩

theorem reconstructedOddStoppedPrefix_threshold_current {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ)
    (terminal : IncrementPair) :
    simpleRandomWalk
        (extendPrefix (reconstructedOddStoppedPrefix labels v terminal).2)
        ((reconstructedOddStoppedPrefix labels v terminal).1 - 1) =
      stoppedTerminalBase labels + directionStep (terminal 0) := by
  rw [unprimedOdd_threshold_eq]
  exact unprimedOdd_terminal_position labels v terminal

theorem reconstructedPrimedTerminalStoppedPrefix_threshold_current {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ) (terminal : IncrementPair) :
    simpleRandomWalk (extendPrefix
        (reconstructedPrimedTerminalStoppedPrefix
          first labels v terminal).2)
        ((reconstructedPrimedTerminalStoppedPrefix
          first labels v terminal).1 - 1) =
      primedStoppedTerminalSite first labels +
        directionStep (terminal 0) := by
  rw [primedEven_threshold_eq]
  exact primedEven_terminal_position first labels v terminal

theorem actualAdmissible_unprimedOddSourceConstraint_eq_mixedBlockPreimage
    {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair) (hm : 0 < m) (hcard : C.card = k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : UnprimedOddOffBaseMixedCondition labels terminal m C)
    (hterminal : stoppedTerminalBase labels + directionStep (terminal 0) ∈ C) :
    (actualAdmissibleOddStoppedVectors m k labels terminal
        (unprimedOddSourceConstraint m k C labels terminal) :
      Set (Fin (q + 1) → ℕ)) =
      (fun v ↦ stoppedPaperBlockSums (0, 0) labels
        (stoppedPaperBlockVector (0, 0) labels v)) ⁻¹'
        stoppedMixedBlockSumEvent (0, 0) labels m C
          (stoppedExternalLeft (0, 0) labels)
          (unprimedOddTerminalExternalRight labels terminal) := by
  ext v
  rw [← unprimedOddSourceConstraint_eq_mixedBlockPreimage
    m k C labels terminal hfree hoff]
  change v ∈ actualAdmissibleOddStoppedVectors m k labels terminal
      (unprimedOddSourceConstraint m k C labels terminal) ↔
    v ∈ unprimedOddSourceConstraint m k C labels terminal
  simp only [actualAdmissibleOddStoppedVectors, Finset.mem_filter]
  constructor
  · exact fun h ↦ h.1
  · intro hv
    refine ⟨hv, ?_⟩
    have hmixed : MixedX1DominoCondition
        (simpleRandomWalk
          (extendPrefix (reconstructedOddStoppedPrefix labels v terminal).2))
        ((reconstructedOddStoppedPrefix labels v terminal).1 - 1) m C := by
      apply (mixedX1DominoCondition_reconstructedOddStoppedPrefix_iff
        labels v terminal m C).mpr
      refine ⟨hfree, hoff, ?_⟩
      have heq := unprimedOddSourceConstraint_eq_mixedBlockPreimage
        m k C labels terminal hfree hoff
      have hvSet : v ∈
          (unprimedOddSourceConstraint m k C labels terminal :
            Set (Fin (q + 1) → ℕ)) := hv
      rw [heq] at hvSet
      exact hvSet
    have hcurrent : simpleRandomWalk
        (extendPrefix (reconstructedOddStoppedPrefix labels v terminal).2)
        ((reconstructedOddStoppedPrefix labels v terminal).1 - 1) ∈ C := by
      rw [reconstructedOddStoppedPrefix_threshold_current]
      exact hterminal
    exact firstKSitesReachLevel_eq_of_mixed_current_mem
      (simpleRandomWalk
        (extendPrefix (reconstructedOddStoppedPrefix labels v terminal).2))
      ((reconstructedOddStoppedPrefix labels v terminal).1 - 1)
      m k C hm hcard hmixed hcurrent

theorem actualAdmissible_primedEvenSourceConstraint_eq_mixedBlockPreimage
    {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair) (terminal : IncrementPair)
    (hm : 0 < m) (hcard : C.card = k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : PrimedEvenOffBaseMixedCondition
      first labels terminal m C)
    (hterminal : primedStoppedTerminalSite first labels +
      directionStep (terminal 0) ∈ C) :
    (actualAdmissiblePrimedTerminalVectors m k first labels terminal
        (primedEvenSourceConstraint m k C first labels terminal) :
      Set (Fin (q + 1) → ℕ)) =
      (fun v ↦ stoppedPaperBlockSums (primedInitialBase first) labels
        (stoppedPaperBlockVector (primedInitialBase first) labels v)) ⁻¹'
        stoppedMixedBlockSumEvent (primedInitialBase first) labels m C
          (primedEvenTerminalExternalLeft first labels terminal)
          (primedStoppedExternalRight first labels) := by
  ext v
  rw [← primedEvenSourceConstraint_eq_mixedBlockPreimage
    m k C first labels terminal hfree hoff]
  change v ∈ actualAdmissiblePrimedTerminalVectors m k first labels terminal
      (primedEvenSourceConstraint m k C first labels terminal) ↔
    v ∈ primedEvenSourceConstraint m k C first labels terminal
  simp only [actualAdmissiblePrimedTerminalVectors, Finset.mem_filter]
  constructor
  · exact fun h ↦ h.1
  · intro hv
    refine ⟨hv, ?_⟩
    have hmixed : MixedX1DominoCondition
        (simpleRandomWalk (extendPrefix
          (reconstructedPrimedTerminalStoppedPrefix
            first labels v terminal).2))
        ((reconstructedPrimedTerminalStoppedPrefix
          first labels v terminal).1 - 1) m C := by
      apply
        (mixedX1DominoCondition_reconstructedPrimedTerminalStoppedPrefix_iff
          first labels v terminal m C).mpr
      refine ⟨hfree, hoff, ?_⟩
      have heq := primedEvenSourceConstraint_eq_mixedBlockPreimage
        m k C first labels terminal hfree hoff
      have hvSet : v ∈
          (primedEvenSourceConstraint m k C first labels terminal :
            Set (Fin (q + 1) → ℕ)) := hv
      rw [heq] at hvSet
      exact hvSet
    have hcurrent : simpleRandomWalk (extendPrefix
        (reconstructedPrimedTerminalStoppedPrefix
          first labels v terminal).2)
        ((reconstructedPrimedTerminalStoppedPrefix
          first labels v terminal).1 - 1) ∈ C := by
      rw [reconstructedPrimedTerminalStoppedPrefix_threshold_current]
      exact hterminal
    exact firstKSitesReachLevel_eq_of_mixed_current_mem
      (simpleRandomWalk (extendPrefix
        (reconstructedPrimedTerminalStoppedPrefix
          first labels v terminal).2))
      ((reconstructedPrimedTerminalStoppedPrefix
        first labels v terminal).1 - 1)
      m k C hm hcard hmixed hcurrent

theorem unprimedOdd_sourceTieLeftWinner_StoppedEquation447Atom_map_law
    {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (terminal : IncrementPair) (hm : 0 < m) (hk : 0 < k)
    (hcard : C.card = k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : UnprimedOddOffBaseMixedCondition labels terminal m C)
    (hterminal : stoppedTerminalBase labels +
      directionStep (terminal 0) ∈ C)
    (candidateBases : Finset (StoppedExternalBase (0, 0) labels))
    (hne : (actualAdmissibleOddStoppedVectors m k labels terminal
      (unprimedOddSourceConstraint m k C labels terminal)).Nonempty) :
    (simpleRandomWalkLaw.restrict
        (simpleRandomWalk ''
          (actualOddStoppedVectorEvent m k labels terminal
              (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C))).map
        (fun s ↦
          (unprimedOddActiveFreePathLazy m k C labels terminal
              (unprimedOddTieLeftWinnerBases labels
                (unprimedOddTerminalExternalRight labels terminal)
                  candidateBases) s,
            unprimedOddActiveFreePathNext m k C labels terminal
              (unprimedOddTieLeftWinnerBases labels
                (unprimedOddTerminalExternalRight labels terminal)
                  candidateBases) s)) =
      simpleRandomWalkLaw
          (simpleRandomWalk ''
            (actualOddStoppedVectorEvent m k labels terminal
                (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C)) •
        ((sourceTruncatedProfileMeasure m
          (activeFreeStoppedShape (0, 0) labels C
            (unprimedOddTieLeftWinnerBases labels
              (unprimedOddTerminalExternalRight labels terminal)
                candidateBases))).prod directionLaw) := by
  exact unprimedOdd_tieLeftWinner_StoppedEquation447Atom_map_law
    m k C labels hnondist terminal hm hk hfree
      (unprimedOddTerminalExternalRight labels terminal) candidateBases
        (actualAdmissible_unprimedOddSourceConstraint_eq_mixedBlockPreimage
          m k C labels terminal hm hcard hfree hoff hterminal) hne

/-- Nonemptiness of the literal unprimed-odd terminal atom forces every
tie-left winner profile below the stopping level. -/
theorem unprimedOdd_tieLeftWinner_profile_lt_of_nonempty
    {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair) (hm : 0 < m) (hcard : C.card = k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : UnprimedOddOffBaseMixedCondition labels terminal m C)
    (hterminal : stoppedTerminalBase labels +
      directionStep (terminal 0) ∈ C)
    (hne : (actualAdmissibleOddStoppedVectors m k labels terminal
      (unprimedOddSourceConstraint m k C labels terminal)).Nonempty)
    (candidateBases : Finset (StoppedExternalBase (0, 0) labels)) :
    ∀ b : ActiveFreeStoppedBase (0, 0) labels C
        (unprimedOddTieLeftWinnerBases labels
          (unprimedOddTerminalExternalRight labels terminal) candidateBases),
      activeFreeStoppedShape (0, 0) labels C
        (unprimedOddTieLeftWinnerBases labels
          (unprimedOddTerminalExternalRight labels terminal) candidateBases) b < m := by
  intro b
  have hgrouped :=
    actualAdmissible_unprimedOddSourceConstraint_eq_mixedBlockPreimage
      m k C labels terminal hm hcard hfree hoff hterminal
  have hpos := mixedCoordinatePos_of_grouped_nonempty
    (0, 0) labels m C (stoppedExternalLeft (0, 0) labels)
      (unprimedOddTerminalExternalRight labels terminal)
      (actualAdmissibleOddStoppedVectors m k labels terminal
        (unprimedOddSourceConstraint m k C labels terminal))
      hgrouped hne b.1
  rw [stoppedMixedBlockValues_activeFree_eq_sourceBelowSet
    (0, 0) labels m C
    (unprimedOddTieLeftWinnerBases labels
      (unprimedOddTerminalExternalRight labels terminal) candidateBases)
    (stoppedExternalLeft (0, 0) labels)
    (unprimedOddTerminalExternalRight labels terminal) b] at hpos
  have hcap := cap_lt_of_negBin_sourceBelowSet_ne_zero _ _ _ hpos
  rw [unprimedOddTieLeftWinnerBases_cap_eq_shape labels C
    (unprimedOddTerminalExternalRight labels terminal) candidateBases b] at hcap
  exact hcap

theorem primedEven_sourceStrictRightWinner_StoppedEquation447Atom_map_law
    {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (terminal : IncrementPair) (hm : 0 < m) (hk : 0 < k)
    (hcard : C.card = k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : PrimedEvenOffBaseMixedCondition
      first labels terminal m C)
    (hterminal : primedStoppedTerminalSite first labels +
      directionStep (terminal 0) ∈ C)
    (candidateBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels))
    (hne : (actualAdmissiblePrimedTerminalVectors m k first labels terminal
      (primedEvenSourceConstraint m k C first labels terminal)).Nonempty) :
    (simpleRandomWalkLaw.restrict
        (simpleRandomWalk ''
          (actualPrimedTerminalVectorEvent m k first labels terminal
              (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C))).map
        (fun s ↦
          (primedEvenActiveFreePathLazy m k C first labels terminal
              (primedEvenStrictRightWinnerBases first labels
                (primedEvenTerminalExternalLeft first labels terminal)
                  candidateBases) s,
            primedEvenActiveFreePathNext m k C first labels terminal
              (primedEvenStrictRightWinnerBases first labels
                (primedEvenTerminalExternalLeft first labels terminal)
                  candidateBases) s)) =
      simpleRandomWalkLaw
          (simpleRandomWalk ''
            (actualPrimedTerminalVectorEvent m k first labels terminal
                (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C)) •
        ((sourceTruncatedProfileMeasure m
          (activeFreeStoppedShape (primedInitialBase first) labels C
            (primedEvenStrictRightWinnerBases first labels
              (primedEvenTerminalExternalLeft first labels terminal)
                candidateBases))).prod directionLaw) := by
  exact primedEven_strictRightWinner_StoppedEquation447Atom_map_law
    m k C first labels hnondist terminal hm hk hfree
      (primedEvenTerminalExternalLeft first labels terminal) candidateBases
        (actualAdmissible_primedEvenSourceConstraint_eq_mixedBlockPreimage
          m k C first labels terminal hm hcard hfree hoff hterminal) hne

/-- Nonemptiness of the literal primed-even terminal atom forces every
strict-right winner profile below the stopping level. -/
theorem primedEven_strictRightWinner_profile_lt_of_nonempty
    {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair) (terminal : IncrementPair)
    (hm : 0 < m) (hcard : C.card = k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : PrimedEvenOffBaseMixedCondition first labels terminal m C)
    (hterminal : primedStoppedTerminalSite first labels +
      directionStep (terminal 0) ∈ C)
    (hne : (actualAdmissiblePrimedTerminalVectors m k first labels terminal
      (primedEvenSourceConstraint m k C first labels terminal)).Nonempty)
    (candidateBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    ∀ b : ActiveFreeStoppedBase (primedInitialBase first) labels C
        (primedEvenStrictRightWinnerBases first labels
          (primedEvenTerminalExternalLeft first labels terminal) candidateBases),
      activeFreeStoppedShape (primedInitialBase first) labels C
        (primedEvenStrictRightWinnerBases first labels
          (primedEvenTerminalExternalLeft first labels terminal) candidateBases) b < m := by
  intro b
  have hgrouped :=
    actualAdmissible_primedEvenSourceConstraint_eq_mixedBlockPreimage
      m k C first labels terminal hm hcard hfree hoff hterminal
  have hpos := mixedCoordinatePos_of_grouped_nonempty
    (primedInitialBase first) labels m C
      (primedEvenTerminalExternalLeft first labels terminal)
      (primedStoppedExternalRight first labels)
      (actualAdmissiblePrimedTerminalVectors m k first labels terminal
        (primedEvenSourceConstraint m k C first labels terminal))
      hgrouped hne b.1
  rw [stoppedMixedBlockValues_activeFree_eq_sourceBelowSet
    (primedInitialBase first) labels m C
    (primedEvenStrictRightWinnerBases first labels
      (primedEvenTerminalExternalLeft first labels terminal) candidateBases)
    (primedEvenTerminalExternalLeft first labels terminal)
    (primedStoppedExternalRight first labels) b] at hpos
  have hcap := cap_lt_of_negBin_sourceBelowSet_ne_zero _ _ _ hpos
  rw [primedEvenStrictRightWinnerBases_cap_eq_shape first labels C
    (primedEvenTerminalExternalLeft first labels terminal) candidateBases b] at hcap
  exact hcap

end Erdos1166.HLOZTerminalParityWinner
