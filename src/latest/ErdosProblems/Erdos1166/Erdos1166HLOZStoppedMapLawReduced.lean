import ErdosProblems.Erdos1166.Erdos1166HLOZStoppedMapLaw
import ErdosProblems.Erdos1166.Erdos1166HLOZStoppedMixedReconstruction
import ErdosProblems.Erdos1166.Erdos1166HLOZStoppedShape

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

namespace Erdos1166.HLOZStoppedMapLawReduced

open HLOZDecomposition HLOZReconstruction HLOZActualStopped
  HLOZIncompleteStoppedBlocks HLOZMixedCreationBlocks
  HLOZStoppedSourcePartition HLOZStoppedMixedReconstruction
  HLOZStoppedMapLaw HLOZStoppedShape HLOZProp48Truncated

theorem unprimedEven_mixedCoordinatePos_of_nonempty {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hm : 0 < m) (hcard : C.card = k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : UnprimedEvenOffBaseMixedCondition labels m C)
    (hterminal : stoppedTerminalBase labels ∈ C)
    (hne : (actualAdmissibleStoppedVectors m k labels
      (unprimedEvenSourceConstraint m k C labels)).Nonempty) :
    ∀ b, HLOZUrn.negBinMeasure
      (Fintype.card (StoppedExternalIndex (0, 0) labels b))
        (stoppedMixedBlockValues (0, 0) labels m C
          (stoppedExternalLeft (0, 0) labels)
          (stoppedExternalRight (0, 0) labels) b : Set ℕ) ≠ 0 := by
  obtain ⟨v, hv⟩ := hne
  have hvSet : v ∈ (actualAdmissibleStoppedVectors m k labels
      (unprimedEvenSourceConstraint m k C labels) :
        Set (Fin (q + 1) → ℕ)) := hv
  rw [actualAdmissible_unprimedEvenSourceConstraint_eq_mixedBlockPreimage
    m k C labels hm hcard hfree hoff hterminal] at hvSet
  apply stoppedMixedCoordinatePos_of_event_nonempty (0, 0) labels m C
    (stoppedExternalLeft (0, 0) labels)
    (stoppedExternalRight (0, 0) labels)
  exact ⟨_, hvSet⟩

/-- Source-reduced unprimed-even stopped law: reconstruction, coordinate
positivity, and both stopped-history premises are discharged internally. -/
theorem unprimedEven_activeFreeWinning_capped_map_law_reduced {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (hm : 0 < m) (hk : 0 < k) (hcard : C.card = k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : UnprimedEvenOffBaseMixedCondition labels m C)
    (hterminal : stoppedTerminalBase labels ∈ C)
    (hne : (actualAdmissibleStoppedVectors m k labels
      (unprimedEvenSourceConstraint m k C labels)).Nonempty)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    HasLaw
      (fun ω ↦
        (restrictActiveFreeStoppedBase (0, 0) labels C activeBases
            (stoppedPaperBlockSums (0, 0) labels
              (stoppedPaperBlockVector (0, 0) labels
                (actualStoppedVector m k labels
                  (unprimedEvenSourceConstraint m k C labels) ω))),
          incrementShiftAfter (stoppedCreationTime m k) ω 0))
      ((sourceCappedProfileMeasure m
          (activeFreeStoppedShape (0, 0) labels C activeBases)
          (activeFreeCapProfile (0, 0) labels C activeBases
            (stoppedExternalLeft (0, 0) labels)
            (stoppedExternalRight (0, 0) labels))).prod directionLaw)
      incrementLaw[|
        actualStoppedVectorEvent m k labels (stoppedRunVectorBox q m) ∩
          stoppedSourceCondition m k C] := by
  apply unprimedEven_activeFreeWinning_capped_map_law
    m k C labels hnondist hm hk hfree
    (stoppedExternalLeft (0, 0) labels)
    (stoppedExternalRight (0, 0) labels) activeBases
  · exact actualAdmissible_unprimedEvenSourceConstraint_eq_mixedBlockPreimage
      m k C labels hm hcard hfree hoff hterminal
  · exact unprimedEven_mixedCoordinatePos_of_nonempty
      m k C labels hm hcard hfree hoff hterminal hne

/-! ### Unnormalized walk-path atom law -/

/-- The measurable increment statistic whose path-space lift supplies both
fields in an equation-(4.47) atom. -/
noncomputable def unprimedEvenActiveFreeStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    (ℕ → Direction) →
      (ActiveFreeStoppedBase (0, 0) labels C activeBases → ℕ) × Direction :=
  fun omega ↦
    (restrictActiveFreeStoppedBase (0, 0) labels C activeBases
        (stoppedPaperBlockSums (0, 0) labels
          (stoppedPaperBlockVector (0, 0) labels
            (actualStoppedVector m k labels
              (unprimedEvenSourceConstraint m k C labels) omega))),
      incrementShiftAfter (stoppedCreationTime m k) omega 0)

/-- Path-space lazy-vector field obtained from the injective walk encoding. -/
noncomputable def unprimedEvenActiveFreePathLazy {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    (ℕ → Site) → ActiveFreeStoppedBase (0, 0) labels C activeBases → ℕ :=
  fun s ↦ (liftIncrementStatisticToPath
    (unprimedEvenActiveFreeStatistic m k C labels activeBases) s).1

/-- Path-space fresh-direction field paired with the preceding lazy vector. -/
noncomputable def unprimedEvenActiveFreePathNext {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    (ℕ → Site) → Direction :=
  fun s ↦ (liftIncrementStatisticToPath
    (unprimedEvenActiveFreeStatistic m k C labels activeBases) s).2

theorem measurable_unprimedEvenActiveFreeStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    Measurable
      (unprimedEvenActiveFreeStatistic m k C labels activeBases) := by
  apply Measurable.prodMk
  · exact (measurable_restrictActiveFreeStoppedBase
      (0, 0) labels C activeBases).comp
        ((measurable_stoppedPaperBlockSums (0, 0) labels).comp
          ((measurable_stoppedPaperBlockVector (0, 0) labels).comp
            (measurable_actualStoppedVector m k labels hnondist
              (unprimedEvenSourceConstraint m k C labels))))
  · exact (measurable_pi_apply 0).comp
      (measurable_incrementShiftAfter (measurable_stoppedCreationTime m k))

theorem measurable_unprimedEvenActiveFreePathLazy {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    Measurable (unprimedEvenActiveFreePathLazy m k C labels activeBases) :=
  (measurable_fst.comp (measurable_liftIncrementStatisticToPath
    (measurable_unprimedEvenActiveFreeStatistic
      m k C labels hnondist activeBases)))

theorem measurable_unprimedEvenActiveFreePathNext {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    Measurable (unprimedEvenActiveFreePathNext m k C labels activeBases) :=
  (measurable_snd.comp (measurable_liftIncrementStatisticToPath
    (measurable_unprimedEvenActiveFreeStatistic
      m k C labels hnondist activeBases)))

/-- The reduced stopped law in the exact unnormalized path-space form used
by `StoppedEquation447Atom.map_law`, with the honest capped profile retained.
The path atom is the image of the literal stopped source atom. -/
theorem unprimedEven_activeFreeWinning_capped_path_map_law_reduced {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (hm : 0 < m) (hk : 0 < k) (hcard : C.card = k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : UnprimedEvenOffBaseMixedCondition labels m C)
    (hterminal : stoppedTerminalBase labels ∈ C)
    (hne : (actualAdmissibleStoppedVectors m k labels
      (unprimedEvenSourceConstraint m k C labels)).Nonempty)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    (simpleRandomWalkLaw.restrict
        (simpleRandomWalk ''
          (actualStoppedVectorEvent m k labels (stoppedRunVectorBox q m) ∩
            stoppedSourceCondition m k C))).map
        (liftIncrementStatisticToPath
          (unprimedEvenActiveFreeStatistic m k C labels activeBases)) =
      simpleRandomWalkLaw
          (simpleRandomWalk ''
            (actualStoppedVectorEvent m k labels (stoppedRunVectorBox q m) ∩
              stoppedSourceCondition m k C)) •
        ((sourceCappedProfileMeasure m
          (activeFreeStoppedShape (0, 0) labels C activeBases)
          (activeFreeCapProfile (0, 0) labels C activeBases
            (stoppedExternalLeft (0, 0) labels)
            (stoppedExternalRight (0, 0) labels))).prod directionLaw) := by
  have hEvent : MeasurableSet
      (actualStoppedVectorEvent m k labels (stoppedRunVectorBox q m) ∩
        stoppedSourceCondition m k C) := by
    rw [unprimedEven_source_partition m k C labels hm hk hfree]
    exact measurableSet_actualStoppedVectorEvent _ _ _ _
  apply liftIncrementStatistic_path_map_law hEvent
    (measurable_unprimedEvenActiveFreeStatistic
      m k C labels hnondist activeBases)
  exact unprimedEven_activeFreeWinning_capped_map_law_reduced
    m k C labels hnondist hm hk hcard hfree hoff hterminal hne activeBases

/-- Once the selected winning-member profile is the raw stopped-block shape,
the preceding source atom has the literal truncated product law required by
equation (4.47).  For unprimed atoms this premise is supplied by restricting
to left/even winners; right/odd winners belong to the primed decomposition. -/
theorem unprimedEven_activeFreeWinning_truncated_path_map_law_reduced {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (hm : 0 < m) (hk : 0 < k) (hcard : C.card = k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : UnprimedEvenOffBaseMixedCondition labels m C)
    (hterminal : stoppedTerminalBase labels ∈ C)
    (hne : (actualAdmissibleStoppedVectors m k labels
      (unprimedEvenSourceConstraint m k C labels)).Nonempty)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels))
    (hwinning : ∀ x,
      activeFreeCapProfile (0, 0) labels C activeBases
          (stoppedExternalLeft (0, 0) labels)
          (stoppedExternalRight (0, 0) labels) x =
        activeFreeStoppedShape (0, 0) labels C activeBases x) :
    (simpleRandomWalkLaw.restrict
        (simpleRandomWalk ''
          (actualStoppedVectorEvent m k labels (stoppedRunVectorBox q m) ∩
            stoppedSourceCondition m k C))).map
        (liftIncrementStatisticToPath
          (unprimedEvenActiveFreeStatistic m k C labels activeBases)) =
      simpleRandomWalkLaw
          (simpleRandomWalk ''
            (actualStoppedVectorEvent m k labels (stoppedRunVectorBox q m) ∩
              stoppedSourceCondition m k C)) •
        ((sourceTruncatedProfileMeasure m
          (activeFreeStoppedShape (0, 0) labels C activeBases)).prod
            directionLaw) := by
  rw [← sourceCappedProfileMeasure_eq_truncated m
    (activeFreeStoppedShape (0, 0) labels C activeBases)
    (activeFreeCapProfile (0, 0) labels C activeBases
      (stoppedExternalLeft (0, 0) labels)
      (stoppedExternalRight (0, 0) labels)) hwinning]
  exact unprimedEven_activeFreeWinning_capped_path_map_law_reduced
    m k C labels hnondist hm hk hcard hfree hoff hterminal hne activeBases

/-- Field-ready version of the preceding result.  Its left-hand statistic is
literally the pair of the `lazyVector` and `nextDirection` fields expected by
`StoppedEquation447Atom.map_law`; both measurability obligations are supplied
by the two preceding lemmas. -/
theorem unprimedEven_StoppedEquation447Atom_map_law {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (hm : 0 < m) (hk : 0 < k) (hcard : C.card = k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : UnprimedEvenOffBaseMixedCondition labels m C)
    (hterminal : stoppedTerminalBase labels ∈ C)
    (hne : (actualAdmissibleStoppedVectors m k labels
      (unprimedEvenSourceConstraint m k C labels)).Nonempty)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels))
    (hwinning : ∀ x,
      activeFreeCapProfile (0, 0) labels C activeBases
          (stoppedExternalLeft (0, 0) labels)
          (stoppedExternalRight (0, 0) labels) x =
        activeFreeStoppedShape (0, 0) labels C activeBases x) :
    (simpleRandomWalkLaw.restrict
        (simpleRandomWalk ''
          (actualStoppedVectorEvent m k labels (stoppedRunVectorBox q m) ∩
            stoppedSourceCondition m k C))).map
        (fun s ↦
          (unprimedEvenActiveFreePathLazy m k C labels activeBases s,
            unprimedEvenActiveFreePathNext m k C labels activeBases s)) =
      simpleRandomWalkLaw
          (simpleRandomWalk ''
            (actualStoppedVectorEvent m k labels (stoppedRunVectorBox q m) ∩
              stoppedSourceCondition m k C)) •
        ((sourceTruncatedProfileMeasure m
          (activeFreeStoppedShape (0, 0) labels C activeBases)).prod
            directionLaw) := by
  simpa only [unprimedEvenActiveFreePathLazy,
    unprimedEvenActiveFreePathNext, Prod.eta] using
      unprimedEven_activeFreeWinning_truncated_path_map_law_reduced
        m k C labels hnondist hm hk hcard hfree hoff hterminal hne
          activeBases hwinning

/-! ### Canonical unprimed left/even winners -/

/-- Filter a source candidate set to the bases whose even (left) member has
the larger fixed external profile.  Right/odd winners are intentionally left
for the primed decomposition. -/
noncomputable def unprimedEvenLeftWinnerBases {q : ℕ}
    (labels : Fin q → IncrementPair)
    (candidateBases : Finset (StoppedExternalBase (0, 0) labels)) :
    Finset (StoppedExternalBase (0, 0) labels) :=
  candidateBases.filter fun b ↦
    stoppedExternalRight (0, 0) labels b ≤
      stoppedExternalLeft (0, 0) labels b

theorem unprimedEvenLeftWinnerBases_left {q : ℕ}
    (labels : Fin q → IncrementPair)
    (candidateBases : Finset (StoppedExternalBase (0, 0) labels))
    (b : ActiveFreeStoppedBase (0, 0) labels C
      (unprimedEvenLeftWinnerBases labels candidateBases)) :
    stoppedExternalRight (0, 0) labels b.1 ≤
      stoppedExternalLeft (0, 0) labels b.1 := by
  exact (Finset.mem_filter.mp b.2.1).2

/-- Nonemptiness of the literal mixed stopped atom already implies the
strict profile bound on every active left-winner coordinate. -/
theorem unprimedEven_leftWinner_profile_lt_of_nonempty {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hm : 0 < m) (hcard : C.card = k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : UnprimedEvenOffBaseMixedCondition labels m C)
    (hterminal : stoppedTerminalBase labels ∈ C)
    (hne : (actualAdmissibleStoppedVectors m k labels
      (unprimedEvenSourceConstraint m k C labels)).Nonempty)
    (candidateBases : Finset (StoppedExternalBase (0, 0) labels)) :
    ∀ b : ActiveFreeStoppedBase (0, 0) labels C
        (unprimedEvenLeftWinnerBases labels candidateBases),
      activeFreeStoppedShape (0, 0) labels C
        (unprimedEvenLeftWinnerBases labels candidateBases) b < m := by
  intro b
  have hpos := unprimedEven_mixedCoordinatePos_of_nonempty
    m k C labels hm hcard hfree hoff hterminal hne b.1
  rw [stoppedMixedBlockValues_activeFree_eq_sourceBelowSet
    (0, 0) labels m C (unprimedEvenLeftWinnerBases labels candidateBases)
    (stoppedExternalLeft (0, 0) labels)
    (stoppedExternalRight (0, 0) labels) b] at hpos
  have hcap := cap_lt_of_negBin_sourceBelowSet_ne_zero _ _ _ hpos
  rw [unprimedEven_activeFreeCap_eq_shape_of_leftWinner labels C
    (unprimedEvenLeftWinnerBases labels candidateBases) b
    (unprimedEvenLeftWinnerBases_left labels candidateBases b)] at hcap
  exact hcap

/-- Fully source-facing equation-(4.47) map law for the unprimed left/even
winners.  The cap/shape premise has disappeared: it follows from the exact
stopped-fiber cardinality theorem and the defining winner filter. -/
theorem unprimedEven_leftWinner_StoppedEquation447Atom_map_law {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (hm : 0 < m) (hk : 0 < k) (hcard : C.card = k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : UnprimedEvenOffBaseMixedCondition labels m C)
    (hterminal : stoppedTerminalBase labels ∈ C)
    (hne : (actualAdmissibleStoppedVectors m k labels
      (unprimedEvenSourceConstraint m k C labels)).Nonempty)
    (candidateBases : Finset (StoppedExternalBase (0, 0) labels)) :
    (simpleRandomWalkLaw.restrict
        (simpleRandomWalk ''
          (actualStoppedVectorEvent m k labels (stoppedRunVectorBox q m) ∩
            stoppedSourceCondition m k C))).map
        (fun s ↦
          (unprimedEvenActiveFreePathLazy m k C labels
              (unprimedEvenLeftWinnerBases labels candidateBases) s,
            unprimedEvenActiveFreePathNext m k C labels
              (unprimedEvenLeftWinnerBases labels candidateBases) s)) =
      simpleRandomWalkLaw
          (simpleRandomWalk ''
            (actualStoppedVectorEvent m k labels (stoppedRunVectorBox q m) ∩
              stoppedSourceCondition m k C)) •
        ((sourceTruncatedProfileMeasure m
          (activeFreeStoppedShape (0, 0) labels C
            (unprimedEvenLeftWinnerBases labels candidateBases))).prod
              directionLaw) := by
  apply unprimedEven_StoppedEquation447Atom_map_law
    m k C labels hnondist hm hk hcard hfree hoff hterminal hne
      (unprimedEvenLeftWinnerBases labels candidateBases)
  intro b
  exact unprimedEven_activeFreeCap_eq_shape_of_leftWinner
    labels C (unprimedEvenLeftWinnerBases labels candidateBases) b
      (unprimedEvenLeftWinnerBases_left labels candidateBases b)

end Erdos1166.HLOZStoppedMapLawReduced
