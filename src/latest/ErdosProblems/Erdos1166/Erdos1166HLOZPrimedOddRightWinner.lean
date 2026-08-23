import ErdosProblems.Erdos1166.Erdos1166HLOZPrimedOddMixedReconstruction
import ErdosProblems.Erdos1166.Erdos1166HLOZStoppedShape

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

namespace Erdos1166.HLOZPrimedOddRightWinner

open HLOZDecomposition HLOZReconstruction HLOZActualStopped
  HLOZPrimedStopped HLOZIncompleteStoppedBlocks HLOZMixedCreationBlocks
  HLOZStoppedSourcePartition HLOZStoppedMixedReconstruction
  HLOZStoppedMapLaw HLOZProp48Truncated HLOZStoppedShape
  HLOZPrimedOddMixedReconstruction

theorem count_primedExternalPath_partner_eq_count_stoppedExternalBasesFrom
    (a x : Site) (labels : List IncrementPair)
    (ha : HLOZPairing.chessEven (primedPairBase a))
    (hx : HLOZPairing.chessEven x) :
    List.count (x + paperE1)
        (a :: reconstructExternalTail a labels) =
      List.count x
        (stoppedExternalBasesFrom (primedPairBase a) labels) := by
  induction labels generalizing a with
  | nil =>
      have heq : x + paperE1 = a ↔ primedPairBase a = x := by
        constructor
        · intro h
          apply add_paperE1_injective
          simpa [primedPairBase_add_paperE1] using h.symm
        · intro h
          rw [← h, primedPairBase_add_paperE1]
      have heq' : a = x + paperE1 ↔ primedPairBase a = x := by
        rw [eq_comm]
        exact heq
      simp only [reconstructExternalTail, stoppedExternalBasesFrom,
        List.count_cons, List.count_nil, beq_iff_eq]
      rw [if_congr heq' rfl rfl]
  | cons p labels ih =>
      let mid := a + directionStep (p 0)
      let endpoint := pairEndpoint a p
      have haOdd : ¬ HLOZPairing.chessEven a := by
        rw [← primedPairBase_add_paperE1 a]
        exact not_chessEven_add_paperE1 ha
      have hmidEven : HLOZPairing.chessEven mid := by
        exact (chessEven_add_directionStep_iff a (p 0)).mpr haOdd
      have htargetOdd : ¬ HLOZPairing.chessEven (x + paperE1) :=
        not_chessEven_add_paperE1 hx
      have hmidNe : x + paperE1 ≠ mid := by
        intro h
        exact htargetOdd (h ▸ hmidEven)
      have hnext : HLOZPairing.chessEven (primedPairBase endpoint) := by
        rw [primedPairBase_pairEndpoint]
        exact (chessEven_pairEndpoint_iff (primedPairBase a) p).mpr ha
      have hih := ih endpoint hnext
      have heq : x + paperE1 = a ↔ primedPairBase a = x := by
        constructor
        · intro h
          apply add_paperE1_injective
          simpa [primedPairBase_add_paperE1] using h.symm
        · intro h
          rw [← h, primedPairBase_add_paperE1]
      have hmidNe' : mid ≠ x + paperE1 := fun h ↦ hmidNe h.symm
      have heq' : a = x + paperE1 ↔ primedPairBase a = x := by
        rw [eq_comm]
        exact heq
      simp only [reconstructExternalTail, stoppedExternalBasesFrom,
        List.count_cons, beq_iff_eq] at hih ⊢
      rw [primedPairBase_pairEndpoint] at hih
      rw [if_neg hmidNe', if_congr heq' rfl rfl]
      rw [hih]
      omega

theorem card_stoppedExternalIndex_eq_primedStoppedExternalRight {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (b : StoppedExternalBase (primedInitialBase first) labels) :
    Fintype.card
        (StoppedExternalIndex (primedInitialBase first) labels b) =
      primedStoppedExternalRight first labels b := by
  rw [card_stoppedExternalIndex_eq_count]
  unfold primedStoppedExternalRight primedStoppedExternalLocalTimeFrom
  have hbEven := primedStoppedExternalBase_chessEven first labels b
  have hpartnerOdd : ¬ HLOZPairing.chessEven (b.1 + paperE1) :=
    not_chessEven_add_paperE1 hbEven
  have hzeroEven : HLOZPairing.chessEven (0, 0) := by
    norm_num [HLOZPairing.chessEven]
  have hne : b.1 + paperE1 ≠ (0, 0) := by
    intro h
    exact hpartnerOdd (h ▸ hzeroEven)
  rw [List.count_cons]
  simp only [beq_iff_eq]
  rw [if_neg (fun h ↦ hne h.symm), add_zero]
  change List.count b.1
      (stoppedExternalBasesFrom (primedPairBase (primedInitialStart first))
        (List.ofFn labels)) =
    List.count (b.1 + paperE1)
      (primedInitialStart first ::
        reconstructExternalTail (primedInitialStart first) (List.ofFn labels))
  exact (count_primedExternalPath_partner_eq_count_stoppedExternalBasesFrom
    (primedInitialStart first) b.1 (List.ofFn labels)
    (primedInitialBase_chessEven first) hbEven).symm

noncomputable def primedOddRightCapBases {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (candidateBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    Finset (StoppedExternalBase (primedInitialBase first) labels) :=
  candidateBases.filter fun b ↦
    primedStoppedExternalLeft first labels b ≤
      primedStoppedExternalRight first labels b

theorem primedOddRightCapBases_right {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (candidateBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels))
    (b : ActiveFreeStoppedBase (primedInitialBase first) labels C
      (primedOddRightCapBases first labels candidateBases)) :
    primedStoppedExternalLeft first labels b.1 ≤
      primedStoppedExternalRight first labels b.1 := by
  exact (Finset.mem_filter.mp b.2.1).2

theorem primedOdd_activeFreeCap_eq_shape_of_rightWinner {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (C : Finset Site)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels))
    (b : ActiveFreeStoppedBase (primedInitialBase first) labels C activeBases)
    (hwin : primedStoppedExternalLeft first labels b.1 ≤
      primedStoppedExternalRight first labels b.1) :
    activeFreeCapProfile (primedInitialBase first) labels C activeBases
        (primedStoppedExternalLeft first labels)
        (primedStoppedExternalRight first labels) b =
      activeFreeStoppedShape (primedInitialBase first) labels C
        activeBases b := by
  unfold activeFreeCapProfile activeFreeStoppedShape
  rw [max_eq_right hwin]
  exact (card_stoppedExternalIndex_eq_primedStoppedExternalRight
    first labels b.1).symm

theorem primedOddRightCapBases_cap_eq_shape {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (C : Finset Site)
    (candidateBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels))
    (b : ActiveFreeStoppedBase (primedInitialBase first) labels C
      (primedOddRightCapBases first labels candidateBases)) :
    activeFreeCapProfile (primedInitialBase first) labels C
        (primedOddRightCapBases first labels candidateBases)
        (primedStoppedExternalLeft first labels)
        (primedStoppedExternalRight first labels) b =
      activeFreeStoppedShape (primedInitialBase first) labels C
        (primedOddRightCapBases first labels candidateBases) b := by
  exact primedOdd_activeFreeCap_eq_shape_of_rightWinner
    first labels C (primedOddRightCapBases first labels candidateBases) b
      (primedOddRightCapBases_right first labels candidateBases b)

theorem primedOdd_mixedCoordinatePos_of_nonempty {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hm : 0 < m) (hcard : C.card = k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : PrimedOddOffBaseMixedCondition first labels m C)
    (hterminal : primedStoppedTerminalSite first labels ∈ C)
    (hne : (actualAdmissiblePrimedStoppedVectors m k first labels
      (primedOddSourceConstraint m k C first labels)).Nonempty) :
    ∀ b, HLOZUrn.negBinMeasure
      (Fintype.card
        (StoppedExternalIndex (primedInitialBase first) labels b))
        (stoppedMixedBlockValues (primedInitialBase first) labels m C
          (primedStoppedExternalLeft first labels)
          (primedStoppedExternalRight first labels) b : Set ℕ) ≠ 0 := by
  obtain ⟨v, hv⟩ := hne
  have hvSet : v ∈
      (actualAdmissiblePrimedStoppedVectors m k first labels
        (primedOddSourceConstraint m k C first labels) :
          Set (Fin (q + 1) → ℕ)) := hv
  rw [actualAdmissible_primedOddSourceConstraint_eq_mixedBlockPreimage
    m k C first labels hm hcard hfree hoff hterminal] at hvSet
  apply stoppedMixedCoordinatePos_of_event_nonempty
    (primedInitialBase first) labels m C
    (primedStoppedExternalLeft first labels)
    (primedStoppedExternalRight first labels)
  exact ⟨_, hvSet⟩

theorem primedOdd_activeFreeWinning_capped_map_law_reduced {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (hm : 0 < m) (hk : 0 < k) (hcard : C.card = k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : PrimedOddOffBaseMixedCondition first labels m C)
    (hterminal : primedStoppedTerminalSite first labels ∈ C)
    (hne : (actualAdmissiblePrimedStoppedVectors m k first labels
      (primedOddSourceConstraint m k C first labels)).Nonempty)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    HasLaw
      (fun ω ↦
        (restrictActiveFreeStoppedBase (primedInitialBase first) labels C
            activeBases
            (stoppedPaperBlockSums (primedInitialBase first) labels
              (stoppedPaperBlockVector (primedInitialBase first) labels
                (actualPrimedStoppedVector m k first labels
                  (primedOddSourceConstraint m k C first labels) ω))),
          incrementShiftAfter (stoppedCreationTime m k) ω 0))
      ((sourceCappedProfileMeasure m
          (activeFreeStoppedShape (primedInitialBase first) labels C
            activeBases)
          (activeFreeCapProfile (primedInitialBase first) labels C
            activeBases (primedStoppedExternalLeft first labels)
              (primedStoppedExternalRight first labels))).prod directionLaw)
      incrementLaw[|
        actualPrimedStoppedVectorEvent m k first labels
            (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C] := by
  apply primedOdd_activeFreeWinning_capped_map_law
    m k C first labels hnondist hm hk hfree
    (primedStoppedExternalLeft first labels)
    (primedStoppedExternalRight first labels) activeBases
  · exact actualAdmissible_primedOddSourceConstraint_eq_mixedBlockPreimage
      m k C first labels hm hcard hfree hoff hterminal
  · exact primedOdd_mixedCoordinatePos_of_nonempty
      m k C first labels hm hcard hfree hoff hterminal hne

noncomputable def primedOddActiveFreeStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    (ℕ → Direction) →
      (ActiveFreeStoppedBase (primedInitialBase first) labels C activeBases →
        ℕ) × Direction :=
  fun ω ↦
    (restrictActiveFreeStoppedBase (primedInitialBase first) labels C
        activeBases
        (stoppedPaperBlockSums (primedInitialBase first) labels
          (stoppedPaperBlockVector (primedInitialBase first) labels
            (actualPrimedStoppedVector m k first labels
              (primedOddSourceConstraint m k C first labels) ω))),
      incrementShiftAfter (stoppedCreationTime m k) ω 0)

noncomputable def primedOddActiveFreePathLazy {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    (ℕ → Site) →
      ActiveFreeStoppedBase (primedInitialBase first) labels C activeBases →
        ℕ :=
  fun s ↦ (liftIncrementStatisticToPath
    (primedOddActiveFreeStatistic m k C first labels activeBases) s).1

noncomputable def primedOddActiveFreePathNext {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    (ℕ → Site) → Direction :=
  fun s ↦ (liftIncrementStatisticToPath
    (primedOddActiveFreeStatistic m k C first labels activeBases) s).2

theorem measurable_primedOddActiveFreeStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    Measurable
      (primedOddActiveFreeStatistic m k C first labels activeBases) := by
  apply Measurable.prodMk
  · exact (measurable_restrictActiveFreeStoppedBase
      (primedInitialBase first) labels C activeBases).comp
        ((measurable_stoppedPaperBlockSums
          (primedInitialBase first) labels).comp
          ((measurable_stoppedPaperBlockVector
            (primedInitialBase first) labels).comp
            (measurable_actualPrimedStoppedVector
              m k first labels hnondist
                (primedOddSourceConstraint m k C first labels))))
  · exact (measurable_pi_apply 0).comp
      (measurable_incrementShiftAfter (measurable_stoppedCreationTime m k))

theorem measurable_primedOddActiveFreePathLazy {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    Measurable
      (primedOddActiveFreePathLazy m k C first labels activeBases) :=
  measurable_fst.comp (measurable_liftIncrementStatisticToPath
    (measurable_primedOddActiveFreeStatistic
      m k C first labels hnondist activeBases))

theorem measurable_primedOddActiveFreePathNext {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    Measurable
      (primedOddActiveFreePathNext m k C first labels activeBases) :=
  measurable_snd.comp (measurable_liftIncrementStatisticToPath
    (measurable_primedOddActiveFreeStatistic
      m k C first labels hnondist activeBases))

theorem primedOdd_activeFreeWinning_capped_path_map_law_reduced {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (hm : 0 < m) (hk : 0 < k) (hcard : C.card = k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : PrimedOddOffBaseMixedCondition first labels m C)
    (hterminal : primedStoppedTerminalSite first labels ∈ C)
    (hne : (actualAdmissiblePrimedStoppedVectors m k first labels
      (primedOddSourceConstraint m k C first labels)).Nonempty)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    (simpleRandomWalkLaw.restrict
        (simpleRandomWalk ''
          (actualPrimedStoppedVectorEvent m k first labels
              (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C))).map
        (liftIncrementStatisticToPath
          (primedOddActiveFreeStatistic m k C first labels activeBases)) =
      simpleRandomWalkLaw
          (simpleRandomWalk ''
            (actualPrimedStoppedVectorEvent m k first labels
                (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C)) •
        ((sourceCappedProfileMeasure m
          (activeFreeStoppedShape (primedInitialBase first) labels C
            activeBases)
          (activeFreeCapProfile (primedInitialBase first) labels C activeBases
            (primedStoppedExternalLeft first labels)
            (primedStoppedExternalRight first labels))).prod directionLaw) := by
  have hEvent : MeasurableSet
      (actualPrimedStoppedVectorEvent m k first labels
          (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C) := by
    rw [primedOdd_source_partition m k C first labels hm hk hfree]
    unfold actualPrimedStoppedVectorEvent
    exact MeasurableSet.iUnion fun v ↦ MeasurableSet.iUnion fun _ ↦
      measurableSet_stoppedPrefixAtom
        (reconstructedPrimedStoppedPrefix first labels v)
  apply liftIncrementStatistic_path_map_law hEvent
    (measurable_primedOddActiveFreeStatistic
      m k C first labels hnondist activeBases)
  exact primedOdd_activeFreeWinning_capped_map_law_reduced
    m k C first labels hnondist hm hk hcard hfree hoff hterminal hne
      activeBases

theorem primedOdd_activeFreeWinning_truncated_path_map_law_reduced {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (hm : 0 < m) (hk : 0 < k) (hcard : C.card = k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : PrimedOddOffBaseMixedCondition first labels m C)
    (hterminal : primedStoppedTerminalSite first labels ∈ C)
    (hne : (actualAdmissiblePrimedStoppedVectors m k first labels
      (primedOddSourceConstraint m k C first labels)).Nonempty)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels))
    (hwinning : ∀ x,
      activeFreeCapProfile (primedInitialBase first) labels C activeBases
          (primedStoppedExternalLeft first labels)
          (primedStoppedExternalRight first labels) x =
        activeFreeStoppedShape (primedInitialBase first) labels C
          activeBases x) :
    (simpleRandomWalkLaw.restrict
        (simpleRandomWalk ''
          (actualPrimedStoppedVectorEvent m k first labels
              (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C))).map
        (liftIncrementStatisticToPath
          (primedOddActiveFreeStatistic m k C first labels activeBases)) =
      simpleRandomWalkLaw
          (simpleRandomWalk ''
            (actualPrimedStoppedVectorEvent m k first labels
                (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C)) •
        ((sourceTruncatedProfileMeasure m
          (activeFreeStoppedShape (primedInitialBase first) labels C
            activeBases)).prod directionLaw) := by
  rw [← sourceCappedProfileMeasure_eq_truncated m
    (activeFreeStoppedShape (primedInitialBase first) labels C activeBases)
    (activeFreeCapProfile (primedInitialBase first) labels C activeBases
      (primedStoppedExternalLeft first labels)
      (primedStoppedExternalRight first labels)) hwinning]
  exact primedOdd_activeFreeWinning_capped_path_map_law_reduced
    m k C first labels hnondist hm hk hcard hfree hoff hterminal hne
      activeBases

theorem primedOdd_StoppedEquation447Atom_map_law {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (hm : 0 < m) (hk : 0 < k) (hcard : C.card = k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : PrimedOddOffBaseMixedCondition first labels m C)
    (hterminal : primedStoppedTerminalSite first labels ∈ C)
    (hne : (actualAdmissiblePrimedStoppedVectors m k first labels
      (primedOddSourceConstraint m k C first labels)).Nonempty)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels))
    (hwinning : ∀ x,
      activeFreeCapProfile (primedInitialBase first) labels C activeBases
          (primedStoppedExternalLeft first labels)
          (primedStoppedExternalRight first labels) x =
        activeFreeStoppedShape (primedInitialBase first) labels C
          activeBases x) :
    (simpleRandomWalkLaw.restrict
        (simpleRandomWalk ''
          (actualPrimedStoppedVectorEvent m k first labels
              (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C))).map
        (fun s ↦
          (primedOddActiveFreePathLazy m k C first labels activeBases s,
            primedOddActiveFreePathNext m k C first labels activeBases s)) =
      simpleRandomWalkLaw
          (simpleRandomWalk ''
            (actualPrimedStoppedVectorEvent m k first labels
                (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C)) •
        ((sourceTruncatedProfileMeasure m
          (activeFreeStoppedShape (primedInitialBase first) labels C
            activeBases)).prod directionLaw) := by
  simpa only [primedOddActiveFreePathLazy,
    primedOddActiveFreePathNext, Prod.eta] using
      primedOdd_activeFreeWinning_truncated_path_map_law_reduced
        m k C first labels hnondist hm hk hcard hfree hoff hterminal hne
          activeBases hwinning

theorem primedOdd_rightWinner_StoppedEquation447Atom_map_law {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (hm : 0 < m) (hk : 0 < k) (hcard : C.card = k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : PrimedOddOffBaseMixedCondition first labels m C)
    (hterminal : primedStoppedTerminalSite first labels ∈ C)
    (hne : (actualAdmissiblePrimedStoppedVectors m k first labels
      (primedOddSourceConstraint m k C first labels)).Nonempty)
    (candidateBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    (simpleRandomWalkLaw.restrict
        (simpleRandomWalk ''
          (actualPrimedStoppedVectorEvent m k first labels
              (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C))).map
        (fun s ↦
          (primedOddActiveFreePathLazy m k C first labels
              (primedOddRightCapBases first labels candidateBases) s,
            primedOddActiveFreePathNext m k C first labels
              (primedOddRightCapBases first labels candidateBases) s)) =
      simpleRandomWalkLaw
          (simpleRandomWalk ''
            (actualPrimedStoppedVectorEvent m k first labels
                (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C)) •
        ((sourceTruncatedProfileMeasure m
          (activeFreeStoppedShape (primedInitialBase first) labels C
            (primedOddRightCapBases first labels candidateBases))).prod
              directionLaw) := by
  apply primedOdd_StoppedEquation447Atom_map_law
    m k C first labels hnondist hm hk hcard hfree hoff hterminal hne
      (primedOddRightCapBases first labels candidateBases)
  intro b
  exact primedOddRightCapBases_cap_eq_shape
    first labels C candidateBases b

/-! ### Honest tie-left winner split

The inclusive right-cap filter above is convenient for the cap/shape
identity.  For candidate-event decompositions we resolve ties to the left,
matching `activeFreeWinningSite`: left winners satisfy `right ≤ left`, while
right winners satisfy the strict inequality `left < right`. -/

noncomputable def primedOddLeftWinnerBases {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (candidateBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    Finset (StoppedExternalBase (primedInitialBase first) labels) :=
  candidateBases.filter fun b ↦
    primedStoppedExternalRight first labels b ≤
      primedStoppedExternalLeft first labels b

noncomputable def primedOddStrictRightWinnerBases {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (candidateBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    Finset (StoppedExternalBase (primedInitialBase first) labels) :=
  candidateBases.filter fun b ↦
    primedStoppedExternalLeft first labels b <
      primedStoppedExternalRight first labels b

theorem primedOddWinnerBases_disjoint {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (candidateBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    Disjoint (primedOddLeftWinnerBases first labels candidateBases)
      (primedOddStrictRightWinnerBases first labels candidateBases) := by
  classical
  rw [Finset.disjoint_left]
  intro b hleft hright
  have hl := (Finset.mem_filter.mp hleft).2
  have hr := (Finset.mem_filter.mp hright).2
  omega

theorem primedOddWinnerBases_union {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (candidateBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    primedOddLeftWinnerBases first labels candidateBases ∪
        primedOddStrictRightWinnerBases first labels candidateBases =
      candidateBases := by
  classical
  ext b
  simp only [primedOddLeftWinnerBases, primedOddStrictRightWinnerBases,
    Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨hb, _⟩ | ⟨hb, _⟩) <;> exact hb
  · intro hb
    by_cases h : primedStoppedExternalRight first labels b ≤
        primedStoppedExternalLeft first labels b
    · exact Or.inl ⟨hb, h⟩
    · exact Or.inr ⟨hb, Nat.lt_of_not_ge h⟩

theorem primedOddStrictRightWinnerBases_right {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (candidateBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels))
    (b : ActiveFreeStoppedBase (primedInitialBase first) labels C
      (primedOddStrictRightWinnerBases first labels candidateBases)) :
    primedStoppedExternalLeft first labels b.1 ≤
      primedStoppedExternalRight first labels b.1 :=
  (Finset.mem_filter.mp b.2.1).2.le

/-- Nonemptiness of the literal primed mixed atom forces every strict-right
winner profile to lie below the stopping level. -/
theorem primedOdd_strictRightWinner_profile_lt_of_nonempty {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hm : 0 < m) (hcard : C.card = k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : PrimedOddOffBaseMixedCondition first labels m C)
    (hterminal : primedStoppedTerminalSite first labels ∈ C)
    (hne : (actualAdmissiblePrimedStoppedVectors m k first labels
      (primedOddSourceConstraint m k C first labels)).Nonempty)
    (candidateBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    ∀ b : ActiveFreeStoppedBase (primedInitialBase first) labels C
        (primedOddStrictRightWinnerBases first labels candidateBases),
      activeFreeStoppedShape (primedInitialBase first) labels C
        (primedOddStrictRightWinnerBases first labels candidateBases) b < m := by
  intro b
  have hpos := primedOdd_mixedCoordinatePos_of_nonempty
    m k C first labels hm hcard hfree hoff hterminal hne b.1
  rw [stoppedMixedBlockValues_activeFree_eq_sourceBelowSet
    (primedInitialBase first) labels m C
    (primedOddStrictRightWinnerBases first labels candidateBases)
    (primedStoppedExternalLeft first labels)
    (primedStoppedExternalRight first labels) b] at hpos
  have hcap := cap_lt_of_negBin_sourceBelowSet_ne_zero _ _ _ hpos
  rw [primedOdd_activeFreeCap_eq_shape_of_rightWinner first labels C
    (primedOddStrictRightWinnerBases first labels candidateBases) b
    (primedOddStrictRightWinnerBases_right first labels candidateBases b)] at hcap
  exact hcap

/-- Tie-left, source-facing right/odd winner law.  This is the disjoint
right branch used with `primedOddWinnerBases_union`; unlike the inclusive
right-cap theorem it cannot overlap the left-winner branch. -/
theorem primedOdd_strictRightWinner_StoppedEquation447Atom_map_law {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (hm : 0 < m) (hk : 0 < k) (hcard : C.card = k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : PrimedOddOffBaseMixedCondition first labels m C)
    (hterminal : primedStoppedTerminalSite first labels ∈ C)
    (hne : (actualAdmissiblePrimedStoppedVectors m k first labels
      (primedOddSourceConstraint m k C first labels)).Nonempty)
    (candidateBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    (simpleRandomWalkLaw.restrict
        (simpleRandomWalk ''
          (actualPrimedStoppedVectorEvent m k first labels
              (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C))).map
        (fun s ↦
          (primedOddActiveFreePathLazy m k C first labels
              (primedOddStrictRightWinnerBases first labels candidateBases) s,
            primedOddActiveFreePathNext m k C first labels
              (primedOddStrictRightWinnerBases first labels candidateBases) s)) =
      simpleRandomWalkLaw
          (simpleRandomWalk ''
            (actualPrimedStoppedVectorEvent m k first labels
                (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C)) •
        ((sourceTruncatedProfileMeasure m
          (activeFreeStoppedShape (primedInitialBase first) labels C
            (primedOddStrictRightWinnerBases first labels candidateBases))).prod
              directionLaw) := by
  apply primedOdd_StoppedEquation447Atom_map_law
    m k C first labels hnondist hm hk hcard hfree hoff hterminal hne
      (primedOddStrictRightWinnerBases first labels candidateBases)
  intro b
  exact primedOdd_activeFreeCap_eq_shape_of_rightWinner
    first labels C
      (primedOddStrictRightWinnerBases first labels candidateBases) b
      (primedOddStrictRightWinnerBases_right first labels candidateBases b)

end Erdos1166.HLOZPrimedOddRightWinner
