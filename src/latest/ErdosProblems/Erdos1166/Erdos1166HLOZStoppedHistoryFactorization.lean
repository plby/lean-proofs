import ErdosProblems.Erdos1166.Erdos1166HLOZStoppedMapLawReduced
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47HighEscape
import ErdosProblems.Erdos1166.Erdos1166HLOZTerminalParityWinner
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47LowStageConnector

namespace Erdos1166.HLOZStoppedHistoryFactorization

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open HLOZDecomposition HLOZActualStopped HLOZIncompleteStoppedBlocks
  HLOZPrimedStopped HLOZPrimedOddMixedReconstruction
  HLOZPrimedOddRightWinner HLOZTerminalParityWinner
  HLOZMixedCreationBlocks HLOZStoppedSourcePartition
  HLOZStoppedMixedReconstruction HLOZStoppedMapLaw
  HLOZStoppedMapLawReduced HLOZStoppedShape HLOZProp48Truncated
  HLOZProp47HighEscape
  HLOZProp47SourceObjects HLOZProp47SourceAssembly HLOZProp47Canonical
  HLOZProp47Parameters
  HLOZProp47LowStageConnector
  HLOZSourceInstantiation

/-- The stopped external blocks not retained as active, free winner blocks. -/
abbrev ComplementStoppedBase {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (C : Finset Site)
    (activeBases : Finset (StoppedExternalBase a labels)) :=
  {b : StoppedExternalBase a labels //
    ¬(b ∈ activeBases ∧ b.1 ∉ C ∧ b.1 + paperE1 ∉ C)}

/-- Restrict a full block-sum vector to the complement of the active free
bases. -/
def restrictComplementStoppedBase {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (C : Finset Site)
    (activeBases : Finset (StoppedExternalBase a labels))
    (u : StoppedExternalBase a labels → ℕ) :
    ComplementStoppedBase a labels C activeBases → ℕ :=
  fun b ↦ u b.1

theorem measurable_restrictComplementStoppedBase {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (C : Finset Site)
    (activeBases : Finset (StoppedExternalBase a labels)) :
    Measurable (restrictComplementStoppedBase a labels C activeBases) :=
  measurable_of_countable _

/-- The coordinatewise conditioned negative-binomial law on all blocks not
retained by the active projection. -/
noncomputable def stoppedMixedComplementMeasure {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (m : ℕ)
    (C : Finset Site) (activeBases : Finset (StoppedExternalBase a labels))
    (externalLeft externalRight : StoppedExternalBase a labels → ℕ) :
    Measure (ComplementStoppedBase a labels C activeBases → ℕ) :=
  Measure.pi fun b ↦
    (HLOZUrn.negBinMeasure
      (Fintype.card (StoppedExternalIndex a labels b.1)))[|
        (stoppedMixedBlockValues a labels m C
          externalLeft externalRight b.1 : Set ℕ)]

theorem stoppedMixedComplementMeasure_isProbabilityMeasure {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (m : ℕ)
    (C : Finset Site) (activeBases : Finset (StoppedExternalBase a labels))
    (externalLeft externalRight : StoppedExternalBase a labels → ℕ)
    (hpos : ∀ b, HLOZUrn.negBinMeasure
      (Fintype.card (StoppedExternalIndex a labels b))
        (stoppedMixedBlockValues a labels m C
          externalLeft externalRight b : Set ℕ) ≠ 0) :
    IsProbabilityMeasure (stoppedMixedComplementMeasure a labels m C
      activeBases externalLeft externalRight) := by
  unfold stoppedMixedComplementMeasure
  letI (b : ComplementStoppedBase a labels C activeBases) :
      IsProbabilityMeasure
        ((HLOZUrn.negBinMeasure
          (Fintype.card (StoppedExternalIndex a labels b.1)))[|
            (stoppedMixedBlockValues a labels m C
              externalLeft externalRight b.1 : Set ℕ)]) :=
    cond_isProbabilityMeasure (hpos b.1)
  infer_instance

/-- The exact active/complement product decomposition of the conditioned
mixed block-sum law. -/
theorem stoppedBlockNegBinMeasure_cond_mixed_map_active_complement {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (m : ℕ)
    (C : Finset Site) (activeBases : Finset (StoppedExternalBase a labels))
    (externalLeft externalRight : StoppedExternalBase a labels → ℕ)
    (hpos : ∀ b, HLOZUrn.negBinMeasure
      (Fintype.card (StoppedExternalIndex a labels b))
        (stoppedMixedBlockValues a labels m C
          externalLeft externalRight b : Set ℕ) ≠ 0) :
    ((stoppedBlockNegBinMeasure a labels)[|
      stoppedMixedBlockSumEvent a labels m C externalLeft externalRight]).map
        (fun u ↦
          (restrictActiveFreeStoppedBase a labels C activeBases u,
            restrictComplementStoppedBase a labels C activeBases u)) =
      (sourceCappedProfileMeasure m
        (activeFreeStoppedShape a labels C activeBases)
        (activeFreeCapProfile a labels C activeBases
          externalLeft externalRight)).prod
        (stoppedMixedComplementMeasure a labels m C activeBases
          externalLeft externalRight) := by
  classical
  let p : StoppedExternalBase a labels → Prop := fun b ↦
    b ∈ activeBases ∧ b.1 ∉ C ∧ b.1 + paperE1 ∉ C
  let μ : StoppedExternalBase a labels → Measure ℕ := fun b ↦
    (HLOZUrn.negBinMeasure
      (Fintype.card (StoppedExternalIndex a labels b)))[|
        (stoppedMixedBlockValues a labels m C
          externalLeft externalRight b : Set ℕ)]
  letI (b : StoppedExternalBase a labels) : IsProbabilityMeasure (μ b) :=
    cond_isProbabilityMeasure (hpos b)
  rw [stoppedBlockNegBinMeasure_cond_mixed_eq_pi_cond
    a labels m C externalLeft externalRight hpos]
  change (Measure.pi μ).map
      (fun u ↦
        (restrictActiveFreeStoppedBase a labels C activeBases u,
          restrictComplementStoppedBase a labels C activeBases u)) = _
  have hsplit := (measurePreserving_piEquivPiSubtypeProd μ p).map_eq
  have hfun : (fun u : StoppedExternalBase a labels → ℕ ↦
      (restrictActiveFreeStoppedBase a labels C activeBases u,
        restrictComplementStoppedBase a labels C activeBases u)) =
      MeasurableEquiv.piEquivPiSubtypeProd
        (fun _ : StoppedExternalBase a labels ↦ ℕ) p := by
    rfl
  rw [hfun, hsplit]
  congr 1
  · unfold sourceCappedProfileMeasure
    congr 1
    funext b
    unfold μ
    rw [stoppedMixedBlockValues_activeFree_eq_sourceBelowSet]
    rfl

/-- Reassociate three independent factors, exchanging the middle and last
coordinates. -/
theorem map_swap_middle
    {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] (μ : Measure X) (ν : Measure Y) (ρ : Measure Z)
    [SFinite μ] [SFinite ν] [SFinite ρ] :
    ((μ.prod ν).prod ρ).map
        (fun w : (X × Y) × Z ↦ ((w.1.1, w.2), w.1.2)) =
      (μ.prod ρ).prod ν := by
  let h₁ := measurePreserving_prodAssoc μ ν ρ
  let h₂ := (MeasurePreserving.id μ).prod
    (Measure.measurePreserving_swap (μ := ν) (ν := ρ))
  let h₃ := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μ ρ ν)
  have h := h₃.comp (h₂.comp h₁)
  have heq : (fun w : (X × Y) × Z ↦ ((w.1.1, w.2), w.1.2)) =
      MeasurableEquiv.prodAssoc.symm ∘ Prod.map id Prod.swap ∘
        MeasurableEquiv.prodAssoc := by
    funext w
    rfl
  rw [heq]
  exact h.map_eq

/-- If a statistic splits into two independent factors, adjoining an
independent direction to the first factor preserves independence from the
second. -/
theorem map_split_prod_direction
    {B X Z : Type*} [MeasurableSpace B] [MeasurableSpace X]
    [MeasurableSpace Z] (μ : Measure B) (ν : Measure X) (ρ : Measure Z)
    [SFinite μ] [SFinite ν] [SFinite ρ]
    (f : B → X × Z) (hf : Measurable f)
    (hmap : μ.map f = ν.prod ρ) :
    (μ.prod directionLaw).map
        (fun w : B × Direction ↦ (((f w.1).1, w.2), (f w.1).2)) =
      (ν.prod directionLaw).prod ρ := by
  let F : (X × Z) × Direction → (X × Direction) × Z :=
    fun w ↦ ((w.1.1, w.2), w.1.2)
  have hF : Measurable F :=
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
      (measurable_snd.comp measurable_fst)
  have heq : (fun w : B × Direction ↦ (((f w.1).1, w.2), (f w.1).2)) =
      F ∘ Prod.map f id := by
    funext w
    rfl
  rw [heq, ← Measure.map_map hF (hf.prodMap measurable_id)]
  rw [← Measure.map_prod_map μ directionLaw hf measurable_id,
    Measure.map_id, hmap]
  exact map_swap_middle ν ρ directionLaw

theorem hasLaw_split_prod_direction
    {Omega B X Z : Type*} [MeasurableSpace Omega] [MeasurableSpace B]
    [MeasurableSpace X] [MeasurableSpace Z]
    {P : Measure Omega} {W : Omega → B} {D : Omega → Direction}
    {μ : Measure B} {ν : Measure X} {ρ : Measure Z}
    [SFinite μ] [SFinite ν] [SFinite ρ]
    (hWD : HasLaw (fun omega ↦ (W omega, D omega))
      (μ.prod directionLaw) P)
    (f : B → X × Z) (hf : Measurable f)
    (hmap : μ.map f = ν.prod ρ) :
    HasLaw (fun omega ↦ (((f (W omega)).1, D omega), (f (W omega)).2))
      ((ν.prod directionLaw).prod ρ) P := by
  let F : B × Direction → (X × Direction) × Z :=
    fun w ↦ (((f w.1).1, w.2), (f w.1).2)
  have hF : Measurable F :=
    (((measurable_fst.comp hf).comp measurable_fst).prodMk measurable_snd).prodMk
      ((measurable_snd.comp hf).comp measurable_fst)
  have hFLaw : HasLaw F ((ν.prod directionLaw).prod ρ)
      (μ.prod directionLaw) :=
    ⟨hF.aemeasurable, map_split_prod_direction μ ν ρ f hf hmap⟩
  simpa only [F] using hFLaw.fun_comp hWD

/-- Generic active/complement version of the stopped grouping theorem.
Starting from the source run-vector law with its fresh direction, the mixed
block constraints split exactly into the active capped profile, the fresh
direction, and every complementary block sum. -/
theorem activeFree_complement_capped_hasLaw_of_joint {q : ℕ}
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
        ((restrictActiveFreeStoppedBase a labels C activeBases
            (stoppedPaperBlockSums a labels
              (stoppedPaperBlockVector a labels (X omega))), D omega),
          restrictComplementStoppedBase a labels C activeBases
            (stoppedPaperBlockSums a labels
              (stoppedPaperBlockVector a labels (X omega)))))
      (((sourceCappedProfileMeasure m
          (activeFreeStoppedShape a labels C activeBases)
          (activeFreeCapProfile a labels C activeBases
            externalLeft externalRight)).prod directionLaw).prod
        (stoppedMixedComplementMeasure a labels m C activeBases
          externalLeft externalRight)) P := by
  let S := fun v : Fin (q + 1) → ℕ ↦ stoppedPaperBlockSums a labels
    (stoppedPaperBlockVector a labels v)
  let R := restrictActiveFreeStoppedBase a labels C activeBases
  let Q := restrictComplementStoppedBase a labels C activeBases
  let Split := fun v : Fin (q + 1) → ℕ ↦ (R (S v), Q (S v))
  let fullLaw := (stoppedBlockNegBinMeasure a labels)[|
    stoppedMixedBlockSumEvent a labels m C externalLeft externalRight]
  let activeLaw := sourceCappedProfileMeasure m
    (activeFreeStoppedShape a labels C activeBases)
    (activeFreeCapProfile a labels C activeBases externalLeft externalRight)
  let complementLaw := stoppedMixedComplementMeasure a labels m C activeBases
    externalLeft externalRight
  letI (b : ActiveFreeStoppedBase a labels C activeBases) :
      IsProbabilityMeasure
        ((HLOZUrn.negBinMeasure
          (activeFreeStoppedShape a labels C activeBases b))[|
            sourceBelowSet m
              (activeFreeCapProfile a labels C activeBases
                externalLeft externalRight b)]) := by
    apply cond_isProbabilityMeasure
    unfold activeFreeStoppedShape
    rw [← stoppedMixedBlockValues_activeFree_eq_sourceBelowSet]
    exact hMixedCoordinatePos b.1
  letI : IsProbabilityMeasure activeLaw := by
    unfold activeLaw sourceCappedProfileMeasure
    infer_instance
  letI : IsProbabilityMeasure complementLaw := by
    unfold complementLaw
    exact stoppedMixedComplementMeasure_isProbabilityMeasure
      a labels m C activeBases externalLeft externalRight hMixedCoordinatePos
  have hgrouped := stoppedPaperBlockSums_hasLaw_mixed_finset
    a labels m C externalLeft externalRight V hGroupedEvent
  have hmapS :
      ((HLOZUrn.runVectorMeasure (q + 1))[|(V : Set _)]).map S =
        fullLaw := by
    simpa only [S, fullLaw] using hgrouped.map_eq
  have hsplitFull : fullLaw.map (fun u ↦ (R u, Q u)) =
      activeLaw.prod complementLaw := by
    simpa only [fullLaw, activeLaw, complementLaw, R, Q] using
      stoppedBlockNegBinMeasure_cond_mixed_map_active_complement
        a labels m C activeBases externalLeft externalRight
          hMixedCoordinatePos
  have hSplit : Measurable Split :=
    ((measurable_restrictActiveFreeStoppedBase
        a labels C activeBases).comp
      ((measurable_stoppedPaperBlockSums a labels).comp
        (measurable_stoppedPaperBlockVector a labels))).prodMk
    ((measurable_restrictComplementStoppedBase
        a labels C activeBases).comp
      ((measurable_stoppedPaperBlockSums a labels).comp
        (measurable_stoppedPaperBlockVector a labels)))
  have hmapSplit :
      ((HLOZUrn.runVectorMeasure (q + 1))[|(V : Set _)]).map Split =
        activeLaw.prod complementLaw := by
    have hRQ : Measurable (fun u ↦ (R u, Q u)) :=
      (measurable_restrictActiveFreeStoppedBase
        a labels C activeBases).prodMk
          (measurable_restrictComplementStoppedBase
            a labels C activeBases)
    have hS : Measurable S :=
      (measurable_stoppedPaperBlockSums a labels).comp
        (measurable_stoppedPaperBlockVector a labels)
    change ((HLOZUrn.runVectorMeasure (q + 1))[|(V : Set _)]).map
      ((fun u ↦ (R u, Q u)) ∘ S) = _
    rw [← Measure.map_map hRQ hS, hmapS, hsplitFull]
  simpa only [Split, S, R, Q, activeLaw, complementLaw] using
    hasLaw_split_prod_direction hjoint Split hSplit hmapSplit

/-- A nonempty grouped run-vector event supplies all coordinate positivity
premises needed by the active/complement factorization.  This terminal-safe
version is kept here because the analogous reconstruction helper is private
to `HLOZTerminalParityWinner`. -/
theorem mixedCoordinatePos_of_grouped_nonempty {q : ℕ}
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

/-! ### Concrete unprimed-even stopped factorization -/

noncomputable def unprimedEvenComplementStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    (ℕ → Direction) →
      (ComplementStoppedBase (0, 0) labels C activeBases → ℕ) :=
  fun omega ↦
    restrictComplementStoppedBase (0, 0) labels C activeBases
      (stoppedPaperBlockSums (0, 0) labels
        (stoppedPaperBlockVector (0, 0) labels
          (actualStoppedVector m k labels
            (unprimedEvenSourceConstraint m k C labels) omega)))

theorem measurable_unprimedEvenComplementStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    Measurable
      (unprimedEvenComplementStatistic m k C labels activeBases) := by
  exact (measurable_restrictComplementStoppedBase
    (0, 0) labels C activeBases).comp
      ((measurable_stoppedPaperBlockSums (0, 0) labels).comp
        ((measurable_stoppedPaperBlockVector (0, 0) labels).comp
          (measurable_actualStoppedVector m k labels hnondist
            (unprimedEvenSourceConstraint m k C labels))))

/-- The stopped source law jointly factors the active block sums with their
fresh direction from every complementary stopped block sum. -/
theorem unprimedEven_active_complement_direction_hasLaw_reduced {q : ℕ}
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
      (fun omega ↦
        ((restrictActiveFreeStoppedBase (0, 0) labels C activeBases
              (stoppedPaperBlockSums (0, 0) labels
                (stoppedPaperBlockVector (0, 0) labels
                  (actualStoppedVector m k labels
                    (unprimedEvenSourceConstraint m k C labels) omega))),
            incrementShiftAfter (stoppedCreationTime m k) omega 0),
          unprimedEvenComplementStatistic m k C labels activeBases omega))
      (((sourceCappedProfileMeasure m
          (activeFreeStoppedShape (0, 0) labels C activeBases)
          (activeFreeCapProfile (0, 0) labels C activeBases
            (stoppedExternalLeft (0, 0) labels)
            (stoppedExternalRight (0, 0) labels))).prod directionLaw).prod
        (stoppedMixedComplementMeasure (0, 0) labels m C activeBases
          (stoppedExternalLeft (0, 0) labels)
          (stoppedExternalRight (0, 0) labels)))
      incrementLaw[|
        actualStoppedVectorEvent m k labels (stoppedRunVectorBox q m) ∩
          stoppedSourceCondition m k C] := by
  let E := unprimedEvenSourceConstraint m k C labels
  let A := actualStoppedVectorEvent m k labels (stoppedRunVectorBox q m) ∩
    stoppedSourceCondition m k C
  let X := actualStoppedVector m k labels E
  let tau := stoppedCreationTime m k
  let S := fun v : Fin (q + 1) → ℕ ↦
    stoppedPaperBlockSums (0, 0) labels
      (stoppedPaperBlockVector (0, 0) labels v)
  let R := restrictActiveFreeStoppedBase (0, 0) labels C activeBases
  let Q := restrictComplementStoppedBase (0, 0) labels C activeBases
  let Split := fun v : Fin (q + 1) → ℕ ↦ (R (S v), Q (S v))
  have htau : Measurable tau := measurable_stoppedCreationTime m k
  have hX : Measurable X :=
    measurable_actualStoppedVector m k labels hnondist E
  have hsource : HasLaw X
      ((HLOZUrn.runVectorMeasure (q + 1))[|
        (actualAdmissibleStoppedVectors m k labels E : Set _)])
      incrementLaw[|A] := by
    simpa only [E, A, X] using
      unprimedEven_source_hasLaw m k C labels hnondist hm hk hfree
  have hjoint : HasLaw (fun omega ↦
      (X omega, incrementShiftAfter tau omega 0))
      (((HLOZUrn.runVectorMeasure (q + 1))[|
        (actualAdmissibleStoppedVectors m k labels E : Set _)]).prod
          directionLaw) incrementLaw[|A] := by
    apply hasLaw_prod_direction_after tau A X _ htau
    · intro n
      simpa only [A, tau] using
        unprimedEven_sourcePast m k C labels hnondist hm hk hfree n
    · exact hX
    · intro v n
      simpa only [A, X, tau, Set.inter_assoc] using
        unprimedEven_vectorFiberPast m k C labels hnondist hm hk hfree v n
    · exact hsource
  have hpos := unprimedEven_mixedCoordinatePos_of_nonempty
    m k C labels hm hcard hfree hoff hterminal hne
  let fullLaw := (stoppedBlockNegBinMeasure (0, 0) labels)[|
    stoppedMixedBlockSumEvent (0, 0) labels m C
      (stoppedExternalLeft (0, 0) labels)
      (stoppedExternalRight (0, 0) labels)]
  let activeLaw := sourceCappedProfileMeasure m
    (activeFreeStoppedShape (0, 0) labels C activeBases)
    (activeFreeCapProfile (0, 0) labels C activeBases
      (stoppedExternalLeft (0, 0) labels)
      (stoppedExternalRight (0, 0) labels))
  let complementLaw := stoppedMixedComplementMeasure (0, 0) labels m C activeBases
    (stoppedExternalLeft (0, 0) labels)
    (stoppedExternalRight (0, 0) labels)
  letI (b : ActiveFreeStoppedBase (0, 0) labels C activeBases) :
      IsProbabilityMeasure
        ((HLOZUrn.negBinMeasure
          (activeFreeStoppedShape (0, 0) labels C activeBases b))[|
            sourceBelowSet m
              (activeFreeCapProfile (0, 0) labels C activeBases
                (stoppedExternalLeft (0, 0) labels)
                (stoppedExternalRight (0, 0) labels) b)]) := by
    apply cond_isProbabilityMeasure
    unfold activeFreeStoppedShape
    rw [← stoppedMixedBlockValues_activeFree_eq_sourceBelowSet]
    exact hpos b.1
  letI : IsProbabilityMeasure activeLaw := by
    unfold activeLaw sourceCappedProfileMeasure
    infer_instance
  letI : IsProbabilityMeasure complementLaw := by
    unfold complementLaw
    exact stoppedMixedComplementMeasure_isProbabilityMeasure
      (0, 0) labels m C activeBases
        (stoppedExternalLeft (0, 0) labels)
        (stoppedExternalRight (0, 0) labels) hpos
  have hgrouped := stoppedPaperBlockSums_hasLaw_mixed_finset
    (0, 0) labels m C
    (stoppedExternalLeft (0, 0) labels)
    (stoppedExternalRight (0, 0) labels)
    (actualAdmissibleStoppedVectors m k labels E)
    (actualAdmissible_unprimedEvenSourceConstraint_eq_mixedBlockPreimage
      m k C labels hm hcard hfree hoff hterminal)
  have hmapS :
      ((HLOZUrn.runVectorMeasure (q + 1))[|
        (actualAdmissibleStoppedVectors m k labels E : Set _)]).map S =
        fullLaw := by
    simpa only [S, fullLaw] using hgrouped.map_eq
  have hsplitFull : fullLaw.map (fun u ↦ (R u, Q u)) =
      activeLaw.prod complementLaw := by
    simpa only [fullLaw, activeLaw, complementLaw, R, Q] using
      stoppedBlockNegBinMeasure_cond_mixed_map_active_complement
        (0, 0) labels m C activeBases
          (stoppedExternalLeft (0, 0) labels)
          (stoppedExternalRight (0, 0) labels) hpos
  have hSplit : Measurable Split :=
    ((measurable_restrictActiveFreeStoppedBase
        (0, 0) labels C activeBases).comp
      ((measurable_stoppedPaperBlockSums (0, 0) labels).comp
        (measurable_stoppedPaperBlockVector (0, 0) labels))).prodMk
    ((measurable_restrictComplementStoppedBase
        (0, 0) labels C activeBases).comp
      ((measurable_stoppedPaperBlockSums (0, 0) labels).comp
        (measurable_stoppedPaperBlockVector (0, 0) labels)))
  have hmapSplit :
      ((HLOZUrn.runVectorMeasure (q + 1))[|
        (actualAdmissibleStoppedVectors m k labels E : Set _)]).map Split =
        activeLaw.prod complementLaw := by
    have hRQ : Measurable (fun u ↦ (R u, Q u)) :=
      (measurable_restrictActiveFreeStoppedBase
        (0, 0) labels C activeBases).prodMk
          (measurable_restrictComplementStoppedBase
            (0, 0) labels C activeBases)
    have hS : Measurable S :=
      (measurable_stoppedPaperBlockSums (0, 0) labels).comp
        (measurable_stoppedPaperBlockVector (0, 0) labels)
    change ((HLOZUrn.runVectorMeasure (q + 1))[|
      (actualAdmissibleStoppedVectors m k labels E : Set _)]).map
        ((fun u ↦ (R u, Q u)) ∘ S) = _
    rw [← Measure.map_map hRQ hS, hmapS, hsplitFull]
  simpa only [A, X, tau, Split, S, R, Q, activeLaw, complementLaw,
    unprimedEvenComplementStatistic] using
      hasLaw_split_prod_direction hjoint Split hSplit hmapSplit

/-- On the canonical left-winner filter, the active capped factor is exactly
the source truncated profile law. -/
theorem unprimedEven_leftWinner_active_complement_direction_hasLaw {q : ℕ}
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
    let activeBases := unprimedEvenLeftWinnerBases labels candidateBases
    HasLaw
      (fun omega ↦
        ((restrictActiveFreeStoppedBase (0, 0) labels C activeBases
              (stoppedPaperBlockSums (0, 0) labels
                (stoppedPaperBlockVector (0, 0) labels
                  (actualStoppedVector m k labels
                    (unprimedEvenSourceConstraint m k C labels) omega))),
            incrementShiftAfter (stoppedCreationTime m k) omega 0),
          unprimedEvenComplementStatistic m k C labels activeBases omega))
      (((sourceTruncatedProfileMeasure m
          (activeFreeStoppedShape (0, 0) labels C activeBases)).prod
            directionLaw).prod
        (stoppedMixedComplementMeasure (0, 0) labels m C activeBases
          (stoppedExternalLeft (0, 0) labels)
          (stoppedExternalRight (0, 0) labels)))
      incrementLaw[|
        actualStoppedVectorEvent m k labels (stoppedRunVectorBox q m) ∩
          stoppedSourceCondition m k C] := by
  dsimp only
  let activeBases := unprimedEvenLeftWinnerBases labels candidateBases
  have hwinning : ∀ b : ActiveFreeStoppedBase (0, 0) labels C activeBases,
      activeFreeCapProfile (0, 0) labels C activeBases
          (stoppedExternalLeft (0, 0) labels)
          (stoppedExternalRight (0, 0) labels) b =
        activeFreeStoppedShape (0, 0) labels C activeBases b := by
    intro b
    exact unprimedEven_activeFreeCap_eq_shape_of_leftWinner labels C
      activeBases b (unprimedEvenLeftWinnerBases_left labels candidateBases b)
  have h := unprimedEven_active_complement_direction_hasLaw_reduced
    m k C labels hnondist hm hk hcard hfree hoff hterminal hne activeBases
  rw [sourceCappedProfileMeasure_eq_truncated m
    (activeFreeStoppedShape (0, 0) labels C activeBases)
    (activeFreeCapProfile (0, 0) labels C activeBases
      (stoppedExternalLeft (0, 0) labels)
      (stoppedExternalRight (0, 0) labels)) hwinning] at h
  exact h

noncomputable def unprimedEvenActiveComplementStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    (ℕ → Direction) →
      ((ActiveFreeStoppedBase (0, 0) labels C activeBases → ℕ) × Direction) ×
        (ComplementStoppedBase (0, 0) labels C activeBases → ℕ) :=
  fun omega ↦
    ((restrictActiveFreeStoppedBase (0, 0) labels C activeBases
          (stoppedPaperBlockSums (0, 0) labels
            (stoppedPaperBlockVector (0, 0) labels
              (actualStoppedVector m k labels
                (unprimedEvenSourceConstraint m k C labels) omega))),
        incrementShiftAfter (stoppedCreationTime m k) omega 0),
      unprimedEvenComplementStatistic m k C labels activeBases omega)

theorem measurable_unprimedEvenActiveComplementStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    Measurable
      (unprimedEvenActiveComplementStatistic m k C labels activeBases) := by
  exact (measurable_unprimedEvenActiveFreeStatistic
    m k C labels hnondist activeBases).prodMk
      (measurable_unprimedEvenComplementStatistic
        m k C labels hnondist activeBases)

/-- Complement statistic on walk-path space, chosen as the second field of
the jointly lifted statistic so that its extension is coordinated with the
active/fresh-direction fields on every stopped atom. -/
noncomputable def unprimedEvenComplementPath {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    (ℕ → Site) → ComplementStoppedBase (0, 0) labels C activeBases → ℕ :=
  fun s ↦ (liftIncrementStatisticToPath
    (unprimedEvenActiveComplementStatistic m k C labels activeBases) s).2

theorem measurable_unprimedEvenComplementPath {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    Measurable (unprimedEvenComplementPath m k C labels activeBases) :=
  measurable_snd.comp (measurable_liftIncrementStatisticToPath
    (measurable_unprimedEvenActiveComplementStatistic
      m k C labels hnondist activeBases))

/-- Unnormalized path-space form of the canonical left-winner joint
active/complement factorization. -/
theorem unprimedEven_leftWinner_active_complement_path_map_law {q : ℕ}
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
    let activeBases := unprimedEvenLeftWinnerBases labels candidateBases
    (simpleRandomWalkLaw.restrict
        (simpleRandomWalk ''
          (actualStoppedVectorEvent m k labels (stoppedRunVectorBox q m) ∩
            stoppedSourceCondition m k C))).map
        (fun s ↦
          ((unprimedEvenActiveFreePathLazy m k C labels activeBases s,
              unprimedEvenActiveFreePathNext m k C labels activeBases s),
            unprimedEvenComplementPath m k C labels activeBases s)) =
      simpleRandomWalkLaw
          (simpleRandomWalk ''
            (actualStoppedVectorEvent m k labels (stoppedRunVectorBox q m) ∩
              stoppedSourceCondition m k C)) •
        (((sourceTruncatedProfileMeasure m
          (activeFreeStoppedShape (0, 0) labels C activeBases)).prod
            directionLaw).prod
          (stoppedMixedComplementMeasure (0, 0) labels m C activeBases
            (stoppedExternalLeft (0, 0) labels)
            (stoppedExternalRight (0, 0) labels))) := by
  dsimp only
  let activeBases := unprimedEvenLeftWinnerBases labels candidateBases
  let A := actualStoppedVectorEvent m k labels (stoppedRunVectorBox q m) ∩
    stoppedSourceCondition m k C
  let J := unprimedEvenActiveComplementStatistic m k C labels activeBases
  have hA : MeasurableSet A := by
    dsimp only [A]
    rw [unprimedEven_source_partition m k C labels hm hk hfree]
    exact measurableSet_actualStoppedVectorEvent _ _ _ _
  have hJ : Measurable J :=
    measurable_unprimedEvenActiveComplementStatistic
      m k C labels hnondist activeBases
  have hLaw := liftIncrementStatistic_path_map_law hA hJ
    (unprimedEven_leftWinner_active_complement_direction_hasLaw
      m k C labels hnondist hm hk hcard hfree hoff hterminal hne candidateBases)
  have hPath : MeasurableSet (simpleRandomWalk '' A) :=
    HLOZSourceInstantiation.measurableEmbedding_simpleRandomWalk.measurableSet_image.2 hA
  calc
    (simpleRandomWalkLaw.restrict (simpleRandomWalk '' A)).map
        (fun s ↦
          ((unprimedEvenActiveFreePathLazy m k C labels activeBases s,
              unprimedEvenActiveFreePathNext m k C labels activeBases s),
            unprimedEvenComplementPath m k C labels activeBases s)) =
      (simpleRandomWalkLaw.restrict (simpleRandomWalk '' A)).map
        (liftIncrementStatisticToPath J) := by
          apply Measure.map_congr
          filter_upwards [ae_restrict_mem hPath] with s hs
          rcases hs with ⟨omega, homega, rfl⟩
          simp only [unprimedEvenActiveFreePathLazy,
            unprimedEvenActiveFreePathNext, unprimedEvenComplementPath,
            liftIncrementStatisticToPath_simpleRandomWalk, J,
            unprimedEvenActiveComplementStatistic,
            unprimedEvenActiveFreeStatistic]
    _ = _ := by simpa only [A, activeBases, J] using hLaw

/-! ### Primed-odd strict-right active/complement factorization -/

noncomputable def primedOddComplementStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    (ℕ → Direction) →
      (ComplementStoppedBase (primedInitialBase first) labels C
        activeBases → ℕ) :=
  fun omega ↦
    restrictComplementStoppedBase (primedInitialBase first) labels C
      activeBases
      (stoppedPaperBlockSums (primedInitialBase first) labels
        (stoppedPaperBlockVector (primedInitialBase first) labels
          (actualPrimedStoppedVector m k first labels
            (primedOddSourceConstraint m k C first labels) omega)))

theorem measurable_primedOddComplementStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    Measurable
      (primedOddComplementStatistic m k C first labels activeBases) := by
  exact (measurable_restrictComplementStoppedBase
    (primedInitialBase first) labels C activeBases).comp
      ((measurable_stoppedPaperBlockSums
        (primedInitialBase first) labels).comp
        ((measurable_stoppedPaperBlockVector
          (primedInitialBase first) labels).comp
          (measurable_actualPrimedStoppedVector m k first labels hnondist
            (primedOddSourceConstraint m k C first labels))))

noncomputable def primedOddActiveComplementStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    (ℕ → Direction) →
      ((ActiveFreeStoppedBase (primedInitialBase first) labels C
          activeBases → ℕ) × Direction) ×
        (ComplementStoppedBase (primedInitialBase first) labels C
          activeBases → ℕ) :=
  fun omega ↦
    ((restrictActiveFreeStoppedBase (primedInitialBase first) labels C
          activeBases
          (stoppedPaperBlockSums (primedInitialBase first) labels
            (stoppedPaperBlockVector (primedInitialBase first) labels
              (actualPrimedStoppedVector m k first labels
                (primedOddSourceConstraint m k C first labels) omega))),
        incrementShiftAfter (stoppedCreationTime m k) omega 0),
      primedOddComplementStatistic m k C first labels activeBases omega)

theorem measurable_primedOddActiveComplementStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    Measurable
      (primedOddActiveComplementStatistic m k C first labels activeBases) := by
  exact (measurable_primedOddActiveFreeStatistic
    m k C first labels hnondist activeBases).prodMk
      (measurable_primedOddComplementStatistic
        m k C first labels hnondist activeBases)

/-- The literal primed-odd source law jointly retains the strict-right
winner coordinates, the fresh direction, and every complementary block. -/
theorem primedOdd_strictRightWinner_active_complement_direction_hasLaw
    {q : ℕ}
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
    let activeBases :=
      primedOddStrictRightWinnerBases first labels candidateBases
    HasLaw
      (primedOddActiveComplementStatistic m k C first labels activeBases)
      (((sourceTruncatedProfileMeasure m
          (activeFreeStoppedShape (primedInitialBase first) labels C
            activeBases)).prod directionLaw).prod
        (stoppedMixedComplementMeasure (primedInitialBase first) labels m C
          activeBases (primedStoppedExternalLeft first labels)
            (primedStoppedExternalRight first labels)))
      incrementLaw[|
        actualPrimedStoppedVectorEvent m k first labels
            (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C] := by
  dsimp only
  let activeBases :=
    primedOddStrictRightWinnerBases first labels candidateBases
  let E := primedOddSourceConstraint m k C first labels
  let A := actualPrimedStoppedVectorEvent m k first labels
      (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C
  let X := actualPrimedStoppedVector m k first labels E
  let tau := stoppedCreationTime m k
  have hX : Measurable X :=
    measurable_actualPrimedStoppedVector m k first labels hnondist E
  have hsource : HasLaw X
      ((HLOZUrn.runVectorMeasure (q + 1))[|
        (actualAdmissiblePrimedStoppedVectors m k first labels E : Set _)])
      incrementLaw[|A] := by
    simpa only [E, A, X] using
      primedOdd_source_hasLaw m k C first labels hnondist hm hk hfree
  have hjoint : HasLaw (fun omega ↦
      (X omega, incrementShiftAfter tau omega 0))
      (((HLOZUrn.runVectorMeasure (q + 1))[|
        (actualAdmissiblePrimedStoppedVectors
          m k first labels E : Set _)]).prod directionLaw)
      incrementLaw[|A] := by
    apply hasLaw_prod_direction_after tau A X _
      (measurable_stoppedCreationTime m k)
    · intro n
      simpa only [A, tau] using
        primedOdd_sourcePast m k C first labels hnondist hm hk hfree n
    · exact hX
    · intro v n
      simpa only [A, X, tau, Set.inter_assoc] using
        primedOdd_vectorFiberPast m k C first labels hnondist
          hm hk hfree v n
    · exact hsource
  have hpos := primedOdd_mixedCoordinatePos_of_nonempty
    m k C first labels hm hcard hfree hoff hterminal hne
  have hgrouped :
      (actualAdmissiblePrimedStoppedVectors m k first labels E : Set _) =
        (fun v ↦ stoppedPaperBlockSums (primedInitialBase first) labels
          (stoppedPaperBlockVector (primedInitialBase first) labels v)) ⁻¹'
          stoppedMixedBlockSumEvent (primedInitialBase first) labels m C
            (primedStoppedExternalLeft first labels)
            (primedStoppedExternalRight first labels) := by
    simpa only [E] using
      actualAdmissible_primedOddSourceConstraint_eq_mixedBlockPreimage
        m k C first labels hm hcard hfree hoff hterminal
  have h := activeFree_complement_capped_hasLaw_of_joint
    (primedInitialBase first) labels m C activeBases
      (primedStoppedExternalLeft first labels)
      (primedStoppedExternalRight first labels)
      (actualAdmissiblePrimedStoppedVectors m k first labels E)
      incrementLaw[|A] X
      (fun omega ↦ incrementShiftAfter tau omega 0)
      hjoint hgrouped hpos
  have hwinning : ∀ b : ActiveFreeStoppedBase
      (primedInitialBase first) labels C activeBases,
      activeFreeCapProfile (primedInitialBase first) labels C activeBases
          (primedStoppedExternalLeft first labels)
          (primedStoppedExternalRight first labels) b =
        activeFreeStoppedShape (primedInitialBase first) labels C
          activeBases b := by
    intro b
    exact primedOdd_activeFreeCap_eq_shape_of_rightWinner first labels C
      activeBases b
        (primedOddStrictRightWinnerBases_right first labels candidateBases b)
  rw [sourceCappedProfileMeasure_eq_truncated m
    (activeFreeStoppedShape (primedInitialBase first) labels C activeBases)
    (activeFreeCapProfile (primedInitialBase first) labels C activeBases
      (primedStoppedExternalLeft first labels)
      (primedStoppedExternalRight first labels)) hwinning] at h
  change HasLaw
    (primedOddActiveComplementStatistic m k C first labels activeBases)
    (((sourceTruncatedProfileMeasure m
        (activeFreeStoppedShape (primedInitialBase first) labels C
          activeBases)).prod directionLaw).prod
      (stoppedMixedComplementMeasure (primedInitialBase first) labels m C
        activeBases (primedStoppedExternalLeft first labels)
          (primedStoppedExternalRight first labels)))
    incrementLaw[|A] at h
  simpa only [A, activeBases] using h

noncomputable def primedOddComplementPath {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    (ℕ → Site) → ComplementStoppedBase
      (primedInitialBase first) labels C activeBases → ℕ :=
  fun s ↦ (liftIncrementStatisticToPath
    (primedOddActiveComplementStatistic m k C first labels activeBases) s).2

theorem measurable_primedOddComplementPath {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    Measurable (primedOddComplementPath m k C first labels activeBases) :=
  measurable_snd.comp (measurable_liftIncrementStatisticToPath
    (measurable_primedOddActiveComplementStatistic
      m k C first labels hnondist activeBases))

/-- Unnormalized path-space joint law for the primed-odd strict-right
branch. -/
theorem primedOdd_strictRightWinner_active_complement_path_map_law
    {q : ℕ}
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
    let activeBases :=
      primedOddStrictRightWinnerBases first labels candidateBases
    (simpleRandomWalkLaw.restrict
        (simpleRandomWalk ''
          (actualPrimedStoppedVectorEvent m k first labels
              (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C))).map
        (fun s ↦
          ((primedOddActiveFreePathLazy m k C first labels activeBases s,
              primedOddActiveFreePathNext m k C first labels activeBases s),
            primedOddComplementPath m k C first labels activeBases s)) =
      simpleRandomWalkLaw
          (simpleRandomWalk ''
            (actualPrimedStoppedVectorEvent m k first labels
                (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C)) •
        (((sourceTruncatedProfileMeasure m
          (activeFreeStoppedShape (primedInitialBase first) labels C
            activeBases)).prod directionLaw).prod
          (stoppedMixedComplementMeasure (primedInitialBase first) labels m C
            activeBases (primedStoppedExternalLeft first labels)
              (primedStoppedExternalRight first labels))) := by
  dsimp only
  let activeBases :=
    primedOddStrictRightWinnerBases first labels candidateBases
  let A := actualPrimedStoppedVectorEvent m k first labels
      (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C
  let J := primedOddActiveComplementStatistic m k C first labels activeBases
  have hA : MeasurableSet A := by
    dsimp only [A]
    rw [primedOdd_source_partition m k C first labels hm hk hfree]
    unfold actualPrimedStoppedVectorEvent
    exact MeasurableSet.iUnion fun v ↦ MeasurableSet.iUnion fun _ ↦
      measurableSet_stoppedPrefixAtom
        (reconstructedPrimedStoppedPrefix first labels v)
  have hJ : Measurable J :=
    measurable_primedOddActiveComplementStatistic
      m k C first labels hnondist activeBases
  have hLaw := liftIncrementStatistic_path_map_law hA hJ
    (primedOdd_strictRightWinner_active_complement_direction_hasLaw
      m k C first labels hnondist hm hk hcard hfree hoff hterminal hne
        candidateBases)
  have hPath : MeasurableSet (simpleRandomWalk '' A) :=
    HLOZSourceInstantiation.measurableEmbedding_simpleRandomWalk
      |>.measurableSet_image.2 hA
  calc
    (simpleRandomWalkLaw.restrict (simpleRandomWalk '' A)).map
        (fun s ↦
          ((primedOddActiveFreePathLazy m k C first labels activeBases s,
              primedOddActiveFreePathNext m k C first labels activeBases s),
            primedOddComplementPath m k C first labels activeBases s)) =
      (simpleRandomWalkLaw.restrict (simpleRandomWalk '' A)).map
        (liftIncrementStatisticToPath J) := by
          apply Measure.map_congr
          filter_upwards [ae_restrict_mem hPath] with s hs
          rcases hs with ⟨omega, homega, rfl⟩
          simp only [primedOddActiveFreePathLazy,
            primedOddActiveFreePathNext, primedOddComplementPath,
            liftIncrementStatisticToPath_simpleRandomWalk, J,
            primedOddActiveComplementStatistic,
            primedOddActiveFreeStatistic]
    _ = _ := by simpa only [A, activeBases, J] using hLaw

/-! ### Unprimed-odd terminal tie-left active/complement factorization -/

noncomputable def unprimedOddTerminalComplementStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    (ℕ → Direction) →
      (ComplementStoppedBase (0, 0) labels C activeBases → ℕ) :=
  fun omega ↦
    restrictComplementStoppedBase (0, 0) labels C activeBases
      (stoppedPaperBlockSums (0, 0) labels
        (stoppedPaperBlockVector (0, 0) labels
          (actualOddStoppedVector m k labels terminal
            (unprimedOddSourceConstraint m k C labels terminal) omega)))

theorem measurable_unprimedOddTerminalComplementStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (terminal : IncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    Measurable (unprimedOddTerminalComplementStatistic
      m k C labels terminal activeBases) := by
  exact (measurable_restrictComplementStoppedBase
    (0, 0) labels C activeBases).comp
      ((measurable_stoppedPaperBlockSums (0, 0) labels).comp
        ((measurable_stoppedPaperBlockVector (0, 0) labels).comp
          (measurable_actualOddStoppedVector m k labels hnondist terminal
            (unprimedOddSourceConstraint m k C labels terminal))))

noncomputable def unprimedOddTerminalActiveComplementStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    (ℕ → Direction) →
      ((ActiveFreeStoppedBase (0, 0) labels C activeBases → ℕ) ×
        Direction) ×
      (ComplementStoppedBase (0, 0) labels C activeBases → ℕ) :=
  fun omega ↦
    ((restrictActiveFreeStoppedBase (0, 0) labels C activeBases
          (stoppedPaperBlockSums (0, 0) labels
            (stoppedPaperBlockVector (0, 0) labels
              (actualOddStoppedVector m k labels terminal
                (unprimedOddSourceConstraint m k C labels terminal) omega))),
        incrementShiftAfter (stoppedCompletionTime m k) omega 0),
      unprimedOddTerminalComplementStatistic
        m k C labels terminal activeBases omega)

theorem measurable_unprimedOddTerminalActiveComplementStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (terminal : IncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    Measurable (unprimedOddTerminalActiveComplementStatistic
      m k C labels terminal activeBases) := by
  exact (measurable_unprimedOddActiveFreeStatistic
    m k C labels hnondist terminal activeBases).prodMk
      (measurable_unprimedOddTerminalComplementStatistic
        m k C labels hnondist terminal activeBases)

theorem unprimedOdd_tieLeftWinner_active_complement_direction_hasLaw
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
    (hne : (actualAdmissibleOddStoppedVectors m k labels terminal
      (unprimedOddSourceConstraint m k C labels terminal)).Nonempty)
    (candidateBases : Finset (StoppedExternalBase (0, 0) labels)) :
    let activeBases := unprimedOddTieLeftWinnerBases labels
      (unprimedOddTerminalExternalRight labels terminal) candidateBases
    HasLaw
      (unprimedOddTerminalActiveComplementStatistic
        m k C labels terminal activeBases)
      (((sourceTruncatedProfileMeasure m
          (activeFreeStoppedShape (0, 0) labels C activeBases)).prod
            directionLaw).prod
        (stoppedMixedComplementMeasure (0, 0) labels m C activeBases
          (stoppedExternalLeft (0, 0) labels)
          (unprimedOddTerminalExternalRight labels terminal)))
      incrementLaw[|
        actualOddStoppedVectorEvent m k labels terminal
          (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C] := by
  dsimp only
  let activeBases := unprimedOddTieLeftWinnerBases labels
    (unprimedOddTerminalExternalRight labels terminal) candidateBases
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
    simpa only [E, A, X] using
      unprimedOdd_source_hasLaw m k C labels hnondist terminal hm hk hfree
  have hjoint : HasLaw
      (fun omega ↦ (X omega, incrementShiftAfter tau omega 0))
      (((HLOZUrn.runVectorMeasure (q + 1))[|
        (actualAdmissibleOddStoppedVectors
          m k labels terminal E : Set _)]).prod directionLaw)
      incrementLaw[|A] := by
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
  have hgrouped :=
    actualAdmissible_unprimedOddSourceConstraint_eq_mixedBlockPreimage
      m k C labels terminal hm hcard hfree hoff hterminal
  have hpos := mixedCoordinatePos_of_grouped_nonempty
    (0, 0) labels m C (stoppedExternalLeft (0, 0) labels)
      (unprimedOddTerminalExternalRight labels terminal)
      (actualAdmissibleOddStoppedVectors m k labels terminal E)
      (by simpa only [E] using hgrouped) hne
  have h := activeFree_complement_capped_hasLaw_of_joint
    (0, 0) labels m C activeBases
      (stoppedExternalLeft (0, 0) labels)
      (unprimedOddTerminalExternalRight labels terminal)
      (actualAdmissibleOddStoppedVectors m k labels terminal E)
      incrementLaw[|A] X
      (fun omega ↦ incrementShiftAfter tau omega 0)
      hjoint (by simpa only [E] using hgrouped) hpos
  have hwinning : ∀ b : ActiveFreeStoppedBase (0, 0) labels C
      activeBases,
      activeFreeCapProfile (0, 0) labels C activeBases
          (stoppedExternalLeft (0, 0) labels)
          (unprimedOddTerminalExternalRight labels terminal) b =
        activeFreeStoppedShape (0, 0) labels C activeBases b := by
    intro b
    exact unprimedOddTieLeftWinnerBases_cap_eq_shape labels C
      (unprimedOddTerminalExternalRight labels terminal) candidateBases b
  rw [sourceCappedProfileMeasure_eq_truncated m
    (activeFreeStoppedShape (0, 0) labels C activeBases)
    (activeFreeCapProfile (0, 0) labels C activeBases
      (stoppedExternalLeft (0, 0) labels)
      (unprimedOddTerminalExternalRight labels terminal)) hwinning] at h
  change HasLaw
    (unprimedOddTerminalActiveComplementStatistic
      m k C labels terminal activeBases)
    (((sourceTruncatedProfileMeasure m
        (activeFreeStoppedShape (0, 0) labels C activeBases)).prod
          directionLaw).prod
      (stoppedMixedComplementMeasure (0, 0) labels m C activeBases
        (stoppedExternalLeft (0, 0) labels)
        (unprimedOddTerminalExternalRight labels terminal)))
    incrementLaw[|A] at h
  simpa only [A, activeBases] using h

noncomputable def unprimedOddTerminalComplementPath {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    (ℕ → Site) → ComplementStoppedBase (0, 0) labels C activeBases → ℕ :=
  fun s ↦ (liftIncrementStatisticToPath
    (unprimedOddTerminalActiveComplementStatistic
      m k C labels terminal activeBases) s).2

theorem measurable_unprimedOddTerminalComplementPath {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (terminal : IncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    Measurable (unprimedOddTerminalComplementPath
      m k C labels terminal activeBases) :=
  measurable_snd.comp (measurable_liftIncrementStatisticToPath
    (measurable_unprimedOddTerminalActiveComplementStatistic
      m k C labels hnondist terminal activeBases))

theorem unprimedOdd_tieLeftWinner_active_complement_path_map_law
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
    (hne : (actualAdmissibleOddStoppedVectors m k labels terminal
      (unprimedOddSourceConstraint m k C labels terminal)).Nonempty)
    (candidateBases : Finset (StoppedExternalBase (0, 0) labels)) :
    let activeBases := unprimedOddTieLeftWinnerBases labels
      (unprimedOddTerminalExternalRight labels terminal) candidateBases
    (simpleRandomWalkLaw.restrict
        (simpleRandomWalk ''
          (actualOddStoppedVectorEvent m k labels terminal
              (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C))).map
        (fun s ↦
          ((unprimedOddActiveFreePathLazy m k C labels terminal activeBases s,
              unprimedOddActiveFreePathNext m k C labels terminal
                activeBases s),
            unprimedOddTerminalComplementPath m k C labels terminal
              activeBases s)) =
      simpleRandomWalkLaw
          (simpleRandomWalk ''
            (actualOddStoppedVectorEvent m k labels terminal
                (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C)) •
        (((sourceTruncatedProfileMeasure m
          (activeFreeStoppedShape (0, 0) labels C activeBases)).prod
            directionLaw).prod
          (stoppedMixedComplementMeasure (0, 0) labels m C activeBases
            (stoppedExternalLeft (0, 0) labels)
            (unprimedOddTerminalExternalRight labels terminal))) := by
  dsimp only
  let activeBases := unprimedOddTieLeftWinnerBases labels
    (unprimedOddTerminalExternalRight labels terminal) candidateBases
  let A := actualOddStoppedVectorEvent m k labels terminal
    (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C
  let J := unprimedOddTerminalActiveComplementStatistic
    m k C labels terminal activeBases
  have hA : MeasurableSet A := by
    dsimp only [A]
    rw [unprimedOdd_source_partition m k C labels terminal hm hk hfree]
    unfold actualOddStoppedVectorEvent
    exact MeasurableSet.iUnion fun v ↦ MeasurableSet.iUnion fun _ ↦
      measurableSet_stoppedPrefixAtom
        (reconstructedOddStoppedPrefix labels v terminal)
  have hJ : Measurable J :=
    measurable_unprimedOddTerminalActiveComplementStatistic
      m k C labels hnondist terminal activeBases
  have hLaw := liftIncrementStatistic_path_map_law hA hJ
    (unprimedOdd_tieLeftWinner_active_complement_direction_hasLaw
      m k C labels hnondist terminal hm hk hcard hfree hoff hterminal hne
        candidateBases)
  have hPath : MeasurableSet (simpleRandomWalk '' A) :=
    HLOZSourceInstantiation.measurableEmbedding_simpleRandomWalk
      |>.measurableSet_image.2 hA
  calc
    (simpleRandomWalkLaw.restrict (simpleRandomWalk '' A)).map
        (fun s ↦
          ((unprimedOddActiveFreePathLazy m k C labels terminal activeBases s,
              unprimedOddActiveFreePathNext m k C labels terminal
                activeBases s),
            unprimedOddTerminalComplementPath m k C labels terminal
              activeBases s)) =
      (simpleRandomWalkLaw.restrict (simpleRandomWalk '' A)).map
        (liftIncrementStatisticToPath J) := by
          apply Measure.map_congr
          filter_upwards [ae_restrict_mem hPath] with s hs
          rcases hs with ⟨omega, homega, rfl⟩
          simp only [unprimedOddActiveFreePathLazy,
            unprimedOddActiveFreePathNext,
            unprimedOddTerminalComplementPath,
            liftIncrementStatisticToPath_simpleRandomWalk, J,
            unprimedOddTerminalActiveComplementStatistic,
            unprimedOddActiveFreeStatistic]
    _ = _ := by simpa only [A, activeBases, J] using hLaw

/-! ### Primed-even terminal strict-right active/complement factorization -/

noncomputable def primedEvenTerminalComplementStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair) (terminal : IncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    (ℕ → Direction) →
      (ComplementStoppedBase (primedInitialBase first) labels C
        activeBases → ℕ) :=
  fun omega ↦
    restrictComplementStoppedBase (primedInitialBase first) labels C
      activeBases
      (stoppedPaperBlockSums (primedInitialBase first) labels
        (stoppedPaperBlockVector (primedInitialBase first) labels
          (actualPrimedTerminalVector m k first labels terminal
            (primedEvenSourceConstraint m k C first labels terminal) omega)))

theorem measurable_primedEvenTerminalComplementStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (terminal : IncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    Measurable (primedEvenTerminalComplementStatistic
      m k C first labels terminal activeBases) := by
  exact (measurable_restrictComplementStoppedBase
    (primedInitialBase first) labels C activeBases).comp
      ((measurable_stoppedPaperBlockSums
        (primedInitialBase first) labels).comp
        ((measurable_stoppedPaperBlockVector
          (primedInitialBase first) labels).comp
          (measurable_actualPrimedTerminalVector
            m k first labels hnondist terminal
              (primedEvenSourceConstraint m k C first labels terminal))))

noncomputable def primedEvenTerminalActiveComplementStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair) (terminal : IncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    (ℕ → Direction) →
      ((ActiveFreeStoppedBase (primedInitialBase first) labels C
        activeBases → ℕ) × Direction) ×
      (ComplementStoppedBase (primedInitialBase first) labels C
        activeBases → ℕ) :=
  fun omega ↦
    (primedEvenActiveFreeStatistic
        m k C first labels terminal activeBases omega,
      primedEvenTerminalComplementStatistic
        m k C first labels terminal activeBases omega)

theorem measurable_primedEvenTerminalActiveComplementStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (terminal : IncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    Measurable (primedEvenTerminalActiveComplementStatistic
      m k C first labels terminal activeBases) := by
  exact (measurable_primedEvenActiveFreeStatistic
    m k C first labels hnondist terminal activeBases).prodMk
      (measurable_primedEvenTerminalComplementStatistic
        m k C first labels hnondist terminal activeBases)

theorem primedEven_strictRightWinner_active_complement_direction_hasLaw
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
    (hne : (actualAdmissiblePrimedTerminalVectors
      m k first labels terminal
        (primedEvenSourceConstraint m k C first labels terminal)).Nonempty)
    (candidateBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    let activeBases := primedEvenStrictRightWinnerBases first labels
      (primedEvenTerminalExternalLeft first labels terminal) candidateBases
    HasLaw
      (primedEvenTerminalActiveComplementStatistic
        m k C first labels terminal activeBases)
      (((sourceTruncatedProfileMeasure m
          (activeFreeStoppedShape (primedInitialBase first) labels C
            activeBases)).prod directionLaw).prod
        (stoppedMixedComplementMeasure (primedInitialBase first) labels m C
          activeBases (primedEvenTerminalExternalLeft first labels terminal)
            (primedStoppedExternalRight first labels)))
      incrementLaw[|
        actualPrimedTerminalVectorEvent m k first labels terminal
          (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C] := by
  dsimp only
  let externalLeft := primedEvenTerminalExternalLeft first labels terminal
  let activeBases := primedEvenStrictRightWinnerBases first labels
    externalLeft candidateBases
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
  have hgrouped :=
    actualAdmissible_primedEvenSourceConstraint_eq_mixedBlockPreimage
      m k C first labels terminal hm hcard hfree hoff hterminal
  have hpos := mixedCoordinatePos_of_grouped_nonempty
    (primedInitialBase first) labels m C externalLeft
      (primedStoppedExternalRight first labels)
      (actualAdmissiblePrimedTerminalVectors
        m k first labels terminal E)
      (by simpa only [E, externalLeft] using hgrouped) hne
  have h := activeFree_complement_capped_hasLaw_of_joint
    (primedInitialBase first) labels m C activeBases externalLeft
      (primedStoppedExternalRight first labels)
      (actualAdmissiblePrimedTerminalVectors
        m k first labels terminal E)
      incrementLaw[|A] X
      (fun omega ↦ incrementShiftAfter tau omega 0)
      hjoint (by simpa only [E, externalLeft] using hgrouped) hpos
  have hwinning : ∀ b : ActiveFreeStoppedBase
      (primedInitialBase first) labels C activeBases,
      activeFreeCapProfile (primedInitialBase first) labels C activeBases
          externalLeft (primedStoppedExternalRight first labels) b =
        activeFreeStoppedShape (primedInitialBase first) labels C
          activeBases b := by
    intro b
    exact primedEvenStrictRightWinnerBases_cap_eq_shape first labels C
      externalLeft candidateBases b
  rw [sourceCappedProfileMeasure_eq_truncated m
    (activeFreeStoppedShape (primedInitialBase first) labels C activeBases)
    (activeFreeCapProfile (primedInitialBase first) labels C activeBases
      externalLeft (primedStoppedExternalRight first labels)) hwinning] at h
  change HasLaw
    (primedEvenTerminalActiveComplementStatistic
      m k C first labels terminal activeBases)
    (((sourceTruncatedProfileMeasure m
        (activeFreeStoppedShape (primedInitialBase first) labels C
          activeBases)).prod directionLaw).prod
      (stoppedMixedComplementMeasure (primedInitialBase first) labels m C
        activeBases externalLeft (primedStoppedExternalRight first labels)))
    incrementLaw[|A] at h
  simpa only [A, activeBases, externalLeft] using h

noncomputable def primedEvenTerminalComplementPath {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair) (terminal : IncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    (ℕ → Site) → ComplementStoppedBase (primedInitialBase first) labels C
      activeBases → ℕ :=
  fun s ↦ (liftIncrementStatisticToPath
    (primedEvenTerminalActiveComplementStatistic
      m k C first labels terminal activeBases) s).2

theorem measurable_primedEvenTerminalComplementPath {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (terminal : IncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    Measurable (primedEvenTerminalComplementPath
      m k C first labels terminal activeBases) :=
  measurable_snd.comp (measurable_liftIncrementStatisticToPath
    (measurable_primedEvenTerminalActiveComplementStatistic
      m k C first labels hnondist terminal activeBases))

theorem primedEven_strictRightWinner_active_complement_path_map_law
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
    (hne : (actualAdmissiblePrimedTerminalVectors
      m k first labels terminal
        (primedEvenSourceConstraint m k C first labels terminal)).Nonempty)
    (candidateBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    let externalLeft := primedEvenTerminalExternalLeft first labels terminal
    let activeBases := primedEvenStrictRightWinnerBases first labels
      externalLeft candidateBases
    (simpleRandomWalkLaw.restrict
        (simpleRandomWalk ''
          (actualPrimedTerminalVectorEvent m k first labels terminal
              (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C))).map
        (fun s ↦
          ((primedEvenActiveFreePathLazy
              m k C first labels terminal activeBases s,
            primedEvenActiveFreePathNext
              m k C first labels terminal activeBases s),
            primedEvenTerminalComplementPath
              m k C first labels terminal activeBases s)) =
      simpleRandomWalkLaw
          (simpleRandomWalk ''
            (actualPrimedTerminalVectorEvent m k first labels terminal
                (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C)) •
        (((sourceTruncatedProfileMeasure m
          (activeFreeStoppedShape (primedInitialBase first) labels C
            activeBases)).prod directionLaw).prod
          (stoppedMixedComplementMeasure (primedInitialBase first) labels m C
            activeBases externalLeft
              (primedStoppedExternalRight first labels))) := by
  dsimp only
  let externalLeft := primedEvenTerminalExternalLeft first labels terminal
  let activeBases := primedEvenStrictRightWinnerBases first labels
    externalLeft candidateBases
  let A := actualPrimedTerminalVectorEvent m k first labels terminal
    (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C
  let J := primedEvenTerminalActiveComplementStatistic
    m k C first labels terminal activeBases
  have hA : MeasurableSet A := by
    dsimp only [A]
    rw [primedEven_source_partition m k C first labels terminal hm hk hfree]
    unfold actualPrimedTerminalVectorEvent
    exact MeasurableSet.iUnion fun v ↦ MeasurableSet.iUnion fun _ ↦
      measurableSet_stoppedPrefixAtom
        (reconstructedPrimedTerminalStoppedPrefix first labels v terminal)
  have hJ : Measurable J :=
    measurable_primedEvenTerminalActiveComplementStatistic
      m k C first labels hnondist terminal activeBases
  have hLaw := liftIncrementStatistic_path_map_law hA hJ
    (primedEven_strictRightWinner_active_complement_direction_hasLaw
      m k C first labels hnondist terminal hm hk hcard hfree hoff hterminal
        hne candidateBases)
  have hPath : MeasurableSet (simpleRandomWalk '' A) :=
    HLOZSourceInstantiation.measurableEmbedding_simpleRandomWalk
      |>.measurableSet_image.2 hA
  calc
    (simpleRandomWalkLaw.restrict (simpleRandomWalk '' A)).map
        (fun s ↦
          ((primedEvenActiveFreePathLazy
              m k C first labels terminal activeBases s,
            primedEvenActiveFreePathNext
              m k C first labels terminal activeBases s),
            primedEvenTerminalComplementPath
              m k C first labels terminal activeBases s)) =
      (simpleRandomWalkLaw.restrict (simpleRandomWalk '' A)).map
        (liftIncrementStatisticToPath J) := by
          apply Measure.map_congr
          filter_upwards [ae_restrict_mem hPath] with s hs
          rcases hs with ⟨omega, homega, rfl⟩
          simp only [primedEvenActiveFreePathLazy,
            primedEvenActiveFreePathNext,
            primedEvenTerminalComplementPath,
            liftIncrementStatisticToPath_simpleRandomWalk, J,
            primedEvenTerminalActiveComplementStatistic]
    _ = _ := by simpa only [A, activeBases, externalLeft, J] using hLaw

/-! ### Honest refinement by the preceding source history -/

/-- Intersecting a stopped source atom with a path event known at the same
creation time preserves fiberwise measurability in the iid past.  The
finiteness premise is essential because `stoppedCreationTime` uses
`WithTop.untopA`. -/
theorem measurableSet_sourcePast_inter_pathStoppedEvent
    (m k n : ℕ) (A : Set (ℕ → Direction)) (E : Set (ℕ → Site))
    (hfinite : A ⊆ {omega | firstKSitesReachLevel m k
      (simpleRandomWalk omega) ≠ ⊤})
    (hA : MeasurableSet[iidHistory (X := Direction) n]
      (A ∩ {omega | stoppedCreationTime m k omega = n}))
    (hE : MeasurableSet[iidHistory (X := Direction) n]
      (simpleRandomWalk ⁻¹' E ∩ {omega | firstKSitesReachLevel m k
        (simpleRandomWalk omega) = n})) :
    MeasurableSet[iidHistory (X := Direction) n]
      ((A ∩ simpleRandomWalk ⁻¹' E) ∩
        {omega | stoppedCreationTime m k omega = n}) := by
  have heq : (A ∩ simpleRandomWalk ⁻¹' E) ∩
        {omega | stoppedCreationTime m k omega = n} =
      (A ∩ {omega | stoppedCreationTime m k omega = n}) ∩
        (simpleRandomWalk ⁻¹' E ∩
          {omega | firstKSitesReachLevel m k
            (simpleRandomWalk omega) = n}) := by
    ext omega
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hAOmega, hEOmega⟩, htau⟩
      refine ⟨⟨hAOmega, htau⟩, hEOmega, ?_⟩
      have hTfinite := hfinite hAOmega
      let T := firstKSitesReachLevel m k (simpleRandomWalk omega)
      have hcoe : ((T.untopA : ℕ) : WithTop ℕ) = T := by
        rw [WithTop.untopA_eq_untop hTfinite]
        exact WithTop.coe_untop T hTfinite
      change T = (n : WithTop ℕ)
      change T.untopA = n at htau
      rw [← hcoe]
      exact_mod_cast htau
    · rintro ⟨⟨hAOmega, htau⟩, hEOmega, _hT⟩
      exact ⟨⟨hAOmega, hEOmega⟩, htau⟩
  rw [heq]
  exact hA.inter hE

/-- The corresponding past-intersection lemma for full-terminal atoms.  A
full terminal pair is known only at the completion clock `T+1`; the path
event itself is lifted monotonically from the history at `T`. -/
theorem measurableSet_sourcePastAfterCompletion_inter_pathStoppedEvent
    (m k n : ℕ) (A : Set (ℕ → Direction)) (E : Set (ℕ → Site))
    (hfinite : A ⊆ {omega | firstKSitesReachLevel m k
      (simpleRandomWalk omega) ≠ ⊤})
    (hA : MeasurableSet[iidHistory (X := Direction) n]
      (A ∩ {omega | stoppedCompletionTime m k omega = n}))
    (hE : ∀ t, MeasurableSet[iidHistory (X := Direction) t]
      (simpleRandomWalk ⁻¹' E ∩ {omega | firstKSitesReachLevel m k
        (simpleRandomWalk omega) = t})) :
    MeasurableSet[iidHistory (X := Direction) n]
      ((A ∩ simpleRandomWalk ⁻¹' E) ∩
        {omega | stoppedCompletionTime m k omega = n}) := by
  cases n with
  | zero =>
      have hempty : (A ∩ simpleRandomWalk ⁻¹' E) ∩
          {omega | stoppedCompletionTime m k omega = 0} = ∅ := by
        ext omega
        simp [stoppedCompletionTime]
      rw [hempty]
      exact @MeasurableSet.empty _ (iidHistory (X := Direction) 0)
  | succ t =>
      have hEt : MeasurableSet[iidHistory (X := Direction) (t + 1)]
          (simpleRandomWalk ⁻¹' E ∩
            {omega | firstKSitesReachLevel m k
              (simpleRandomWalk omega) = t}) :=
        iidHistory_mono_local (Nat.le_succ t) _ (hE t)
      have heq : (A ∩ simpleRandomWalk ⁻¹' E) ∩
            {omega | stoppedCompletionTime m k omega = t + 1} =
          (A ∩ {omega | stoppedCompletionTime m k omega = t + 1}) ∩
            (simpleRandomWalk ⁻¹' E ∩
              {omega | firstKSitesReachLevel m k
                (simpleRandomWalk omega) = t}) := by
        ext omega
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨⟨hAOmega, hEOmega⟩, hcompletion⟩
          refine ⟨⟨hAOmega, hcompletion⟩, hEOmega, ?_⟩
          have hTfinite := hfinite hAOmega
          let T := firstKSitesReachLevel m k (simpleRandomWalk omega)
          have hcoe : ((T.untopA : ℕ) : WithTop ℕ) = T := by
            rw [WithTop.untopA_eq_untop hTfinite]
            exact WithTop.coe_untop T hTfinite
          have huntop : T.untopA = t := by
            change T.untopA + 1 = t + 1 at hcompletion
            omega
          change T = (t : WithTop ℕ)
          rw [← hcoe]
          exact_mod_cast huntop
        · rintro ⟨⟨hAOmega, _hcompletion⟩, hEOmega, hT⟩
          refine ⟨⟨hAOmega, hEOmega⟩, ?_⟩
          unfold stoppedCompletionTime stoppedCreationTime
          rw [hT]
          rfl
      rw [heq]
      exact hA.inter hEt

/-- A countable union of iid-history fibers is ordinarily measurable. -/
theorem measurableSet_of_iidHistory_fibers_nat
    (tau : (ℕ → Direction) → ℕ) (A : Set (ℕ → Direction))
    (hA : ∀ n, MeasurableSet[iidHistory (X := Direction) n]
      (A ∩ {omega | tau omega = n})) :
    MeasurableSet A := by
  have heq : A = ⋃ n : ℕ, A ∩ {omega | tau omega = n} := by
    ext omega
    constructor
    · intro h
      exact Set.mem_iUnion_of_mem (tau omega) ⟨h, rfl⟩
    · intro h
      rcases Set.mem_iUnion.mp h with ⟨n, hn⟩
      exact hn.1
  rw [heq]
  exact MeasurableSet.iUnion fun n ↦ iidHistory_le n _ (hA n)

/-- The ordered level-`m` creation sites through `T_m^k`.  Unlike the
unordered creation finset, this records the source history needed by the
sequential Proposition-4.7 decomposition. -/
noncomputable def orderedCreationSites
    (m k : ℕ) (s : ℕ → Site) : Fin k → Site :=
  fun j ↦ levelCreationSite s m (j.1 + 1)

theorem measurable_levelCreationSite_at_firstK
    (m : ℕ) {j k : ℕ} (hjk : j ≤ k) :
    Measurable[(isStoppingTime_firstKSitesReachLevel m k).measurableSpace]
      (fun s ↦ levelCreationSite s m j) := by
  let hj := isStoppingTime_firstKSitesReachLevel m j
  let hk := isStoppingTime_firstKSitesReachLevel m k
  exact (HLOZLemma410Race.measurable_stoppedCoordinate hj).mono
    (hj.measurableSpace_mono hk (fun s ↦
      firstKSitesReachLevel_mono_k s m hjk)) le_rfl

theorem measurable_orderedCreationSites (m k : ℕ) :
    Measurable[(isStoppingTime_firstKSitesReachLevel m k).measurableSpace]
      (orderedCreationSites m k) := by
  let _ : MeasurableSpace (ℕ → Site) :=
    (isStoppingTime_firstKSitesReachLevel m k).measurableSpace
  change Measurable (orderedCreationSites m k)
  apply measurable_pi_lambda
  intro j
  exact measurable_levelCreationSite_at_firstK m (by omega)

def orderedCreationSitesEvent
    (m k : ℕ) (c : Fin k → Site) : Set (ℕ → Site) :=
  {s | orderedCreationSites m k s = c}

theorem measurableSet_orderedCreationSitesEvent
    (m k : ℕ) (c : Fin k → Site) :
    MeasurableSet[(isStoppingTime_firstKSitesReachLevel m k).measurableSpace]
      (orderedCreationSitesEvent m k c) := by
  exact measurableSet_eq_fun (measurable_orderedCreationSites m k)
    measurable_const

/-- The complete refinement visible at the current threshold: the ordered
creation sites together with all preceding screens for a chosen profile
family. -/
noncomputable def orderedProfileHistoryEvent
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (c : Fin (stageNumber r) → Site) : Set (ℕ → Site) :=
  orderedCreationSitesEvent m (stageNumber r) c ∩
    prop47History profiles cStar m i a r.1

/-- The auxiliary pairing-adapted instance retained for compatibility with
the original stopped-history development. -/
noncomputable def orderedCanonicalHistoryEvent
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (c : Fin (stageNumber r) → Site) : Set (ℕ → Site) :=
  orderedProfileHistoryEvent canonicalProfiles canonicalCStar m i a r c

theorem measurableSet_orderedProfileHistoryEvent_at_threshold
    (profiles : Fin 6 → ExternalProfilePair)
    (hadapt : OneStepAdaptedProfiles profiles) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (c : Fin (stageNumber r) → Site) (hm : 0 < m) :
    MeasurableSet[(isStoppingTime_firstKSitesReachLevel
      m (stageNumber r)).measurableSpace]
      (orderedProfileHistoryEvent profiles cStar m i a r c) := by
  apply (measurableSet_orderedCreationSitesEvent
    m (stageNumber r) c).inter
  convert measurableSet_prop47History_at_threshold
    profiles hadapt cStar m i a r.1 (by omega) hm using 1 <;>
    simp [stageNumber]

theorem measurableSet_orderedProfileHistoryEvent
    (profiles : Fin 6 → ExternalProfilePair)
    (hadapt : OneStepAdaptedProfiles profiles) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (c : Fin (stageNumber r) → Site) (hm : 0 < m) :
    MeasurableSet (orderedProfileHistoryEvent profiles cStar m i a r c) := by
  let hT := isStoppingTime_firstKSitesReachLevel m (stageNumber r)
  exact hT.measurableSpace_le _
    (measurableSet_orderedProfileHistoryEvent_at_threshold
      profiles hadapt cStar m i a r c hm)

theorem measurableSet_orderedCanonicalHistoryEvent_at_threshold
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (c : Fin (stageNumber r) → Site) (hm : 0 < m) :
    MeasurableSet[(isStoppingTime_firstKSitesReachLevel
      m (stageNumber r)).measurableSpace]
      (orderedCanonicalHistoryEvent m i a r c) := by
  exact measurableSet_orderedProfileHistoryEvent_at_threshold
    canonicalProfiles canonicalProfiles_oneStepAdapted canonicalCStar
      m i a r c hm

theorem measurableSet_orderedProfileHistoryEvent_stoppedFiber
    (profiles : Fin 6 → ExternalProfilePair)
    (hadapt : OneStepAdaptedProfiles profiles) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (c : Fin (stageNumber r) → Site) (hm : 0 < m) (n : ℕ) :
    MeasurableSet[iidHistory (X := Direction) n]
      (simpleRandomWalk ⁻¹'
          orderedProfileHistoryEvent profiles cStar m i a r c ∩
        {omega | firstKSitesReachLevel m (stageNumber r)
          (simpleRandomWalk omega) = n}) := by
  exact Erdos1166.measurableSet_pathStoppedEvent_inter_fiber_iidHistory
    (isStoppingTime_firstKSitesReachLevel m (stageNumber r))
    (orderedProfileHistoryEvent profiles cStar m i a r c)
    (measurableSet_orderedProfileHistoryEvent_at_threshold
      profiles hadapt cStar m i a r c hm) n

theorem measurableSet_orderedCanonicalHistoryEvent_stoppedFiber
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (c : Fin (stageNumber r) → Site) (hm : 0 < m) (n : ℕ) :
    MeasurableSet[iidHistory (X := Direction) n]
      (simpleRandomWalk ⁻¹' orderedCanonicalHistoryEvent m i a r c ∩
        {omega | firstKSitesReachLevel m (stageNumber r)
          (simpleRandomWalk omega) = n}) := by
  exact measurableSet_orderedProfileHistoryEvent_stoppedFiber
    canonicalProfiles canonicalProfiles_oneStepAdapted canonicalCStar
      m i a r c hm n

noncomputable def unprimedEvenOrderedRefinedAtom {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (c : Fin k → Site) : Set (ℕ → Direction) :=
  (actualStoppedVectorEvent m k labels (stoppedRunVectorBox q m) ∩
    stoppedSourceCondition m k C) ∩
      simpleRandomWalk ⁻¹' orderedCreationSitesEvent m k c

theorem unprimedEvenOrderedRefinedAtom_stoppedPast {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (c : Fin k → Site)
    (hnondist : ∀ j, labels j ≠ distinguishedIncrementPair)
    (hm : 0 < m) (hk : 0 < k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (n : ℕ) :
    MeasurableSet[iidHistory (X := Direction) n]
      (unprimedEvenOrderedRefinedAtom m k C labels c ∩
        {omega | stoppedCreationTime m k omega = n}) := by
  let A := actualStoppedVectorEvent m k labels (stoppedRunVectorBox q m) ∩
    stoppedSourceCondition m k C
  let O := simpleRandomWalk ⁻¹' orderedCreationSitesEvent m k c
  let tau := stoppedCreationTime m k
  have hA : MeasurableSet[iidHistory (X := Direction) n]
      (A ∩ {omega | tau omega = n}) := by
    simpa only [A, tau] using
      unprimedEven_sourcePast m k C labels hnondist hm hk hfree n
  have hO : MeasurableSet[iidHistory (X := Direction) n]
      (O ∩ {omega | firstKSitesReachLevel m k
        (simpleRandomWalk omega) = n}) := by
    simpa only [O] using
      Erdos1166.measurableSet_pathStoppedEvent_inter_fiber_iidHistory
        (isStoppingTime_firstKSitesReachLevel m k)
        (orderedCreationSitesEvent m k c)
        (measurableSet_orderedCreationSitesEvent m k c) n
  have heq : (A ∩ O) ∩ {omega | tau omega = n} =
      (A ∩ {omega | tau omega = n}) ∩
        (O ∩ {omega | firstKSitesReachLevel m k
          (simpleRandomWalk omega) = n}) := by
    ext omega
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hAOmega, hOOmega⟩, htau⟩
      refine ⟨⟨hAOmega, htau⟩, hOOmega, ?_⟩
      have hfinite : firstKSitesReachLevel m k
          (simpleRandomWalk omega) ≠ ⊤ :=
        ne_top_of_lt hAOmega.2.1
      let T := firstKSitesReachLevel m k (simpleRandomWalk omega)
      have hcoe : ((T.untopA : ℕ) : WithTop ℕ) = T := by
        rw [WithTop.untopA_eq_untop hfinite]
        exact WithTop.coe_untop T hfinite
      change T = (n : WithTop ℕ)
      change T.untopA = n at htau
      rw [← hcoe]
      exact_mod_cast htau
    · rintro ⟨⟨hAOmega, htau⟩, hOOmega, _hT⟩
      exact ⟨⟨hAOmega, hOOmega⟩, htau⟩
  change MeasurableSet[iidHistory (X := Direction) n]
    ((A ∩ O) ∩ {omega | tau omega = n})
  rw [heq]
  exact hA.inter hO

/-- The literal raw stopped source atom refined by the complete preceding
canonical history.  No assertion is made that this event is a complement-
block preimage: that stronger claim is false for the coarse unordered-`C`
atom. -/
noncomputable def unprimedEvenHistoryRefinedAtom {q : ℕ}
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (C : Finset Site) (labels : Fin q → IncrementPair) :
    Set (ℕ → Direction) :=
  (actualStoppedVectorEvent m (stageNumber r) labels
      (stoppedRunVectorBox q m) ∩
    stoppedSourceCondition m (stageNumber r) C) ∩
  simpleRandomWalk ⁻¹'
    prop47History canonicalProfiles canonicalCStar m i a r.1

/-- The refined atom is genuinely known at `T_m^(stageNumber r)`, fiber by
fiber in the iid increment history.  This is the source-valid conditioning
sigma-field for a direct history-intersected Proposition-4.9 estimate. -/
theorem unprimedEvenHistoryRefinedAtom_stoppedPast {q : ℕ}
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ j, labels j ≠ distinguishedIncrementPair)
    (hm : 0 < m)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (n : ℕ) :
    MeasurableSet[iidHistory (X := Direction) n]
      (unprimedEvenHistoryRefinedAtom m i a r C labels ∩
        {omega | stoppedCreationTime m (stageNumber r) omega = n}) := by
  let k := stageNumber r
  let A := actualStoppedVectorEvent m k labels (stoppedRunVectorBox q m) ∩
    stoppedSourceCondition m k C
  let H := simpleRandomWalk ⁻¹'
    prop47History canonicalProfiles canonicalCStar m i a r.1
  let tau := stoppedCreationTime m k
  have hA : MeasurableSet[iidHistory (X := Direction) n]
      (A ∩ {omega | tau omega = n}) := by
    simpa only [A, tau] using unprimedEven_sourcePast
      m k C labels hnondist hm (by simp [k, stageNumber]) hfree n
  have hH : MeasurableSet[iidHistory (X := Direction) n]
      (H ∩ {omega | firstKSitesReachLevel m k
        (simpleRandomWalk omega) = n}) := by
    simpa only [H, k] using
      measurableSet_canonicalProp47History_stoppedFiber_iidHistory
        m i a r n hm
  have heq : (A ∩ H) ∩ {omega | tau omega = n} =
      (A ∩ {omega | tau omega = n}) ∩
        (H ∩ {omega | firstKSitesReachLevel m k
          (simpleRandomWalk omega) = n}) := by
    ext omega
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hAOmega, hHOmega⟩, htau⟩
      refine ⟨⟨hAOmega, htau⟩, hHOmega, ?_⟩
      have hfinite := prop47History_subset_thresholdFinite
        canonicalProfiles canonicalCStar m i a r hHOmega
      let T := firstKSitesReachLevel m k (simpleRandomWalk omega)
      have hcoe : ((T.untopA : ℕ) : WithTop ℕ) = T := by
        rw [WithTop.untopA_eq_untop hfinite]
        exact WithTop.coe_untop T hfinite
      change T = (n : WithTop ℕ)
      change T.untopA = n at htau
      rw [← hcoe]
      exact_mod_cast htau
    · rintro ⟨⟨hAOmega, htau⟩, hHOmega, _hT⟩
      exact ⟨⟨hAOmega, hHOmega⟩, htau⟩
  change MeasurableSet[iidHistory (X := Direction) n]
    ((A ∩ H) ∩ {omega | tau omega = n})
  rw [heq]
  exact hA.inter hH

/-- The literal source refinement obtained by fixing both the ordered
creation sites and the complete preceding screening history.  This is
strictly finer than the raw atom that fixes only the deleted labels and the
unordered creation set. -/
noncomputable def unprimedEvenOrderedHistoryRefinedAtom {q : ℕ}
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (C : Finset Site) (labels : Fin q → IncrementPair)
    (c : Fin (stageNumber r) → Site) : Set (ℕ → Direction) :=
  unprimedEvenOrderedRefinedAtom m (stageNumber r) C labels c ∩
    unprimedEvenHistoryRefinedAtom m i a r C labels

/-- After fixing deleted labels, the ordered creation sites, the unordered
creation set, and the preceding canonical history, the resulting atom is
still measurable in the stopped iid past, fiber by fiber. -/
theorem unprimedEvenOrderedHistoryRefinedAtom_stoppedPast {q : ℕ}
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (C : Finset Site) (labels : Fin q → IncrementPair)
    (c : Fin (stageNumber r) → Site)
    (hnondist : ∀ j, labels j ≠ distinguishedIncrementPair)
    (hm : 0 < m)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (n : ℕ) :
    MeasurableSet[iidHistory (X := Direction) n]
      (unprimedEvenOrderedHistoryRefinedAtom m i a r C labels c ∩
        {omega | stoppedCreationTime m (stageNumber r) omega = n}) := by
  let O := unprimedEvenOrderedRefinedAtom
    m (stageNumber r) C labels c
  let H := unprimedEvenHistoryRefinedAtom m i a r C labels
  let F : Set (ℕ → Direction) :=
    {omega | stoppedCreationTime m (stageNumber r) omega = n}
  have hO : MeasurableSet[iidHistory (X := Direction) n] (O ∩ F) := by
    simpa only [O, F] using unprimedEvenOrderedRefinedAtom_stoppedPast
      m (stageNumber r) C labels c hnondist hm
        (by simp [stageNumber]) hfree n
  have hH : MeasurableSet[iidHistory (X := Direction) n] (H ∩ F) := by
    simpa only [H, F] using unprimedEvenHistoryRefinedAtom_stoppedPast
      m i a r C labels hnondist hm hfree n
  have heq : (O ∩ H) ∩ F = (O ∩ F) ∩ (H ∩ F) := by
    ext omega
    simp only [Set.mem_inter_iff]
    tauto
  change MeasurableSet[iidHistory (X := Direction) n] ((O ∩ H) ∩ F)
  rw [heq]
  exact hO.inter hH

/-- Stopped-past fiber measurability implies ordinary measurability for the
fully refined atom, because its natural stopping time is total as a
`Nat`-valued function (`untopA` is irrelevant off the raw finite atom). -/
theorem measurableSet_unprimedEvenOrderedHistoryRefinedAtom {q : ℕ}
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (C : Finset Site) (labels : Fin q → IncrementPair)
    (c : Fin (stageNumber r) → Site)
    (hnondist : ∀ j, labels j ≠ distinguishedIncrementPair)
    (hm : 0 < m)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C) :
    MeasurableSet
      (unprimedEvenOrderedHistoryRefinedAtom m i a r C labels c) := by
  let A := unprimedEvenOrderedHistoryRefinedAtom m i a r C labels c
  let tau := stoppedCreationTime m (stageNumber r)
  have hfiber (n : ℕ) : MeasurableSet (A ∩ {omega | tau omega = n}) :=
    iidHistory_le n _ (by
      simpa only [A, tau] using
        unprimedEvenOrderedHistoryRefinedAtom_stoppedPast
          m i a r C labels c hnondist hm hfree n)
  have heq : A = ⋃ n : ℕ, A ∩ {omega | tau omega = n} := by
    ext omega
    constructor
    · intro h
      exact Set.mem_iUnion_of_mem (tau omega) ⟨h, rfl⟩
    · intro h
      rcases Set.mem_iUnion.mp h with ⟨n, hn⟩
      exact hn.1
  change MeasurableSet A
  rw [heq]
  exact MeasurableSet.iUnion hfiber

/-- Path-space version of the fully refined source atom. -/
noncomputable def unprimedEvenOrderedHistoryPathAtom {q : ℕ}
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (C : Finset Site) (labels : Fin q → IncrementPair)
    (c : Fin (stageNumber r) → Site) : Set (ℕ → Site) :=
  simpleRandomWalk ''
    unprimedEvenOrderedHistoryRefinedAtom m i a r C labels c

theorem measurableSet_unprimedEvenOrderedHistoryPathAtom {q : ℕ}
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (C : Finset Site) (labels : Fin q → IncrementPair)
    (c : Fin (stageNumber r) → Site)
    (hnondist : ∀ j, labels j ≠ distinguishedIncrementPair)
    (hm : 0 < m)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C) :
    MeasurableSet
      (unprimedEvenOrderedHistoryPathAtom m i a r C labels c) := by
  exact measurableEmbedding_simpleRandomWalk.measurableSet_image.2
    (measurableSet_unprimedEvenOrderedHistoryRefinedAtom
      m i a r C labels c hnondist hm hfree)

/-- The refined path atom really lies in the preceding canonical history.
This records containment only; it deliberately does not identify history as
a preimage of the coarse complement-block statistic. -/
theorem unprimedEvenOrderedHistoryPathAtom_subset_history {q : ℕ}
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (C : Finset Site) (labels : Fin q → IncrementPair)
    (c : Fin (stageNumber r) → Site) :
    unprimedEvenOrderedHistoryPathAtom m i a r C labels c ⊆
      prop47History canonicalProfiles canonicalCStar m i a r.1 := by
  rintro s ⟨omega, homega, rfl⟩
  exact homega.2.2

/-- The increment-space refinement is exactly the coarse stopped atom
intersected on path space with the ordered canonical history. -/
theorem unprimedEvenOrderedHistoryPathAtom_eq_coarse_inter_history {q : ℕ}
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (C : Finset Site) (labels : Fin q → IncrementPair)
    (c : Fin (stageNumber r) → Site) :
    unprimedEvenOrderedHistoryPathAtom m i a r C labels c =
      (simpleRandomWalk ''
          (actualStoppedVectorEvent m (stageNumber r) labels
              (stoppedRunVectorBox q m) ∩
            stoppedSourceCondition m (stageNumber r) C)) ∩
        orderedCanonicalHistoryEvent m i a r c := by
  ext s
  constructor
  · rintro ⟨omega, ⟨⟨hA, hordered⟩, ⟨_hA, hhistory⟩⟩, rfl⟩
    exact ⟨⟨omega, hA, rfl⟩, hordered, hhistory⟩
  · rintro ⟨⟨omega, hA, rfl⟩, hordered, hhistory⟩
    exact ⟨omega, ⟨⟨hA, hordered⟩, ⟨hA, hhistory⟩⟩, rfl⟩

/-! ### The other three X-east terminal-parity/winner branches -/

/-- The exact source estimate deliberately left open by the refined-atom
construction.  Proposition 4.9 must bound the requested phase screen
uniformly on each such atom; measurability and stopped-past adaptedness alone
do not imply this inequality. -/
def RefinedAtomScreenEstimate
    (atom screen : Set (ℕ → Site)) (rate : ℝ≥0∞) : Prop :=
  simpleRandomWalkLaw (atom ∩ screen) ≤
    rate * simpleRandomWalkLaw atom

/-- The exact truncated-product law on a history-refined source atom is the
probabilistic input needed in Proposition 4.9.  The checked finite union over
candidate coordinates and all local-limit arithmetic are inherited from the
coarse stopped input. -/
theorem refinedAtomScreenEstimate_of_refinedMapLaw
    {ι : Type*} [Fintype ι]
    {m k A : ℕ} {alpha : ℝ} {screen refinedAtom : Set Path}
    {D : @StoppedTruncatedProp49AtomInput ι _ m k A alpha screen}
    (F : StoppedTruncatedProp49RefinedAtomMapLaw D refinedAtom) :
    RefinedAtomScreenEstimate refinedAtom screen
      (sourceProp49ScreenRate m A alpha) := by
  exact F.screen_measure_le

/-- Since every refined atom below is already contained in the preceding
history, the explicit source estimate has exactly the history-intersected
shape required by the phase-specific Proposition-4.9 interface. -/
theorem refinedAtom_history_screen_le
    (atom history screen : Set (ℕ → Site)) (rate : ℝ≥0∞)
    (hsubset : atom ⊆ history)
    (hsource : RefinedAtomScreenEstimate atom screen rate) :
    simpleRandomWalkLaw (atom ∩ history ∩ screen) ≤
      rate * simpleRandomWalkLaw (atom ∩ history) := by
  rw [Set.inter_eq_left.mpr hsubset]
  exact hsource

/-- Primed-odd/strict-right source atom refined by ordered creation sites
and the complete canonical preceding history.  The winner filter belongs to
the downstream statistic; this conditioning atom records the literal
source data common to every strict-right candidate family. -/
noncomputable def primedOddOrderedHistoryRefinedAtom {q : ℕ}
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (c : Fin (stageNumber r) → Site) : Set (ℕ → Direction) :=
  (actualPrimedStoppedVectorEvent m (stageNumber r) first labels
      (stoppedRunVectorBox q m) ∩
    stoppedSourceCondition m (stageNumber r) C) ∩
  simpleRandomWalk ⁻¹' orderedCanonicalHistoryEvent m i a r c

theorem primedOddOrderedHistoryRefinedAtom_stoppedPast {q : ℕ}
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (c : Fin (stageNumber r) → Site)
    (hnondist : ∀ j, labels j ≠ primedDistinguishedIncrementPair)
    (hm : 0 < m)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (n : ℕ) :
    MeasurableSet[iidHistory (X := Direction) n]
      (primedOddOrderedHistoryRefinedAtom
          m i a r C first labels c ∩
        {omega | stoppedCreationTime m (stageNumber r) omega = n}) := by
  let k := stageNumber r
  let A := actualPrimedStoppedVectorEvent m k first labels
      (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C
  let E := orderedCanonicalHistoryEvent m i a r c
  change MeasurableSet[iidHistory (X := Direction) n]
    ((A ∩ simpleRandomWalk ⁻¹' E) ∩
      {omega | stoppedCreationTime m k omega = n})
  apply measurableSet_sourcePast_inter_pathStoppedEvent m k n A E
  · intro omega homega
    exact ne_top_of_lt homega.2.1
  · simpa only [A] using primedOdd_sourcePast
      m k C first labels hnondist hm (by simp [k, stageNumber]) hfree n
  · simpa only [E, k] using
      measurableSet_orderedCanonicalHistoryEvent_stoppedFiber
        m i a r c hm n

theorem measurableSet_primedOddOrderedHistoryRefinedAtom {q : ℕ}
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (c : Fin (stageNumber r) → Site)
    (hnondist : ∀ j, labels j ≠ primedDistinguishedIncrementPair)
    (hm : 0 < m)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C) :
    MeasurableSet
      (primedOddOrderedHistoryRefinedAtom m i a r C first labels c) := by
  exact measurableSet_of_iidHistory_fibers_nat
    (stoppedCreationTime m (stageNumber r))
    (primedOddOrderedHistoryRefinedAtom m i a r C first labels c)
    (fun n ↦ primedOddOrderedHistoryRefinedAtom_stoppedPast
      m i a r C first labels c hnondist hm hfree n)

noncomputable def primedOddOrderedHistoryPathAtom {q : ℕ}
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (c : Fin (stageNumber r) → Site) : Set (ℕ → Site) :=
  simpleRandomWalk ''
    primedOddOrderedHistoryRefinedAtom m i a r C first labels c

theorem measurableSet_primedOddOrderedHistoryPathAtom {q : ℕ}
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (c : Fin (stageNumber r) → Site)
    (hnondist : ∀ j, labels j ≠ primedDistinguishedIncrementPair)
    (hm : 0 < m)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C) :
    MeasurableSet
      (primedOddOrderedHistoryPathAtom m i a r C first labels c) := by
  exact measurableEmbedding_simpleRandomWalk.measurableSet_image.2
    (measurableSet_primedOddOrderedHistoryRefinedAtom
      m i a r C first labels c hnondist hm hfree)

theorem primedOddOrderedHistoryPathAtom_subset_history {q : ℕ}
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (c : Fin (stageNumber r) → Site) :
    primedOddOrderedHistoryPathAtom m i a r C first labels c ⊆
      prop47History canonicalProfiles canonicalCStar m i a r.1 := by
  rintro s ⟨omega, homega, rfl⟩
  exact homega.2.2

theorem primedOddOrderedHistoryPathAtom_eq_coarse_inter_history {q : ℕ}
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (c : Fin (stageNumber r) → Site) :
    primedOddOrderedHistoryPathAtom m i a r C first labels c =
      (simpleRandomWalk ''
          (actualPrimedStoppedVectorEvent m (stageNumber r) first labels
              (stoppedRunVectorBox q m) ∩
            stoppedSourceCondition m (stageNumber r) C)) ∩
        orderedCanonicalHistoryEvent m i a r c := by
  ext s
  constructor
  · rintro ⟨omega, ⟨⟨hA, hsource⟩, ⟨hordered, hhistory⟩⟩, rfl⟩
    exact ⟨⟨omega, ⟨hA, hsource⟩, rfl⟩, hordered, hhistory⟩
  · rintro ⟨⟨omega, ⟨hA, hsource⟩, rfl⟩, hordered, hhistory⟩
    exact ⟨omega, ⟨⟨hA, hsource⟩, ⟨hordered, hhistory⟩⟩, rfl⟩

/-- Unprimed-odd/tie-left full-terminal source atom, refined at its honest
completion clock.  The terminal pair is part of the conditioning data. -/
noncomputable def unprimedOddTerminalOrderedHistoryRefinedAtom {q : ℕ}
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (C : Finset Site) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair)
    (c : Fin (stageNumber r) → Site) : Set (ℕ → Direction) :=
  (actualOddStoppedVectorEvent m (stageNumber r) labels terminal
      (stoppedRunVectorBox q m) ∩
    stoppedSourceCondition m (stageNumber r) C) ∩
  simpleRandomWalk ⁻¹' orderedCanonicalHistoryEvent m i a r c

theorem unprimedOddTerminalOrderedHistoryRefinedAtom_stoppedPast {q : ℕ}
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (C : Finset Site) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair)
    (c : Fin (stageNumber r) → Site)
    (hnondist : ∀ j, labels j ≠ distinguishedIncrementPair)
    (hm : 0 < m)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (n : ℕ) :
    MeasurableSet[iidHistory (X := Direction) n]
      (unprimedOddTerminalOrderedHistoryRefinedAtom
          m i a r C labels terminal c ∩
        {omega | stoppedCompletionTime m (stageNumber r) omega = n}) := by
  let k := stageNumber r
  let A := actualOddStoppedVectorEvent m k labels terminal
      (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C
  let E := orderedCanonicalHistoryEvent m i a r c
  change MeasurableSet[iidHistory (X := Direction) n]
    ((A ∩ simpleRandomWalk ⁻¹' E) ∩
      {omega | stoppedCompletionTime m k omega = n})
  apply measurableSet_sourcePastAfterCompletion_inter_pathStoppedEvent
    m k n A E
  · intro omega homega
    exact ne_top_of_lt homega.2.1
  · simpa only [A] using unprimedOdd_sourcePastAfterCompletion
      m k C labels hnondist terminal hm
        (by simp [k, stageNumber]) hfree n
  · intro t
    simpa only [E, k] using
      measurableSet_orderedCanonicalHistoryEvent_stoppedFiber
        m i a r c hm t

theorem measurableSet_unprimedOddTerminalOrderedHistoryRefinedAtom {q : ℕ}
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (C : Finset Site) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair)
    (c : Fin (stageNumber r) → Site)
    (hnondist : ∀ j, labels j ≠ distinguishedIncrementPair)
    (hm : 0 < m)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C) :
    MeasurableSet
      (unprimedOddTerminalOrderedHistoryRefinedAtom
        m i a r C labels terminal c) := by
  exact measurableSet_of_iidHistory_fibers_nat
    (stoppedCompletionTime m (stageNumber r))
    (unprimedOddTerminalOrderedHistoryRefinedAtom
      m i a r C labels terminal c)
    (fun n ↦ unprimedOddTerminalOrderedHistoryRefinedAtom_stoppedPast
      m i a r C labels terminal c hnondist hm hfree n)

noncomputable def unprimedOddTerminalOrderedHistoryPathAtom {q : ℕ}
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (C : Finset Site) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair)
    (c : Fin (stageNumber r) → Site) : Set (ℕ → Site) :=
  simpleRandomWalk ''
    unprimedOddTerminalOrderedHistoryRefinedAtom
      m i a r C labels terminal c

theorem measurableSet_unprimedOddTerminalOrderedHistoryPathAtom {q : ℕ}
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (C : Finset Site) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair)
    (c : Fin (stageNumber r) → Site)
    (hnondist : ∀ j, labels j ≠ distinguishedIncrementPair)
    (hm : 0 < m)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C) :
    MeasurableSet
      (unprimedOddTerminalOrderedHistoryPathAtom
        m i a r C labels terminal c) := by
  exact measurableEmbedding_simpleRandomWalk.measurableSet_image.2
    (measurableSet_unprimedOddTerminalOrderedHistoryRefinedAtom
      m i a r C labels terminal c hnondist hm hfree)

theorem unprimedOddTerminalOrderedHistoryPathAtom_subset_history {q : ℕ}
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (C : Finset Site) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair)
    (c : Fin (stageNumber r) → Site) :
    unprimedOddTerminalOrderedHistoryPathAtom
        m i a r C labels terminal c ⊆
      prop47History canonicalProfiles canonicalCStar m i a r.1 := by
  rintro s ⟨omega, homega, rfl⟩
  exact homega.2.2

theorem unprimedOddTerminalOrderedHistoryPathAtom_eq_coarse_inter_history
    {q : ℕ}
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (C : Finset Site) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair)
    (c : Fin (stageNumber r) → Site) :
    unprimedOddTerminalOrderedHistoryPathAtom
        m i a r C labels terminal c =
      (simpleRandomWalk ''
          (actualOddStoppedVectorEvent m (stageNumber r) labels terminal
              (stoppedRunVectorBox q m) ∩
            stoppedSourceCondition m (stageNumber r) C)) ∩
        orderedCanonicalHistoryEvent m i a r c := by
  ext s
  constructor
  · rintro ⟨omega, ⟨⟨hA, hsource⟩, ⟨hordered, hhistory⟩⟩, rfl⟩
    exact ⟨⟨omega, ⟨hA, hsource⟩, rfl⟩, hordered, hhistory⟩
  · rintro ⟨⟨omega, ⟨hA, hsource⟩, rfl⟩, hordered, hhistory⟩
    exact ⟨omega, ⟨⟨hA, hsource⟩, ⟨hordered, hhistory⟩⟩, rfl⟩

/-- Primed-even/strict-right full-terminal source atom, again conditioned at
the completion clock and retaining the paper's `-e₁` primed orientation. -/
noncomputable def primedEvenTerminalOrderedHistoryRefinedAtom {q : ℕ}
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair) (terminal : IncrementPair)
    (c : Fin (stageNumber r) → Site) : Set (ℕ → Direction) :=
  (actualPrimedTerminalVectorEvent m (stageNumber r) first labels terminal
      (stoppedRunVectorBox q m) ∩
    stoppedSourceCondition m (stageNumber r) C) ∩
  simpleRandomWalk ⁻¹' orderedCanonicalHistoryEvent m i a r c

theorem primedEvenTerminalOrderedHistoryRefinedAtom_stoppedPast {q : ℕ}
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair) (terminal : IncrementPair)
    (c : Fin (stageNumber r) → Site)
    (hnondist : ∀ j, labels j ≠ primedDistinguishedIncrementPair)
    (hm : 0 < m)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (n : ℕ) :
    MeasurableSet[iidHistory (X := Direction) n]
      (primedEvenTerminalOrderedHistoryRefinedAtom
          m i a r C first labels terminal c ∩
        {omega | stoppedCompletionTime m (stageNumber r) omega = n}) := by
  let k := stageNumber r
  let A := actualPrimedTerminalVectorEvent m k first labels terminal
      (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C
  let E := orderedCanonicalHistoryEvent m i a r c
  change MeasurableSet[iidHistory (X := Direction) n]
    ((A ∩ simpleRandomWalk ⁻¹' E) ∩
      {omega | stoppedCompletionTime m k omega = n})
  apply measurableSet_sourcePastAfterCompletion_inter_pathStoppedEvent
    m k n A E
  · intro omega homega
    exact ne_top_of_lt homega.2.1
  · simpa only [A] using primedEven_sourcePastAfterCompletion
      m k C first labels hnondist terminal hm
        (by simp [k, stageNumber]) hfree n
  · intro t
    simpa only [E, k] using
      measurableSet_orderedCanonicalHistoryEvent_stoppedFiber
        m i a r c hm t

theorem measurableSet_primedEvenTerminalOrderedHistoryRefinedAtom {q : ℕ}
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair) (terminal : IncrementPair)
    (c : Fin (stageNumber r) → Site)
    (hnondist : ∀ j, labels j ≠ primedDistinguishedIncrementPair)
    (hm : 0 < m)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C) :
    MeasurableSet
      (primedEvenTerminalOrderedHistoryRefinedAtom
        m i a r C first labels terminal c) := by
  exact measurableSet_of_iidHistory_fibers_nat
    (stoppedCompletionTime m (stageNumber r))
    (primedEvenTerminalOrderedHistoryRefinedAtom
      m i a r C first labels terminal c)
    (fun n ↦ primedEvenTerminalOrderedHistoryRefinedAtom_stoppedPast
      m i a r C first labels terminal c hnondist hm hfree n)

noncomputable def primedEvenTerminalOrderedHistoryPathAtom {q : ℕ}
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair) (terminal : IncrementPair)
    (c : Fin (stageNumber r) → Site) : Set (ℕ → Site) :=
  simpleRandomWalk ''
    primedEvenTerminalOrderedHistoryRefinedAtom
      m i a r C first labels terminal c

theorem measurableSet_primedEvenTerminalOrderedHistoryPathAtom {q : ℕ}
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair) (terminal : IncrementPair)
    (c : Fin (stageNumber r) → Site)
    (hnondist : ∀ j, labels j ≠ primedDistinguishedIncrementPair)
    (hm : 0 < m)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C) :
    MeasurableSet
      (primedEvenTerminalOrderedHistoryPathAtom
        m i a r C first labels terminal c) := by
  exact measurableEmbedding_simpleRandomWalk.measurableSet_image.2
    (measurableSet_primedEvenTerminalOrderedHistoryRefinedAtom
      m i a r C first labels terminal c hnondist hm hfree)

theorem primedEvenTerminalOrderedHistoryPathAtom_subset_history {q : ℕ}
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair) (terminal : IncrementPair)
    (c : Fin (stageNumber r) → Site) :
    primedEvenTerminalOrderedHistoryPathAtom
        m i a r C first labels terminal c ⊆
      prop47History canonicalProfiles canonicalCStar m i a r.1 := by
  rintro s ⟨omega, homega, rfl⟩
  exact homega.2.2

theorem primedEvenTerminalOrderedHistoryPathAtom_eq_coarse_inter_history
    {q : ℕ}
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair) (terminal : IncrementPair)
    (c : Fin (stageNumber r) → Site) :
    primedEvenTerminalOrderedHistoryPathAtom
        m i a r C first labels terminal c =
      (simpleRandomWalk ''
          (actualPrimedTerminalVectorEvent m (stageNumber r) first labels
              terminal (stoppedRunVectorBox q m) ∩
            stoppedSourceCondition m (stageNumber r) C)) ∩
        orderedCanonicalHistoryEvent m i a r c := by
  ext s
  constructor
  · rintro ⟨omega, ⟨⟨hA, hsource⟩, ⟨hordered, hhistory⟩⟩, rfl⟩
    exact ⟨⟨omega, ⟨hA, hsource⟩, rfl⟩, hordered, hhistory⟩
  · rintro ⟨⟨omega, ⟨hA, hsource⟩, rfl⟩, hordered, hhistory⟩
    exact ⟨omega, ⟨⟨hA, hsource⟩, ⟨hordered, hhistory⟩⟩, rfl⟩

/-! ### Local Proposition-4.9 fields for the four X branches

The refined finite-branch interface asks for the measure of
`atom ∩ history ∩ branchScreen`, normalized by
`atom ∩ history`.  The next four lemmas put each literal X source atom in
exactly that form.  Their only probabilistic premise is the genuinely
source-specific narrow-band estimate on the refined atom itself; in
particular, no raw complement-factorization assertion is introduced. -/

theorem unprimedEvenOrderedHistoryPathAtom_prop49_local {q : ℕ}
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (C : Finset Site) (labels : Fin q → IncrementPair)
    (c : Fin (stageNumber r) → Site)
    (screen : Set (ℕ → Site)) (rate : ℝ≥0∞)
    (hsource : RefinedAtomScreenEstimate
      (unprimedEvenOrderedHistoryPathAtom m i a r C labels c)
      screen rate) :
    simpleRandomWalkLaw
        (unprimedEvenOrderedHistoryPathAtom m i a r C labels c ∩
          prop47History canonicalProfiles canonicalCStar m i a r.1 ∩
          screen) ≤
      rate * simpleRandomWalkLaw
        (unprimedEvenOrderedHistoryPathAtom m i a r C labels c ∩
          prop47History canonicalProfiles canonicalCStar m i a r.1) := by
  exact refinedAtom_history_screen_le
    (unprimedEvenOrderedHistoryPathAtom m i a r C labels c)
    (prop47History canonicalProfiles canonicalCStar m i a r.1)
    screen rate
    (unprimedEvenOrderedHistoryPathAtom_subset_history
      m i a r C labels c)
    hsource

theorem primedOddOrderedHistoryPathAtom_prop49_local {q : ℕ}
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (c : Fin (stageNumber r) → Site)
    (screen : Set (ℕ → Site)) (rate : ℝ≥0∞)
    (hsource : RefinedAtomScreenEstimate
      (primedOddOrderedHistoryPathAtom m i a r C first labels c)
      screen rate) :
    simpleRandomWalkLaw
        (primedOddOrderedHistoryPathAtom m i a r C first labels c ∩
          prop47History canonicalProfiles canonicalCStar m i a r.1 ∩
          screen) ≤
      rate * simpleRandomWalkLaw
        (primedOddOrderedHistoryPathAtom m i a r C first labels c ∩
          prop47History canonicalProfiles canonicalCStar m i a r.1) := by
  exact refinedAtom_history_screen_le
    (primedOddOrderedHistoryPathAtom m i a r C first labels c)
    (prop47History canonicalProfiles canonicalCStar m i a r.1)
    screen rate
    (primedOddOrderedHistoryPathAtom_subset_history
      m i a r C first labels c)
    hsource

theorem unprimedOddTerminalOrderedHistoryPathAtom_prop49_local {q : ℕ}
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (C : Finset Site) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair)
    (c : Fin (stageNumber r) → Site)
    (screen : Set (ℕ → Site)) (rate : ℝ≥0∞)
    (hsource : RefinedAtomScreenEstimate
      (unprimedOddTerminalOrderedHistoryPathAtom
        m i a r C labels terminal c) screen rate) :
    simpleRandomWalkLaw
        (unprimedOddTerminalOrderedHistoryPathAtom
            m i a r C labels terminal c ∩
          prop47History canonicalProfiles canonicalCStar m i a r.1 ∩
          screen) ≤
      rate * simpleRandomWalkLaw
        (unprimedOddTerminalOrderedHistoryPathAtom
            m i a r C labels terminal c ∩
          prop47History canonicalProfiles canonicalCStar m i a r.1) := by
  exact refinedAtom_history_screen_le
    (unprimedOddTerminalOrderedHistoryPathAtom
      m i a r C labels terminal c)
    (prop47History canonicalProfiles canonicalCStar m i a r.1)
    screen rate
    (unprimedOddTerminalOrderedHistoryPathAtom_subset_history
      m i a r C labels terminal c)
    hsource

theorem primedEvenTerminalOrderedHistoryPathAtom_prop49_local {q : ℕ}
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair) (terminal : IncrementPair)
    (c : Fin (stageNumber r) → Site)
    (screen : Set (ℕ → Site)) (rate : ℝ≥0∞)
    (hsource : RefinedAtomScreenEstimate
      (primedEvenTerminalOrderedHistoryPathAtom
        m i a r C first labels terminal c) screen rate) :
    simpleRandomWalkLaw
        (primedEvenTerminalOrderedHistoryPathAtom
            m i a r C first labels terminal c ∩
          prop47History canonicalProfiles canonicalCStar m i a r.1 ∩
          screen) ≤
      rate * simpleRandomWalkLaw
        (primedEvenTerminalOrderedHistoryPathAtom
            m i a r C first labels terminal c ∩
          prop47History canonicalProfiles canonicalCStar m i a r.1) := by
  exact refinedAtom_history_screen_le
    (primedEvenTerminalOrderedHistoryPathAtom
      m i a r C first labels terminal c)
    (prop47History canonicalProfiles canonicalCStar m i a r.1)
    screen rate
    (primedEvenTerminalOrderedHistoryPathAtom_subset_history
      m i a r C first labels terminal c)
    hsource

/-! ### Checked coordinate tail plus an honest complement-history tower

For the unprimed-even/left-winner branch the checked stopped map law already
gives a joint product of the active truncated profile, the fresh direction,
and every complementary stopped block.  Thus the atom-local estimate does
not need to be assumed once the ordered preceding history is identified as
a measurable event of that complement statistic.  The identification below
is the exact remaining deterministic/tower obligation; unlike a raw
factorization assertion, it is stated only on the coarse stopped atom. -/

/-- A statistic determines an event on an atom precisely when membership in
that event is constant on the statistic's fibers inside the atom.  This is
strictly weaker than constancy on the whole coarse atom. -/
def EventDeterminedByOn
    {Omega Z : Type*} (atom history : Set Omega) (z : Omega → Z) : Prop :=
  ∀ ω₁ ∈ atom, ∀ ω₂ ∈ atom, z ω₁ = z ω₂ →
    (ω₁ ∈ history ↔ ω₂ ∈ history)

/-- An event containing the whole atom is automatically determined by every
statistic on that atom. -/
theorem EventDeterminedByOn.of_subset
    {Omega Z : Type*} {atom history : Set Omega} {z : Omega → Z}
    (hsubset : atom ⊆ history) :
    EventDeterminedByOn atom history z := by
  intro ω₁ hω₁ ω₂ hω₂ _hz
  exact ⟨fun _ ↦ hsubset hω₂, fun _ ↦ hsubset hω₁⟩

theorem EventDeterminedByOn.inter
    {Omega Z : Type*} {atom E F : Set Omega} {z : Omega → Z}
    (hE : EventDeterminedByOn atom E z)
    (hF : EventDeterminedByOn atom F z) :
    EventDeterminedByOn atom (E ∩ F) z := by
  intro ω₁ hω₁ ω₂ hω₂ hz
  have hE' := hE ω₁ hω₁ ω₂ hω₂ hz
  have hF' := hF ω₁ hω₁ ω₂ hω₂ hz
  constructor
  · rintro ⟨hωE, hωF⟩
    exact ⟨hE'.mp hωE, hF'.mp hωF⟩
  · rintro ⟨hωE, hωF⟩
    exact ⟨hE'.mpr hωE, hF'.mpr hωF⟩

/-- Fibre determination is preserved by the recursive screening-history
intersection.  This is the set-theoretic tower step needed by the later
Proposition-4.9 atoms: it reduces determination of the whole preceding
history to determination of its base event and of each earlier screen. -/
theorem EventDeterminedByOn.screeningHistory
    {Omega Z : Type*} (atom base : Set Omega) (screen : ℕ → Set Omega)
    (z : Omega → Z) (n : ℕ)
    (hbase : EventDeterminedByOn atom base z)
    (hscreen : ∀ j < n, EventDeterminedByOn atom (screen j) z) :
    EventDeterminedByOn atom
      (HLOZScreeningAssembly.screeningHistory base screen n) z := by
  induction n with
  | zero =>
      simpa only [HLOZScreeningAssembly.screeningHistory_zero] using hbase
  | succ n ih =>
      rw [HLOZScreeningAssembly.screeningHistory_succ]
      apply (ih fun j hj ↦ hscreen j (hj.trans (Nat.lt_succ_self n))).inter
      exact hscreen n (Nat.lt_succ_self n)

/-- For the literal Proposition-4.7 history, the generic screening-history
tower says that it is enough to determine the initial one-site pairing event
and every preceding concrete stage event.  Screens outside the three-stage
range are `univ` and therefore require no source input. -/
theorem eventDeterminedByOn_prop47History_of_stages
    {Z : Type*} (atom : Set Path) (z : Path → Z)
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (n : ℕ)
    (hbase : EventDeterminedByOn atom (prefixPairingEvent m i 1) z)
    (hstage : ∀ (j : Fin 3), j.1 < n →
      EventDeterminedByOn atom
        (prop47StageEvent profiles cStar i m j
          (alphaValue (tripleAlphaIndex a j))) z) :
    EventDeterminedByOn atom
      (prop47History profiles cStar m i a n) z := by
  unfold prop47History
  apply EventDeterminedByOn.screeningHistory atom
    (prefixPairingEvent m i 1)
      (fun j ↦ if h : j < 3 then
        prop47StageEvent profiles cStar i m ⟨j, h⟩
          (alphaValue (tripleAlphaIndex a ⟨j, h⟩))
        else Set.univ) z n hbase
  intro j hj
  by_cases hj3 : j < 3
  · simpa only [hj3, dite_true] using hstage ⟨j, hj3⟩ hj
  · simp only [hj3, dite_false]
    exact EventDeterminedByOn.of_subset (Set.subset_univ atom)

/-- Source-facing decomposition of the complete ordered-history fibre
condition.  The ordered creation tuple, the initial pairing event and each
earlier stage event may now be proved independently from the chronological
complement statistic. -/
theorem eventDeterminedByOn_orderedProfileHistoryEvent_of_stages
    {Z : Type*} (atom : Set Path) (z : Path → Z)
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (c : Fin (stageNumber r) → Site)
    (hordered : EventDeterminedByOn atom
      (orderedCreationSitesEvent m (stageNumber r) c) z)
    (hbase : EventDeterminedByOn atom (prefixPairingEvent m i 1) z)
    (hstage : ∀ (j : Fin 3), j.1 < r.1 →
      EventDeterminedByOn atom
        (prop47StageEvent profiles cStar i m j
          (alphaValue (tripleAlphaIndex a j))) z) :
    EventDeterminedByOn atom
      (orderedProfileHistoryEvent profiles cStar m i a r c) z := by
  simpa only [orderedProfileHistoryEvent] using hordered.inter
    (eventDeterminedByOn_prop47History_of_stages atom z profiles cStar
      m i a r.1 hbase hstage)

theorem levelCreationSitesUpTo_one (s : Path) (m : ℕ) :
    levelCreationSitesUpTo s m 1 = {levelCreationSite s m 1} := by
  simp [levelCreationSitesUpTo]

/-- With only one level-creation site, its unordered singleton already
determines the ordered creation tuple. -/
theorem orderedCreationSites_one_eq_of_levelCreationSitesUpTo_eq
    {s t : Path} {m : ℕ}
    (hsets : levelCreationSitesUpTo s m 1 =
      levelCreationSitesUpTo t m 1) :
    orderedCreationSites m 1 s = orderedCreationSites m 1 t := by
  have hsite : levelCreationSite s m 1 = levelCreationSite t m 1 := by
    have hmem : levelCreationSite s m 1 ∈
        levelCreationSitesUpTo t m 1 := by
      rw [← hsets, levelCreationSitesUpTo_one]
      simp
    simpa [levelCreationSitesUpTo_one] using hmem
  funext j
  have hj : j = 0 := Fin.eq_zero j
  subst j
  simpa [orderedCreationSites] using hsite

/-- If every path in an atom has the same one-element unordered creation
set, then every ordered one-site creation event is constant on that atom.
No property of the chosen statistic is needed. -/
theorem eventDeterminedByOn_orderedCreationSitesEvent_one_of_fixed_set
    {Z : Type*} (atom : Set Path) (z : Path → Z) (m : ℕ)
    (C : Finset Site) (c : Fin 1 → Site)
    (hfixed : ∀ s ∈ atom, levelCreationSitesUpTo s m 1 = C) :
    EventDeterminedByOn atom (orderedCreationSitesEvent m 1 c) z := by
  intro s hs t ht _hz
  have hst : orderedCreationSites m 1 s = orderedCreationSites m 1 t :=
    orderedCreationSites_one_eq_of_levelCreationSitesUpTo_eq
      ((hfixed s hs).trans (hfixed t ht).symm)
  change orderedCreationSites m 1 s = c ↔ orderedCreationSites m 1 t = c
  rw [hst]

/-- The exact full-history fiber condition splits into the two deterministic
questions appearing in the source: the ordered creation tuple and the
recursive preceding screen history. -/
theorem eventDeterminedByOn_orderedProfileHistoryEvent
    {Z : Type*} (atom : Set Path) (z : Path → Z)
    (profiles : Fin 6 → HLOZProp47SourceObjects.ExternalProfilePair)
    (cStar : Fin 6 → ℝ) (m : ℕ) (i : Fin 6) (a : AlphaTriple)
    (r : StageIndex) (c : Fin (stageNumber r) → Site)
    (hordered : EventDeterminedByOn atom
      (orderedCreationSitesEvent m (stageNumber r) c) z)
    (hhistory : EventDeterminedByOn atom
      (prop47History profiles cStar m i a r.1) z) :
    EventDeterminedByOn atom
      (orderedProfileHistoryEvent profiles cStar m i a r c) z := by
  exact hordered.inter hhistory

/-- At the first screening stage, a fixed one-site creation set and the
corresponding pairing condition determine the complete ordered history.
This is the stage-zero case of the Proposition-4.9 tower and requires no
fiber information from the complement statistic. -/
theorem eventDeterminedByOn_orderedProfileHistoryEvent_zero_of_fixed_source
    {Z : Type*} (atom : Set Path) (z : Path → Z)
    (profiles : Fin 6 → HLOZProp47SourceObjects.ExternalProfilePair)
    (cStar : Fin 6 → ℝ) (m : ℕ) (i : Fin 6) (a : AlphaTriple)
    (C : Finset Site) (c : Fin 1 → Site)
    (hthreshold : atom ⊆ hlozThresholdTimeEventK m 1)
    (hfixed : ∀ s ∈ atom, levelCreationSitesUpTo s m 1 = C)
    (hfree : HLOZPairing.PairFree (HLOZPairing.pairingRelation i) C) :
    EventDeterminedByOn atom
      (orderedProfileHistoryEvent profiles cStar m i a 0 c) z := by
  apply eventDeterminedByOn_orderedProfileHistoryEvent
  · exact eventDeterminedByOn_orderedCreationSitesEvent_one_of_fixed_set
      atom z m C c hfixed
  · apply EventDeterminedByOn.of_subset
    intro s hs
    change s ∈ prop47History profiles cStar m i a 0
    rw [prop47History_zero]
    refine ⟨hthreshold hs, ?_⟩
    change HLOZPairing.PairFree (HLOZPairing.pairingRelation i)
      (levelCreationSitesUpTo s m 1)
    rw [hfixed s hs]
    exact hfree

/-- Fiberwise determination gives the literal complement-preimage identity
needed by the tower argument. -/
theorem inter_eq_inter_preimage_of_eventDeterminedByOn
    {Omega Z : Type*} (atom history : Set Omega) (z : Omega → Z)
    (hdet : EventDeterminedByOn atom history z) :
    atom ∩ history = atom ∩ z ⁻¹'
      {v | ∃ ω ∈ atom, ω ∈ history ∧ z ω = v} := by
  ext ω
  constructor
  · rintro ⟨hωatom, hωhistory⟩
    exact ⟨hωatom, ω, hωatom, hωhistory, rfl⟩
  · rintro ⟨hωatom, τ, hτatom, hτhistory, hτω⟩
    exact ⟨hωatom, (hdet τ hτatom ω hωatom hτω).mp hτhistory⟩

/-- A checked joint active/complement law and fiberwise determination of a
history event give the Proposition-4.9 estimate on the history-refined atom.

This is profile-generic: `history` can be the ordered history belonging to
any one-step-adapted profile family.  The only set-level input beyond
fiberwise determination is measurability of the realized complement image;
for all finite/countable stopped complements below it is automatic from the
discrete measurable space. -/
theorem refinedAtomScreenEstimate_of_joint_complement_determined
    {ι : Type*} [Fintype ι]
    {m k A : ℕ} {alpha : ℝ} {screen history : Set Path}
    (D : @StoppedTruncatedProp49AtomInput ι _ m k A alpha screen)
    {Z : Type} [MeasurableSpace Z]
    (complementLaw : Measure Z) [SFinite complementLaw]
    (z : Path → Z) (hz : Measurable z)
    (himage : MeasurableSet {v | ∃ s ∈ D.atom, s ∈ history ∧ z s = v})
    (hdet : EventDeterminedByOn D.atom history z)
    (hjoint :
      (simpleRandomWalkLaw.restrict D.atom).map
          (fun s ↦ ((D.lazyVector s, D.nextDirection s), z s)) =
        simpleRandomWalkLaw D.atom •
          (((sourceTruncatedProfileMeasure m D.profile).prod directionLaw).prod
            complementLaw)) :
    RefinedAtomScreenEstimate (D.atom ∩ history) screen
      (sourceProp49ScreenRate m A alpha) := by
  let H : Set Z := {v | ∃ s ∈ D.atom, s ∈ history ∧ z s = v}
  let F : StoppedTruncatedProp49HistoryFactorization D history :=
    { Z := Z
      measurableSpaceZ := inferInstance
      complementLaw := complementLaw
      sFiniteComplementLaw := inferInstance
      complement := z
      measurable_complement := hz
      historySet := H
      measurable_historySet := by simpa only [H] using himage
      history_eq := inter_eq_inter_preimage_of_eventDeterminedByOn
        D.atom history z hdet
      joint_map_law := hjoint }
  exact F.history_screen_le D

theorem unprimedEvenLeftWinnerProp49_orderedHistory_screen_le
    {m A : ℕ} {alpha : ℝ} {screen : Set (ℕ → Site)}
    {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    (D : UnprimedEvenLeftWinnerProp49AtomData
      m (stageNumber r) A alpha screen)
    (c : Fin (stageNumber r) → Site)
    (historySet : Set
      (ComplementStoppedBase (0, 0) D.labels D.C
        (unprimedEvenLeftWinnerBases D.labels D.candidateBases) → ℕ))
    (hmeasurableHistorySet : MeasurableSet historySet)
    (history_eq :
      D.atom ∩ orderedCanonicalHistoryEvent m i a r c =
        D.atom ∩
          unprimedEvenComplementPath m (stageNumber r) D.C D.labels
            (unprimedEvenLeftWinnerBases D.labels D.candidateBases) ⁻¹'
              historySet) :
    simpleRandomWalkLaw
        (D.atom ∩ orderedCanonicalHistoryEvent m i a r c ∩ screen) ≤
      sourceProp49ScreenRate m A alpha *
        simpleRandomWalkLaw
          (D.atom ∩ orderedCanonicalHistoryEvent m i a r c) := by
  let activeBases :=
    unprimedEvenLeftWinnerBases D.labels D.candidateBases
  let complementLaw := stoppedMixedComplementMeasure
    (0, 0) D.labels m D.C activeBases
      (stoppedExternalLeft (0, 0) D.labels)
      (stoppedExternalRight (0, 0) D.labels)
  have hpos := unprimedEven_mixedCoordinatePos_of_nonempty
    m (stageNumber r) D.C D.labels D.m_pos D.creation_card
      D.creation_pairFree D.offBase D.terminal_mem D.admissible_nonempty
  letI : IsProbabilityMeasure complementLaw := by
    dsimp only [complementLaw]
    exact stoppedMixedComplementMeasure_isProbabilityMeasure
      (0, 0) D.labels m D.C activeBases
        (stoppedExternalLeft (0, 0) D.labels)
        (stoppedExternalRight (0, 0) D.labels) hpos
  let F : StoppedTruncatedProp49HistoryFactorization D.toInput
      (orderedCanonicalHistoryEvent m i a r c) :=
    { Z := ComplementStoppedBase (0, 0) D.labels D.C activeBases → ℕ
      measurableSpaceZ := inferInstance
      complementLaw := complementLaw
      sFiniteComplementLaw := inferInstance
      complement := unprimedEvenComplementPath
        m (stageNumber r) D.C D.labels activeBases
      measurable_complement :=
        measurable_unprimedEvenComplementPath
          m (stageNumber r) D.C D.labels D.nondistinguished activeBases
      historySet := historySet
      measurable_historySet := hmeasurableHistorySet
      history_eq := history_eq
      joint_map_law := by
        change
          (simpleRandomWalkLaw.restrict
              (simpleRandomWalk ''
                (actualStoppedVectorEvent m (stageNumber r) D.labels
                    (stoppedRunVectorBox D.q m) ∩
                  stoppedSourceCondition m (stageNumber r) D.C))).map
              (fun s ↦
                ((unprimedEvenActiveFreePathLazy m (stageNumber r) D.C
                    D.labels activeBases s,
                  unprimedEvenActiveFreePathNext m (stageNumber r) D.C
                    D.labels activeBases s),
                  unprimedEvenComplementPath m (stageNumber r) D.C
                    D.labels activeBases s)) =
            simpleRandomWalkLaw
                (simpleRandomWalk ''
                  (actualStoppedVectorEvent m (stageNumber r) D.labels
                      (stoppedRunVectorBox D.q m) ∩
                    stoppedSourceCondition m (stageNumber r) D.C)) •
              (((sourceTruncatedProfileMeasure m
                (activeFreeStoppedShape (0, 0) D.labels D.C activeBases)).prod
                  directionLaw).prod complementLaw)
        simpa only [activeBases, complementLaw] using
          unprimedEven_leftWinner_active_complement_path_map_law
            m (stageNumber r) D.C D.labels D.nondistinguished D.m_pos
              D.k_pos D.creation_card D.creation_pairFree D.offBase
              D.terminal_mem D.admissible_nonempty D.candidateBases }
  exact F.history_screen_le D.toInput

/-- The checked coordinate tail therefore proves the requested
`RefinedAtomScreenEstimate` on the ordered-history atom, subject only to the
explicit complement representation of that history. -/
theorem unprimedEvenLeftWinnerProp49_orderedHistory_screenEstimate
    {m A : ℕ} {alpha : ℝ} {screen : Set (ℕ → Site)}
    {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    (D : UnprimedEvenLeftWinnerProp49AtomData
      m (stageNumber r) A alpha screen)
    (c : Fin (stageNumber r) → Site)
    (historySet : Set
      (ComplementStoppedBase (0, 0) D.labels D.C
        (unprimedEvenLeftWinnerBases D.labels D.candidateBases) → ℕ))
    (hmeasurableHistorySet : MeasurableSet historySet)
    (history_eq :
      D.atom ∩ orderedCanonicalHistoryEvent m i a r c =
        D.atom ∩
          unprimedEvenComplementPath m (stageNumber r) D.C D.labels
            (unprimedEvenLeftWinnerBases D.labels D.candidateBases) ⁻¹'
              historySet) :
    RefinedAtomScreenEstimate
      (unprimedEvenOrderedHistoryPathAtom
        m i a r D.C D.labels c) screen
      (sourceProp49ScreenRate m A alpha) := by
  rw [RefinedAtomScreenEstimate,
    unprimedEvenOrderedHistoryPathAtom_eq_coarse_inter_history]
  exact unprimedEvenLeftWinnerProp49_orderedHistory_screen_le
    D c historySet hmeasurableHistorySet history_eq

/-- Source-friendly version of the preceding theorem.  It is enough to
prove that the ordered history is constant on fibers of the *complement*
statistic within the coarse stopped atom.  Countability of the finite
complement vector makes the resulting history set measurable automatically.
-/
theorem unprimedEvenLeftWinnerProp49_orderedHistory_screenEstimate_of_fiberwise
    {m A : ℕ} {alpha : ℝ} {screen : Set (ℕ → Site)}
    {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    (D : UnprimedEvenLeftWinnerProp49AtomData
      m (stageNumber r) A alpha screen)
    (c : Fin (stageNumber r) → Site)
    (hdet : EventDeterminedByOn D.atom
      (orderedCanonicalHistoryEvent m i a r c)
      (unprimedEvenComplementPath m (stageNumber r) D.C D.labels
        (unprimedEvenLeftWinnerBases D.labels D.candidateBases))) :
    RefinedAtomScreenEstimate
      (unprimedEvenOrderedHistoryPathAtom
        m i a r D.C D.labels c) screen
      (sourceProp49ScreenRate m A alpha) := by
  let z := unprimedEvenComplementPath m (stageNumber r) D.C D.labels
    (unprimedEvenLeftWinnerBases D.labels D.candidateBases)
  let history := orderedCanonicalHistoryEvent m i a r c
  let H : Set
      (ComplementStoppedBase (0, 0) D.labels D.C
        (unprimedEvenLeftWinnerBases D.labels D.candidateBases) → ℕ) :=
    {v | ∃ s ∈ D.atom, s ∈ history ∧ z s = v}
  have hH : MeasurableSet H := MeasurableSet.of_discrete
  have heq : D.atom ∩ history = D.atom ∩ z ⁻¹' H := by
    exact inter_eq_inter_preimage_of_eventDeterminedByOn
      D.atom history z hdet
  exact unprimedEvenLeftWinnerProp49_orderedHistory_screenEstimate
    D c H hH heq

/-- Primed-odd analogue of the checked history tower.  The stopped map law
and the active/complement independence are now internal; only the literal
identification of the ordered history with a complement event is supplied. -/
theorem primedOddStrictRightWinnerProp49_orderedHistory_screen_le
    {m A : ℕ} {alpha : ℝ} {screen : Set (ℕ → Site)}
    {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    (D : PrimedOddStrictRightWinnerProp49AtomData
      m (stageNumber r) A alpha screen)
    (c : Fin (stageNumber r) → Site)
    (historySet : Set
      (ComplementStoppedBase (primedInitialBase D.first) D.labels D.C
        (primedOddStrictRightWinnerBases D.first D.labels
          D.candidateBases) → ℕ))
    (hmeasurableHistorySet : MeasurableSet historySet)
    (history_eq :
      D.atom ∩ orderedCanonicalHistoryEvent m i a r c =
        D.atom ∩
          primedOddComplementPath m (stageNumber r) D.C D.first D.labels
            (primedOddStrictRightWinnerBases D.first D.labels
              D.candidateBases) ⁻¹' historySet) :
    simpleRandomWalkLaw
        (D.atom ∩ orderedCanonicalHistoryEvent m i a r c ∩ screen) ≤
      sourceProp49ScreenRate m A alpha *
        simpleRandomWalkLaw
          (D.atom ∩ orderedCanonicalHistoryEvent m i a r c) := by
  let activeBases :=
    primedOddStrictRightWinnerBases D.first D.labels D.candidateBases
  let complementLaw := stoppedMixedComplementMeasure
    (primedInitialBase D.first) D.labels m D.C activeBases
      (primedStoppedExternalLeft D.first D.labels)
      (primedStoppedExternalRight D.first D.labels)
  have hpos := primedOdd_mixedCoordinatePos_of_nonempty
    m (stageNumber r) D.C D.first D.labels D.m_pos D.creation_card
      D.creation_pairFree D.offBase D.terminal_mem D.admissible_nonempty
  letI : IsProbabilityMeasure complementLaw := by
    dsimp only [complementLaw]
    exact stoppedMixedComplementMeasure_isProbabilityMeasure
      (primedInitialBase D.first) D.labels m D.C activeBases
        (primedStoppedExternalLeft D.first D.labels)
        (primedStoppedExternalRight D.first D.labels) hpos
  let F : StoppedTruncatedProp49HistoryFactorization D.toInput
      (orderedCanonicalHistoryEvent m i a r c) :=
    { Z := ComplementStoppedBase (primedInitialBase D.first) D.labels D.C
        activeBases → ℕ
      measurableSpaceZ := inferInstance
      complementLaw := complementLaw
      sFiniteComplementLaw := inferInstance
      complement := primedOddComplementPath
        m (stageNumber r) D.C D.first D.labels activeBases
      measurable_complement :=
        measurable_primedOddComplementPath m (stageNumber r) D.C D.first
          D.labels D.nondistinguished activeBases
      historySet := historySet
      measurable_historySet := hmeasurableHistorySet
      history_eq := history_eq
      joint_map_law := by
        change
          (simpleRandomWalkLaw.restrict
              (simpleRandomWalk ''
                (actualPrimedStoppedVectorEvent m (stageNumber r) D.first
                    D.labels (stoppedRunVectorBox D.q m) ∩
                  stoppedSourceCondition m (stageNumber r) D.C))).map
              (fun s ↦
                ((primedOddActiveFreePathLazy m (stageNumber r) D.C
                    D.first D.labels activeBases s,
                  primedOddActiveFreePathNext m (stageNumber r) D.C
                    D.first D.labels activeBases s),
                  primedOddComplementPath m (stageNumber r) D.C D.first
                    D.labels activeBases s)) =
            simpleRandomWalkLaw
                (simpleRandomWalk ''
                  (actualPrimedStoppedVectorEvent m (stageNumber r) D.first
                      D.labels (stoppedRunVectorBox D.q m) ∩
                    stoppedSourceCondition m (stageNumber r) D.C)) •
              (((sourceTruncatedProfileMeasure m
                (activeFreeStoppedShape (primedInitialBase D.first)
                  D.labels D.C activeBases)).prod directionLaw).prod
                    complementLaw)
        simpa only [activeBases, complementLaw] using
          primedOdd_strictRightWinner_active_complement_path_map_law
            m (stageNumber r) D.C D.first D.labels D.nondistinguished
              D.m_pos D.k_pos D.creation_card D.creation_pairFree D.offBase
              D.terminal_mem D.admissible_nonempty D.candidateBases }
  exact F.history_screen_le D.toInput

theorem primedOddStrictRightWinnerProp49_orderedHistory_screenEstimate
    {m A : ℕ} {alpha : ℝ} {screen : Set (ℕ → Site)}
    {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    (D : PrimedOddStrictRightWinnerProp49AtomData
      m (stageNumber r) A alpha screen)
    (c : Fin (stageNumber r) → Site)
    (historySet : Set
      (ComplementStoppedBase (primedInitialBase D.first) D.labels D.C
        (primedOddStrictRightWinnerBases D.first D.labels
          D.candidateBases) → ℕ))
    (hmeasurableHistorySet : MeasurableSet historySet)
    (history_eq :
      D.atom ∩ orderedCanonicalHistoryEvent m i a r c =
        D.atom ∩
          primedOddComplementPath m (stageNumber r) D.C D.first D.labels
            (primedOddStrictRightWinnerBases D.first D.labels
              D.candidateBases) ⁻¹' historySet) :
    RefinedAtomScreenEstimate
      (primedOddOrderedHistoryPathAtom
        m i a r D.C D.first D.labels c) screen
      (sourceProp49ScreenRate m A alpha) := by
  rw [RefinedAtomScreenEstimate,
    primedOddOrderedHistoryPathAtom_eq_coarse_inter_history]
  exact primedOddStrictRightWinnerProp49_orderedHistory_screen_le
    D c historySet hmeasurableHistorySet history_eq

theorem primedOddStrictRightWinnerProp49_orderedHistory_screenEstimate_of_fiberwise
    {m A : ℕ} {alpha : ℝ} {screen : Set (ℕ → Site)}
    {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    (D : PrimedOddStrictRightWinnerProp49AtomData
      m (stageNumber r) A alpha screen)
    (c : Fin (stageNumber r) → Site)
    (hdet : EventDeterminedByOn D.atom
      (orderedCanonicalHistoryEvent m i a r c)
      (primedOddComplementPath m (stageNumber r) D.C D.first D.labels
        (primedOddStrictRightWinnerBases D.first D.labels
          D.candidateBases))) :
    RefinedAtomScreenEstimate
      (primedOddOrderedHistoryPathAtom
        m i a r D.C D.first D.labels c) screen
      (sourceProp49ScreenRate m A alpha) := by
  let z := primedOddComplementPath m (stageNumber r) D.C D.first D.labels
    (primedOddStrictRightWinnerBases D.first D.labels D.candidateBases)
  let history := orderedCanonicalHistoryEvent m i a r c
  let H : Set
      (ComplementStoppedBase (primedInitialBase D.first) D.labels D.C
        (primedOddStrictRightWinnerBases D.first D.labels
          D.candidateBases) → ℕ) :=
    {v | ∃ s ∈ D.atom, s ∈ history ∧ z s = v}
  have hH : MeasurableSet H := MeasurableSet.of_discrete
  have heq : D.atom ∩ history = D.atom ∩ z ⁻¹' H := by
    exact inter_eq_inter_preimage_of_eventDeterminedByOn
      D.atom history z hdet
  exact primedOddStrictRightWinnerProp49_orderedHistory_screenEstimate
    D c H hH heq

/-- Unprimed-odd terminal analogue of the checked history tower. -/
theorem unprimedOddTerminalTieLeftProp49_orderedHistory_screen_le
    {m A : ℕ} {alpha : ℝ} {screen : Set (ℕ → Site)}
    {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    (D : UnprimedOddTerminalTieLeftProp49AtomData
      m (stageNumber r) A alpha screen)
    (c : Fin (stageNumber r) → Site)
    (historySet : Set
      (ComplementStoppedBase (0, 0) D.labels D.C
        (unprimedOddTieLeftWinnerBases D.labels
          (unprimedOddTerminalExternalRight D.labels D.terminal)
            D.candidateBases) → ℕ))
    (hmeasurableHistorySet : MeasurableSet historySet)
    (history_eq :
      D.atom ∩ orderedCanonicalHistoryEvent m i a r c =
        D.atom ∩
          unprimedOddTerminalComplementPath m (stageNumber r) D.C D.labels
            D.terminal
            (unprimedOddTieLeftWinnerBases D.labels
              (unprimedOddTerminalExternalRight D.labels D.terminal)
                D.candidateBases) ⁻¹' historySet) :
    simpleRandomWalkLaw
        (D.atom ∩ orderedCanonicalHistoryEvent m i a r c ∩ screen) ≤
      sourceProp49ScreenRate m A alpha *
        simpleRandomWalkLaw
          (D.atom ∩ orderedCanonicalHistoryEvent m i a r c) := by
  let externalRight :=
    unprimedOddTerminalExternalRight D.labels D.terminal
  let activeBases := unprimedOddTieLeftWinnerBases D.labels
    externalRight D.candidateBases
  let complementLaw := stoppedMixedComplementMeasure
    (0, 0) D.labels m D.C activeBases
      (stoppedExternalLeft (0, 0) D.labels) externalRight
  have hgrouped :=
    actualAdmissible_unprimedOddSourceConstraint_eq_mixedBlockPreimage
      m (stageNumber r) D.C D.labels D.terminal D.m_pos D.creation_card
        D.creation_pairFree D.offBase D.terminal_mem
  have hpos := mixedCoordinatePos_of_grouped_nonempty
    (0, 0) D.labels m D.C (stoppedExternalLeft (0, 0) D.labels)
      externalRight
      (actualAdmissibleOddStoppedVectors m (stageNumber r) D.labels
        D.terminal (unprimedOddSourceConstraint m (stageNumber r) D.C
          D.labels D.terminal))
      (by simpa only [externalRight] using hgrouped) D.admissible_nonempty
  letI : IsProbabilityMeasure complementLaw := by
    dsimp only [complementLaw]
    exact stoppedMixedComplementMeasure_isProbabilityMeasure
      (0, 0) D.labels m D.C activeBases
        (stoppedExternalLeft (0, 0) D.labels) externalRight hpos
  let F : StoppedTruncatedProp49HistoryFactorization D.toInput
      (orderedCanonicalHistoryEvent m i a r c) :=
    { Z := ComplementStoppedBase (0, 0) D.labels D.C activeBases → ℕ
      measurableSpaceZ := inferInstance
      complementLaw := complementLaw
      sFiniteComplementLaw := inferInstance
      complement := unprimedOddTerminalComplementPath
        m (stageNumber r) D.C D.labels D.terminal activeBases
      measurable_complement :=
        measurable_unprimedOddTerminalComplementPath
          m (stageNumber r) D.C D.labels D.nondistinguished D.terminal
            activeBases
      historySet := historySet
      measurable_historySet := hmeasurableHistorySet
      history_eq := history_eq
      joint_map_law := by
        change
          (simpleRandomWalkLaw.restrict
              (simpleRandomWalk ''
                (actualOddStoppedVectorEvent m (stageNumber r) D.labels
                    D.terminal (stoppedRunVectorBox D.q m) ∩
                  stoppedSourceCondition m (stageNumber r) D.C))).map
              (fun s ↦
                ((unprimedOddActiveFreePathLazy m (stageNumber r) D.C
                    D.labels D.terminal activeBases s,
                  unprimedOddActiveFreePathNext m (stageNumber r) D.C
                    D.labels D.terminal activeBases s),
                  unprimedOddTerminalComplementPath m (stageNumber r) D.C
                    D.labels D.terminal activeBases s)) =
            simpleRandomWalkLaw
                (simpleRandomWalk ''
                  (actualOddStoppedVectorEvent m (stageNumber r) D.labels
                      D.terminal (stoppedRunVectorBox D.q m) ∩
                    stoppedSourceCondition m (stageNumber r) D.C)) •
              (((sourceTruncatedProfileMeasure m
                (activeFreeStoppedShape (0, 0) D.labels D.C
                  activeBases)).prod directionLaw).prod complementLaw)
        simpa only [activeBases, externalRight, complementLaw] using
          unprimedOdd_tieLeftWinner_active_complement_path_map_law
            m (stageNumber r) D.C D.labels D.nondistinguished D.terminal
              D.m_pos D.k_pos D.creation_card D.creation_pairFree D.offBase
              D.terminal_mem D.admissible_nonempty D.candidateBases }
  exact F.history_screen_le D.toInput

theorem unprimedOddTerminalTieLeftProp49_orderedHistory_screenEstimate
    {m A : ℕ} {alpha : ℝ} {screen : Set (ℕ → Site)}
    {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    (D : UnprimedOddTerminalTieLeftProp49AtomData
      m (stageNumber r) A alpha screen)
    (c : Fin (stageNumber r) → Site)
    (historySet : Set
      (ComplementStoppedBase (0, 0) D.labels D.C
        (unprimedOddTieLeftWinnerBases D.labels
          (unprimedOddTerminalExternalRight D.labels D.terminal)
            D.candidateBases) → ℕ))
    (hmeasurableHistorySet : MeasurableSet historySet)
    (history_eq :
      D.atom ∩ orderedCanonicalHistoryEvent m i a r c =
        D.atom ∩
          unprimedOddTerminalComplementPath m (stageNumber r) D.C D.labels
            D.terminal
            (unprimedOddTieLeftWinnerBases D.labels
              (unprimedOddTerminalExternalRight D.labels D.terminal)
                D.candidateBases) ⁻¹' historySet) :
    RefinedAtomScreenEstimate
      (unprimedOddTerminalOrderedHistoryPathAtom
        m i a r D.C D.labels D.terminal c) screen
      (sourceProp49ScreenRate m A alpha) := by
  rw [RefinedAtomScreenEstimate,
    unprimedOddTerminalOrderedHistoryPathAtom_eq_coarse_inter_history]
  exact unprimedOddTerminalTieLeftProp49_orderedHistory_screen_le
    D c historySet hmeasurableHistorySet history_eq

theorem unprimedOddTerminalTieLeftProp49_orderedHistory_screenEstimate_of_fiberwise
    {m A : ℕ} {alpha : ℝ} {screen : Set (ℕ → Site)}
    {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    (D : UnprimedOddTerminalTieLeftProp49AtomData
      m (stageNumber r) A alpha screen)
    (c : Fin (stageNumber r) → Site)
    (hdet : EventDeterminedByOn D.atom
      (orderedCanonicalHistoryEvent m i a r c)
      (unprimedOddTerminalComplementPath m (stageNumber r) D.C D.labels
        D.terminal
        (unprimedOddTieLeftWinnerBases D.labels
          (unprimedOddTerminalExternalRight D.labels D.terminal)
            D.candidateBases))) :
    RefinedAtomScreenEstimate
      (unprimedOddTerminalOrderedHistoryPathAtom
        m i a r D.C D.labels D.terminal c) screen
      (sourceProp49ScreenRate m A alpha) := by
  let z := unprimedOddTerminalComplementPath m (stageNumber r) D.C D.labels
    D.terminal
    (unprimedOddTieLeftWinnerBases D.labels
      (unprimedOddTerminalExternalRight D.labels D.terminal) D.candidateBases)
  let history := orderedCanonicalHistoryEvent m i a r c
  let H : Set
      (ComplementStoppedBase (0, 0) D.labels D.C
        (unprimedOddTieLeftWinnerBases D.labels
          (unprimedOddTerminalExternalRight D.labels D.terminal)
            D.candidateBases) → ℕ) :=
    {v | ∃ s ∈ D.atom, s ∈ history ∧ z s = v}
  have hH : MeasurableSet H := MeasurableSet.of_discrete
  have heq : D.atom ∩ history = D.atom ∩ z ⁻¹' H := by
    exact inter_eq_inter_preimage_of_eventDeterminedByOn
      D.atom history z hdet
  exact unprimedOddTerminalTieLeftProp49_orderedHistory_screenEstimate
    D c H hH heq

/-- Primed-even terminal analogue of the checked history tower. -/
theorem primedEvenTerminalStrictRightProp49_orderedHistory_screen_le
    {m A : ℕ} {alpha : ℝ} {screen : Set (ℕ → Site)}
    {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    (D : PrimedEvenTerminalStrictRightProp49AtomData
      m (stageNumber r) A alpha screen)
    (c : Fin (stageNumber r) → Site)
    (historySet : Set
      (ComplementStoppedBase (primedInitialBase D.first) D.labels D.C
        (primedEvenStrictRightWinnerBases D.first D.labels
          (primedEvenTerminalExternalLeft D.first D.labels D.terminal)
            D.candidateBases) → ℕ))
    (hmeasurableHistorySet : MeasurableSet historySet)
    (history_eq :
      D.atom ∩ orderedCanonicalHistoryEvent m i a r c =
        D.atom ∩
          primedEvenTerminalComplementPath m (stageNumber r) D.C D.first
            D.labels D.terminal
            (primedEvenStrictRightWinnerBases D.first D.labels
              (primedEvenTerminalExternalLeft D.first D.labels D.terminal)
                D.candidateBases) ⁻¹' historySet) :
    simpleRandomWalkLaw
        (D.atom ∩ orderedCanonicalHistoryEvent m i a r c ∩ screen) ≤
      sourceProp49ScreenRate m A alpha *
        simpleRandomWalkLaw
          (D.atom ∩ orderedCanonicalHistoryEvent m i a r c) := by
  let externalLeft :=
    primedEvenTerminalExternalLeft D.first D.labels D.terminal
  let activeBases := primedEvenStrictRightWinnerBases D.first D.labels
    externalLeft D.candidateBases
  let complementLaw := stoppedMixedComplementMeasure
    (primedInitialBase D.first) D.labels m D.C activeBases externalLeft
      (primedStoppedExternalRight D.first D.labels)
  have hgrouped :=
    actualAdmissible_primedEvenSourceConstraint_eq_mixedBlockPreimage
      m (stageNumber r) D.C D.first D.labels D.terminal D.m_pos
        D.creation_card D.creation_pairFree D.offBase D.terminal_mem
  have hpos := mixedCoordinatePos_of_grouped_nonempty
    (primedInitialBase D.first) D.labels m D.C externalLeft
      (primedStoppedExternalRight D.first D.labels)
      (actualAdmissiblePrimedTerminalVectors m (stageNumber r) D.first
        D.labels D.terminal
          (primedEvenSourceConstraint m (stageNumber r) D.C D.first
            D.labels D.terminal))
      (by simpa only [externalLeft] using hgrouped) D.admissible_nonempty
  letI : IsProbabilityMeasure complementLaw := by
    dsimp only [complementLaw]
    exact stoppedMixedComplementMeasure_isProbabilityMeasure
      (primedInitialBase D.first) D.labels m D.C activeBases externalLeft
        (primedStoppedExternalRight D.first D.labels) hpos
  let F : StoppedTruncatedProp49HistoryFactorization D.toInput
      (orderedCanonicalHistoryEvent m i a r c) :=
    { Z := ComplementStoppedBase (primedInitialBase D.first) D.labels D.C
        activeBases → ℕ
      measurableSpaceZ := inferInstance
      complementLaw := complementLaw
      sFiniteComplementLaw := inferInstance
      complement := primedEvenTerminalComplementPath
        m (stageNumber r) D.C D.first D.labels D.terminal activeBases
      measurable_complement :=
        measurable_primedEvenTerminalComplementPath
          m (stageNumber r) D.C D.first D.labels D.nondistinguished
            D.terminal activeBases
      historySet := historySet
      measurable_historySet := hmeasurableHistorySet
      history_eq := history_eq
      joint_map_law := by
        change
          (simpleRandomWalkLaw.restrict
              (simpleRandomWalk ''
                (actualPrimedTerminalVectorEvent m (stageNumber r) D.first
                    D.labels D.terminal (stoppedRunVectorBox D.q m) ∩
                  stoppedSourceCondition m (stageNumber r) D.C))).map
              (fun s ↦
                ((primedEvenActiveFreePathLazy m (stageNumber r) D.C
                    D.first D.labels D.terminal activeBases s,
                  primedEvenActiveFreePathNext m (stageNumber r) D.C
                    D.first D.labels D.terminal activeBases s),
                  primedEvenTerminalComplementPath m (stageNumber r) D.C
                    D.first D.labels D.terminal activeBases s)) =
            simpleRandomWalkLaw
                (simpleRandomWalk ''
                  (actualPrimedTerminalVectorEvent m (stageNumber r) D.first
                      D.labels D.terminal (stoppedRunVectorBox D.q m) ∩
                    stoppedSourceCondition m (stageNumber r) D.C)) •
              (((sourceTruncatedProfileMeasure m
                (activeFreeStoppedShape (primedInitialBase D.first)
                  D.labels D.C activeBases)).prod directionLaw).prod
                    complementLaw)
        simpa only [activeBases, externalLeft, complementLaw] using
          primedEven_strictRightWinner_active_complement_path_map_law
            m (stageNumber r) D.C D.first D.labels D.nondistinguished
              D.terminal D.m_pos D.k_pos D.creation_card
              D.creation_pairFree D.offBase D.terminal_mem
              D.admissible_nonempty D.candidateBases }
  exact F.history_screen_le D.toInput

theorem primedEvenTerminalStrictRightProp49_orderedHistory_screenEstimate
    {m A : ℕ} {alpha : ℝ} {screen : Set (ℕ → Site)}
    {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    (D : PrimedEvenTerminalStrictRightProp49AtomData
      m (stageNumber r) A alpha screen)
    (c : Fin (stageNumber r) → Site)
    (historySet : Set
      (ComplementStoppedBase (primedInitialBase D.first) D.labels D.C
        (primedEvenStrictRightWinnerBases D.first D.labels
          (primedEvenTerminalExternalLeft D.first D.labels D.terminal)
            D.candidateBases) → ℕ))
    (hmeasurableHistorySet : MeasurableSet historySet)
    (history_eq :
      D.atom ∩ orderedCanonicalHistoryEvent m i a r c =
        D.atom ∩
          primedEvenTerminalComplementPath m (stageNumber r) D.C D.first
            D.labels D.terminal
            (primedEvenStrictRightWinnerBases D.first D.labels
              (primedEvenTerminalExternalLeft D.first D.labels D.terminal)
                D.candidateBases) ⁻¹' historySet) :
    RefinedAtomScreenEstimate
      (primedEvenTerminalOrderedHistoryPathAtom
        m i a r D.C D.first D.labels D.terminal c) screen
      (sourceProp49ScreenRate m A alpha) := by
  rw [RefinedAtomScreenEstimate,
    primedEvenTerminalOrderedHistoryPathAtom_eq_coarse_inter_history]
  exact primedEvenTerminalStrictRightProp49_orderedHistory_screen_le
    D c historySet hmeasurableHistorySet history_eq

theorem primedEvenTerminalStrictRightProp49_orderedHistory_screenEstimate_of_fiberwise
    {m A : ℕ} {alpha : ℝ} {screen : Set (ℕ → Site)}
    {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    (D : PrimedEvenTerminalStrictRightProp49AtomData
      m (stageNumber r) A alpha screen)
    (c : Fin (stageNumber r) → Site)
    (hdet : EventDeterminedByOn D.atom
      (orderedCanonicalHistoryEvent m i a r c)
      (primedEvenTerminalComplementPath m (stageNumber r) D.C D.first
        D.labels D.terminal
        (primedEvenStrictRightWinnerBases D.first D.labels
          (primedEvenTerminalExternalLeft D.first D.labels D.terminal)
            D.candidateBases))) :
    RefinedAtomScreenEstimate
      (primedEvenTerminalOrderedHistoryPathAtom
        m i a r D.C D.first D.labels D.terminal c) screen
      (sourceProp49ScreenRate m A alpha) := by
  let z := primedEvenTerminalComplementPath m (stageNumber r) D.C D.first
    D.labels D.terminal
    (primedEvenStrictRightWinnerBases D.first D.labels
      (primedEvenTerminalExternalLeft D.first D.labels D.terminal)
        D.candidateBases)
  let history := orderedCanonicalHistoryEvent m i a r c
  let H : Set
      (ComplementStoppedBase (primedInitialBase D.first) D.labels D.C
        (primedEvenStrictRightWinnerBases D.first D.labels
          (primedEvenTerminalExternalLeft D.first D.labels D.terminal)
            D.candidateBases) → ℕ) :=
    {v | ∃ s ∈ D.atom, s ∈ history ∧ z s = v}
  have hH : MeasurableSet H := MeasurableSet.of_discrete
  have heq : D.atom ∩ history = D.atom ∩ z ⁻¹' H := by
    exact inter_eq_inter_preimage_of_eventDeterminedByOn
      D.atom history z hdet
  exact primedEvenTerminalStrictRightProp49_orderedHistory_screenEstimate
    D c H hH heq

/-! ### Profile-generic history refinement

The local stopped laws do not depend on which of the six external-profile
families is used to describe the preceding Proposition-4.7 history.  The
following wrapper therefore refines any measurable raw path atom by the
ordered history for an arbitrary one-step-adapted profile family.  In
particular it applies directly to `sourceCanonicalProfiles`, without passing
through the auxiliary endpoint-adapted column profiles. -/

noncomputable def orderedProfileHistoryPathAtom
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (c : Fin (stageNumber r) → Site) (baseAtom : Set (ℕ → Site)) :
    Set (ℕ → Site) :=
  baseAtom ∩ orderedProfileHistoryEvent profiles cStar m i a r c

theorem measurableSet_orderedProfileHistoryPathAtom
    (profiles : Fin 6 → ExternalProfilePair)
    (hadapt : OneStepAdaptedProfiles profiles) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (c : Fin (stageNumber r) → Site) (baseAtom : Set (ℕ → Site))
    (hm : 0 < m) (hbase : MeasurableSet baseAtom) :
    MeasurableSet
      (orderedProfileHistoryPathAtom profiles cStar
        m i a r c baseAtom) :=
  hbase.inter (measurableSet_orderedProfileHistoryEvent
    profiles hadapt cStar m i a r c hm)

theorem orderedProfileHistoryPathAtom_subset_history
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (c : Fin (stageNumber r) → Site) (baseAtom : Set (ℕ → Site)) :
    orderedProfileHistoryPathAtom profiles cStar m i a r c baseAtom ⊆
      prop47History profiles cStar m i a r.1 := by
  intro s hs
  exact hs.2.2

theorem orderedProfileHistoryPathAtom_prop49_local
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (c : Fin (stageNumber r) → Site) (baseAtom screen : Set (ℕ → Site))
    (rate : ℝ≥0∞)
    (hsource : RefinedAtomScreenEstimate
      (orderedProfileHistoryPathAtom profiles cStar
        m i a r c baseAtom) screen rate) :
    simpleRandomWalkLaw
        (orderedProfileHistoryPathAtom profiles cStar m i a r c baseAtom ∩
          prop47History profiles cStar m i a r.1 ∩ screen) ≤
      rate * simpleRandomWalkLaw
        (orderedProfileHistoryPathAtom profiles cStar m i a r c baseAtom ∩
          prop47History profiles cStar m i a r.1) :=
  refinedAtom_history_screen_le
    (orderedProfileHistoryPathAtom profiles cStar m i a r c baseAtom)
    (prop47History profiles cStar m i a r.1) screen rate
    (orderedProfileHistoryPathAtom_subset_history
      profiles cStar m i a r c baseAtom) hsource

theorem measurableSet_orderedSourceHistoryPathAtom
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (c : Fin (stageNumber r) → Site) (baseAtom : Set (ℕ → Site))
    (hm : 0 < m) (hbase : MeasurableSet baseAtom) :
    MeasurableSet
      (orderedProfileHistoryPathAtom sourceCanonicalProfiles canonicalCStar
        m i a r c baseAtom) :=
  measurableSet_orderedProfileHistoryPathAtom sourceCanonicalProfiles
    sourceCanonicalProfiles_oneStepAdapted canonicalCStar
      m i a r c baseAtom hm hbase

/-- Source-facing form of the refined finite-branch Proposition-4.9 input
for atoms that already include the complete preceding history.

Compared with
`Prop47StoppedProfileProp49RefinedFiniteBranchEstimate`, this asks the source
to prove the honest atom inclusion and the unnormalized narrow-band estimate
on that atom.  The history intersections in the connector are then
definitionally redundant.  Covers, within-branch disjointness, and the
narrow-band estimate itself remain explicit. -/
def Prop47StoppedProfileProp49HistoryContainedFiniteBranchEstimate
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (branchCount localCoeff : ℕ)
    (branchScreen : ℕ → Fin 6 → AlphaTriple → StageIndex →
      Fin branchCount → Set (ℕ → Site))
    (refinedAtom : ℕ → Fin 6 → AlphaTriple → StageIndex →
      Fin branchCount → ℕ → Set (ℕ → Site)) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i a (r : StageIndex),
    alphaValue (tripleAlphaIndex a r) ≤ kappaTwo →
    let atom := refinedAtom m i a r
    let history := prop47History profiles cStar m i a r.1
    let fullScreen := HLOZProp47SourceObjects.lowScaleScreenEvent
      (profiles i) (cStar i) i m (stageNumber r)
        (alphaValue (tripleAlphaIndex a r) + delta)
    let screen := branchScreen m i a r
    (∀ j, Pairwise fun n l ↦ Disjoint (atom j n) (atom j l)) ∧
    (∀ j n, MeasurableSet (atom j n)) ∧
    history ∩ fullScreen ⊆ ⋃ j, history ∩ screen j ∧
    (∀ j, history ∩ screen j ⊆ ⋃ n, atom j n) ∧
    ∀ j n,
      atom j n ⊆ history ∧
      RefinedAtomScreenEstimate (atom j n) (screen j)
        (sourceProp49ScreenRate m localCoeff
          (alphaValue (tripleAlphaIndex a r)))

/-- History-contained source atoms supply exactly the local field of the
finite-branch Proposition-4.9 connector. -/
theorem prop47StoppedProfileProp49RefinedFiniteBranchEstimate_of_historyContained
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (branchCount localCoeff : ℕ)
    (branchScreen : ℕ → Fin 6 → AlphaTriple → StageIndex →
      Fin branchCount → Set (ℕ → Site))
    (refinedAtom : ℕ → Fin 6 → AlphaTriple → StageIndex →
      Fin branchCount → ℕ → Set (ℕ → Site))
    (hsource :
      Prop47StoppedProfileProp49HistoryContainedFiniteBranchEstimate
        profiles cStar branchCount localCoeff branchScreen refinedAtom) :
    HLOZProp47LowStageConnector.Prop47StoppedProfileProp49RefinedFiniteBranchEstimate
      profiles cStar branchCount localCoeff
      branchScreen refinedAtom := by
  filter_upwards [hsource] with m hm
  intro i a r halpha
  rcases hm i a r halpha with
    ⟨hdisjoint, hmeasurable, hbranchCover, hatomCover, hlocal⟩
  refine ⟨hdisjoint, hmeasurable, hbranchCover, hatomCover, ?_⟩
  intro j n
  rcases hlocal j n with ⟨hsubset, hscreen⟩
  exact refinedAtom_history_screen_le
    (refinedAtom m i a r j n)
    (prop47History profiles cStar m i a r.1)
    (branchScreen m i a r j)
    (sourceProp49ScreenRate m localCoeff
      (alphaValue (tripleAlphaIndex a r)))
    hsubset hscreen

/-! ### Ordered-history atoms as the source-facing finite-branch interface -/

/-- Refine a raw stopped atom by the ordered creation tuple and the complete
preceding history for the literal source profile family. -/
noncomputable def sourceOrderedHistoryRefinedAtom
    {branchCount : ℕ}
    (baseAtom : (m : ℕ) → (i : Fin 6) → AlphaTriple → (r : StageIndex) →
      Fin branchCount → ℕ → Set (ℕ → Site))
    (creation : (m : ℕ) → (i : Fin 6) → AlphaTriple → (r : StageIndex) →
      Fin branchCount → ℕ → Fin (stageNumber r) → Site)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (j : Fin branchCount) (n : ℕ) : Set (ℕ → Site) :=
  orderedProfileHistoryPathAtom sourceCanonicalProfiles canonicalCStar
    m i a r (creation m i a r j n) (baseAtom m i a r j n)

/-- The strongest generic Proposition-4.9 source interface built from raw
stopped atoms.  Measurability of the refined atoms and their containment in
the complete preceding history are consequences of the definition above.
Only within-branch disjointness, the two honest event covers, and the
history-retained local narrow-band estimate remain. -/
def Prop47StoppedProfileProp49OrderedFiniteBranchEstimate
    (branchCount localCoeff : ℕ)
    (branchScreen : ℕ → Fin 6 → AlphaTriple → StageIndex →
      Fin branchCount → Set (ℕ → Site))
    (baseAtom : (m : ℕ) → (i : Fin 6) → AlphaTriple → (r : StageIndex) →
      Fin branchCount → ℕ → Set (ℕ → Site))
    (creation : (m : ℕ) → (i : Fin 6) → AlphaTriple → (r : StageIndex) →
      Fin branchCount → ℕ → Fin (stageNumber r) → Site) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i a (r : StageIndex),
    alphaValue (tripleAlphaIndex a r) ≤ kappaTwo →
    let atom := sourceOrderedHistoryRefinedAtom baseAtom creation m i a r
    let history := prop47History sourceCanonicalProfiles canonicalCStar
      m i a r.1
    let fullScreen := HLOZProp47SourceObjects.lowScaleScreenEvent
      (sourceCanonicalProfiles i) (canonicalCStar i) i m (stageNumber r)
        (alphaValue (tripleAlphaIndex a r) + delta)
    let screen := branchScreen m i a r
    (∀ j, Pairwise fun n l ↦
      Disjoint (baseAtom m i a r j n) (baseAtom m i a r j l)) ∧
    (∀ j n, MeasurableSet (baseAtom m i a r j n)) ∧
    history ∩ fullScreen ⊆ ⋃ j, history ∩ screen j ∧
    (∀ j, history ∩ screen j ⊆ ⋃ n, atom j n) ∧
    ∀ j n, RefinedAtomScreenEstimate (atom j n) (screen j)
      (sourceProp49ScreenRate m localCoeff
        (alphaValue (tripleAlphaIndex a r)))

/-- Raw ordered-history source atoms supply the history-contained connector.
Intersection preserves disjointness, one-step adaptedness supplies
measurability, and the defining history intersection supplies containment. -/
theorem prop47StoppedProfileProp49HistoryContainedFiniteBranchEstimate_of_ordered
    (branchCount localCoeff : ℕ)
    (branchScreen : ℕ → Fin 6 → AlphaTriple → StageIndex →
      Fin branchCount → Set (ℕ → Site))
    (baseAtom : (m : ℕ) → (i : Fin 6) → AlphaTriple → (r : StageIndex) →
      Fin branchCount → ℕ → Set (ℕ → Site))
    (creation : (m : ℕ) → (i : Fin 6) → AlphaTriple → (r : StageIndex) →
      Fin branchCount → ℕ → Fin (stageNumber r) → Site)
    (hsource : Prop47StoppedProfileProp49OrderedFiniteBranchEstimate
      branchCount localCoeff branchScreen baseAtom creation) :
    Prop47StoppedProfileProp49HistoryContainedFiniteBranchEstimate
      sourceCanonicalProfiles canonicalCStar branchCount localCoeff
      branchScreen (sourceOrderedHistoryRefinedAtom baseAtom creation) := by
  filter_upwards [hsource, eventually_ge_atTop (1 : ℕ)] with m hm hmpos
  intro i a r halpha
  rcases hm i a r halpha with
    ⟨hdisjoint, hmeasurable, hbranchCover, hatomCover, hlocal⟩
  refine ⟨?_, ?_, hbranchCover, hatomCover, ?_⟩
  · intro j n l hne
    exact (hdisjoint j hne).mono inter_subset_left inter_subset_left
  · intro j n
    exact measurableSet_orderedSourceHistoryPathAtom
      m i a r (creation m i a r j n) (baseAtom m i a r j n)
        (by omega) (hmeasurable j n)
  · intro j n
    exact ⟨orderedProfileHistoryPathAtom_subset_history
      sourceCanonicalProfiles canonicalCStar m i a r
        (creation m i a r j n) (baseAtom m i a r j n), hlocal j n⟩

end Erdos1166.HLOZStoppedHistoryFactorization
