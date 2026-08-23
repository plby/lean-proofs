import ErdosProblems.Erdos1166.Erdos1166HLOZStoppedHistoryFactorization

namespace Erdos1166.HLOZStoppedFullComplement

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory BigOperators
open HLOZDecomposition HLOZActualStopped HLOZIncompleteStoppedBlocks
  HLOZPrimedStopped HLOZPrimedOddMixedReconstruction
  HLOZPrimedOddRightWinner HLOZTerminalParityWinner
  HLOZStoppedMapLaw HLOZStoppedHistoryFactorization HLOZProp48Truncated
  HLOZStoppedSourcePartition HLOZStoppedMixedReconstruction
  HLOZStoppedMapLawReduced HLOZStoppedShape HLOZSourceInstantiation
  HLOZProp47LowStageConnector HLOZProp47Parameters HLOZProp47SourceObjects
  HLOZProp47SourceAssembly HLOZPairing

/-- Conditioning a finite product on a product of measurable coordinate
events preserves the product structure. -/
theorem pi_cond_pi_eq_pi_cond
    {B : Type*} [Fintype B]
    {X : B → Type*} [∀ b, MeasurableSpace (X b)]
    [∀ b, MeasurableSingletonClass (X b)] [∀ b, Countable (X b)]
    (μ : ∀ b, Measure (X b)) [∀ b, IsProbabilityMeasure (μ b)]
    (E : ∀ b, Set (X b)) (hE : ∀ b, MeasurableSet (E b))
    (hpos : ∀ b, μ b (E b) ≠ 0) :
    (Measure.pi μ)[|Set.pi Set.univ E] =
      Measure.pi (fun b ↦ (μ b)[|E b]) := by
  letI (b : B) : IsProbabilityMeasure ((μ b)[|E b]) :=
    cond_isProbabilityMeasure (hpos b)
  have hmEvent : MeasurableSet (Set.pi Set.univ E) :=
    MeasurableSet.univ_pi hE
  apply Measure.ext_of_singleton
  intro x
  rw [cond_apply hmEvent, Measure.pi_singleton]
  rw [show Set.pi Set.univ E ∩ {x} =
      Set.pi Set.univ (fun b ↦ E b ∩ {x b}) by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_pi,
      Set.mem_univ, true_implies]
    constructor
    · rintro ⟨hy, rfl⟩ b
      exact ⟨hy b, rfl⟩
    · intro hy
      have hyx : y = x := funext fun b ↦ (hy b).2
      exact ⟨fun b ↦ (hy b).1, hyx⟩]
  rw [Measure.pi_pi, Measure.pi_pi]
  simp_rw [cond_apply (hE _)]
  rw [Finset.prod_mul_distrib]
  congr 1
  apply ENNReal.prod_inv_distrib
  intro i _hi _j _hj _hij
  exact Or.inl (hpos i)

/-- Conditioning commutes with a measurable pushforward when the event is
pulled back from the target. -/
theorem cond_preimage_map
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (f : X → Y) (E : Set Y)
    (hf : Measurable f) (hE : MeasurableSet E) :
    (μ[|f ⁻¹' E]).map f = (μ.map f)[|E] := by
  ext s hs
  rw [Measure.map_apply hf hs, cond_apply (hE.preimage hf), cond_apply hE,
    Measure.map_apply hf hE, Measure.map_apply hf (hE.inter hs)]
  rfl

/-- The conditional law of all chronological runs in one external-base
fiber. -/
noncomputable def stoppedMixedBlockRunMeasure {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (m : ℕ)
    (C : Finset Site)
    (externalLeft externalRight : StoppedExternalBase a labels → ℕ)
    (b : StoppedExternalBase a labels) :
    Measure (StoppedExternalIndex a labels b → ℕ) :=
  (Measure.pi fun _ : StoppedExternalIndex a labels b ↦ HLOZUrn.runMeasure)[|
    (fun w ↦ ∑ i, w i) ⁻¹'
      (stoppedMixedBlockValues a labels m C externalLeft externalRight b : Set ℕ)]

theorem stoppedMixedBlockRunMeasure_map_sum {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (m : ℕ)
    (C : Finset Site)
    (externalLeft externalRight : StoppedExternalBase a labels → ℕ)
    (b : StoppedExternalBase a labels) :
    (stoppedMixedBlockRunMeasure a labels m C externalLeft externalRight b).map
        (fun w ↦ ∑ i, w i) =
      (HLOZUrn.negBinMeasure
        (Fintype.card (StoppedExternalIndex a labels b)))[|
          (stoppedMixedBlockValues a labels m C
            externalLeft externalRight b : Set ℕ)] := by
  rw [stoppedMixedBlockRunMeasure, cond_preimage_map]
  · rw [stoppedBlockSum_map_eq_negBinMeasure]
  · exact measurable_of_countable _
  · exact (stoppedMixedBlockValues a labels m C
      externalLeft externalRight b).measurableSet

theorem stoppedMixedBlockRunMeasure_isProbabilityMeasure {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (m : ℕ)
    (C : Finset Site)
    (externalLeft externalRight : StoppedExternalBase a labels → ℕ)
    (b : StoppedExternalBase a labels)
    (hpos : HLOZUrn.negBinMeasure
      (Fintype.card (StoppedExternalIndex a labels b))
        (stoppedMixedBlockValues a labels m C
          externalLeft externalRight b : Set ℕ) ≠ 0) :
    IsProbabilityMeasure
      (stoppedMixedBlockRunMeasure a labels m C
        externalLeft externalRight b) := by
  unfold stoppedMixedBlockRunMeasure
  apply cond_isProbabilityMeasure
  have hmap := stoppedBlockSum_map_eq_negBinMeasure a labels b
  have heval :
      (Measure.map (fun w : StoppedExternalIndex a labels b → ℕ ↦ ∑ i, w i)
          (Measure.pi fun _ : StoppedExternalIndex a labels b ↦
            HLOZUrn.runMeasure))
          (stoppedMixedBlockValues a labels m C
            externalLeft externalRight b : Set ℕ) =
        (Measure.pi fun _ : StoppedExternalIndex a labels b ↦
          HLOZUrn.runMeasure)
          ((fun w ↦ ∑ i, w i) ⁻¹'
            (stoppedMixedBlockValues a labels m C
              externalLeft externalRight b : Set ℕ)) :=
    Measure.map_apply (measurable_of_countable _)
      (stoppedMixedBlockValues a labels m C
        externalLeft externalRight b).measurableSet
  rw [hmap] at heval
  exact heval.symm ▸ hpos

/-- The full chronological run vectors on all complementary bases. -/
abbrev ComplementStoppedRuns {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (C : Finset Site)
    (activeBases : Finset (StoppedExternalBase a labels)) :=
  ∀ b : ComplementStoppedBase a labels C activeBases,
    StoppedExternalIndex a labels b.1 → ℕ

/-- Restrict a nested chronological run vector to complementary bases,
without summing repeated visits. -/
def restrictComplementStoppedRuns {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (C : Finset Site)
    (activeBases : Finset (StoppedExternalBase a labels))
    (w : ∀ b : StoppedExternalBase a labels,
      StoppedExternalIndex a labels b → ℕ) :
    ComplementStoppedRuns a labels C activeBases :=
  fun b ↦ w b.1

theorem measurable_restrictComplementStoppedRuns {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (C : Finset Site)
    (activeBases : Finset (StoppedExternalBase a labels)) :
    Measurable (restrictComplementStoppedRuns a labels C activeBases) :=
  measurable_of_countable _

/-- Product law of the complete chronological run vectors outside the
active free bases. -/
noncomputable def stoppedMixedComplementRunMeasure {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (m : ℕ)
    (C : Finset Site) (activeBases : Finset (StoppedExternalBase a labels))
    (externalLeft externalRight : StoppedExternalBase a labels → ℕ) :
    Measure (ComplementStoppedRuns a labels C activeBases) :=
  Measure.pi fun b ↦ stoppedMixedBlockRunMeasure
    a labels m C externalLeft externalRight b.1

theorem stoppedMixedComplementRunMeasure_isProbabilityMeasure {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (m : ℕ)
    (C : Finset Site) (activeBases : Finset (StoppedExternalBase a labels))
    (externalLeft externalRight : StoppedExternalBase a labels → ℕ)
    (hpos : ∀ b, HLOZUrn.negBinMeasure
      (Fintype.card (StoppedExternalIndex a labels b))
        (stoppedMixedBlockValues a labels m C
          externalLeft externalRight b : Set ℕ) ≠ 0) :
    IsProbabilityMeasure
      (stoppedMixedComplementRunMeasure a labels m C activeBases
        externalLeft externalRight) := by
  unfold stoppedMixedComplementRunMeasure
  letI (b : ComplementStoppedBase a labels C activeBases) :
      IsProbabilityMeasure (stoppedMixedBlockRunMeasure
        a labels m C externalLeft externalRight b.1) :=
    stoppedMixedBlockRunMeasure_isProbabilityMeasure
      a labels m C externalLeft externalRight b.1 (hpos b.1)
  infer_instance

/-- The mixed constraint before block summation, stated on the nested
chronological run vector. -/
def stoppedMixedBlockRunEvent {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (m : ℕ)
    (C : Finset Site)
    (externalLeft externalRight : StoppedExternalBase a labels → ℕ) :
    Set (∀ b : StoppedExternalBase a labels,
      StoppedExternalIndex a labels b → ℕ) :=
  Set.pi Set.univ fun b ↦
    (fun w ↦ ∑ i, w i) ⁻¹'
      (stoppedMixedBlockValues a labels m C
        externalLeft externalRight b : Set ℕ)

theorem stoppedBlockRunMeasure_cond_mixed_eq_pi_run_cond {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (m : ℕ)
    (C : Finset Site)
    (externalLeft externalRight : StoppedExternalBase a labels → ℕ)
    (hpos : ∀ b, HLOZUrn.negBinMeasure
      (Fintype.card (StoppedExternalIndex a labels b))
        (stoppedMixedBlockValues a labels m C
          externalLeft externalRight b : Set ℕ) ≠ 0) :
    (stoppedBlockRunMeasure a labels)[|
        stoppedMixedBlockRunEvent a labels m C externalLeft externalRight] =
      Measure.pi fun b ↦ stoppedMixedBlockRunMeasure
        a labels m C externalLeft externalRight b := by
  let μ := fun _b : StoppedExternalBase a labels ↦
    Measure.pi fun _i : StoppedExternalIndex a labels _b ↦ HLOZUrn.runMeasure
  let E := fun b : StoppedExternalBase a labels ↦
    (fun w : StoppedExternalIndex a labels b → ℕ ↦ ∑ i, w i) ⁻¹'
      (stoppedMixedBlockValues a labels m C
        externalLeft externalRight b : Set ℕ)
  have hE : ∀ b, MeasurableSet (E b) := fun _ ↦ MeasurableSet.of_discrete
  have hrunpos : ∀ b, μ b (E b) ≠ 0 := by
    intro b
    dsimp only [μ, E]
    have hmap := stoppedBlockSum_map_eq_negBinMeasure a labels b
    have heval :
        (Measure.map (fun w : StoppedExternalIndex a labels b → ℕ ↦ ∑ i, w i)
            (Measure.pi fun _ : StoppedExternalIndex a labels b ↦
              HLOZUrn.runMeasure))
            (stoppedMixedBlockValues a labels m C
              externalLeft externalRight b : Set ℕ) =
          (Measure.pi fun _ : StoppedExternalIndex a labels b ↦
            HLOZUrn.runMeasure)
            ((fun w ↦ ∑ i, w i) ⁻¹'
              (stoppedMixedBlockValues a labels m C
                externalLeft externalRight b : Set ℕ)) :=
      Measure.map_apply (measurable_of_countable _)
        (stoppedMixedBlockValues a labels m C
          externalLeft externalRight b).measurableSet
    rw [hmap] at heval
    exact heval.symm ▸ hpos b
  simpa only [stoppedBlockRunMeasure, stoppedMixedBlockRunEvent,
    stoppedMixedBlockRunMeasure, μ, E] using
      pi_cond_pi_eq_pi_cond μ E hE hrunpos

/-- Exact active-sum/full-complement factorization.  Unlike the earlier
block-sum complement, the second component retains every chronological run
coordinate, so it does not erase creation-order information. -/
theorem stoppedBlockRunMeasure_cond_mixed_map_active_fullComplement {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (m : ℕ)
    (C : Finset Site)
    (activeBases : Finset (StoppedExternalBase a labels))
    (externalLeft externalRight : StoppedExternalBase a labels → ℕ)
    (hpos : ∀ b, HLOZUrn.negBinMeasure
      (Fintype.card (StoppedExternalIndex a labels b))
        (stoppedMixedBlockValues a labels m C
          externalLeft externalRight b : Set ℕ) ≠ 0) :
    ((stoppedBlockRunMeasure a labels)[|
      stoppedMixedBlockRunEvent a labels m C
        externalLeft externalRight]).map
        (fun w ↦
          ((fun b : ActiveFreeStoppedBase a labels C activeBases ↦
              ∑ i, w b.1 i),
            restrictComplementStoppedRuns a labels C activeBases w)) =
      (sourceCappedProfileMeasure m
        (activeFreeStoppedShape a labels C activeBases)
        (activeFreeCapProfile a labels C activeBases
          externalLeft externalRight)).prod
        (stoppedMixedComplementRunMeasure a labels m C activeBases
          externalLeft externalRight) := by
  classical
  let p : StoppedExternalBase a labels → Prop := fun b ↦
    b ∈ activeBases ∧ b.1 ∉ C ∧ b.1 + paperE1 ∉ C
  let μ : (b : StoppedExternalBase a labels) →
      Measure (StoppedExternalIndex a labels b → ℕ) := fun b ↦
    stoppedMixedBlockRunMeasure a labels m C
      externalLeft externalRight b
  letI (b : StoppedExternalBase a labels) :
      IsProbabilityMeasure (μ b) :=
    stoppedMixedBlockRunMeasure_isProbabilityMeasure
      a labels m C externalLeft externalRight b (hpos b)
  let activeFullLaw := Measure.pi fun b : ActiveFreeStoppedBase
      a labels C activeBases ↦ μ b.1
  let complementLaw := stoppedMixedComplementRunMeasure
    a labels m C activeBases externalLeft externalRight
  let sumActive := fun
      w : ∀ b : ActiveFreeStoppedBase a labels C activeBases,
        StoppedExternalIndex a labels b.1 → ℕ ↦
    fun b ↦ ∑ i, w b i
  have hcond :
      (stoppedBlockRunMeasure a labels)[|
          stoppedMixedBlockRunEvent a labels m C
            externalLeft externalRight] = Measure.pi μ := by
    simpa only [μ] using
      stoppedBlockRunMeasure_cond_mixed_eq_pi_run_cond
        a labels m C externalLeft externalRight hpos
  have hsplit : (Measure.pi μ).map
      (MeasurableEquiv.piEquivPiSubtypeProd
        (fun b : StoppedExternalBase a labels ↦
          StoppedExternalIndex a labels b → ℕ) p) =
      activeFullLaw.prod complementLaw := by
    simpa only [activeFullLaw, complementLaw, p, μ,
      stoppedMixedComplementRunMeasure] using
      (measurePreserving_piEquivPiSubtypeProd μ p).map_eq
  have hactive : activeFullLaw.map sumActive =
      sourceCappedProfileMeasure m
        (activeFreeStoppedShape a labels C activeBases)
        (activeFreeCapProfile a labels C activeBases
          externalLeft externalRight) := by
    dsimp only [activeFullLaw, sumActive]
    rw [Measure.pi_map_pi]
    · congr 1
      funext b
      simpa only [μ, activeFreeStoppedShape,
        activeFreeCapProfile,
        stoppedMixedBlockValues_activeFree_eq_sourceBelowSet] using
        stoppedMixedBlockRunMeasure_map_sum
          a labels m C externalLeft externalRight b.1
    · intro b
      exact (measurable_of_countable _).aemeasurable
  have hsum : Measurable sumActive := measurable_of_countable _
  have hsplitMeas : Measurable
      (MeasurableEquiv.piEquivPiSubtypeProd
        (fun b : StoppedExternalBase a labels ↦
          StoppedExternalIndex a labels b → ℕ) p) :=
    (MeasurableEquiv.piEquivPiSubtypeProd
      (fun b : StoppedExternalBase a labels ↦
        StoppedExternalIndex a labels b → ℕ) p).measurable
  rw [hcond]
  change (Measure.pi μ).map
      ((Prod.map sumActive id) ∘
        MeasurableEquiv.piEquivPiSubtypeProd
          (fun b : StoppedExternalBase a labels ↦
            StoppedExternalIndex a labels b → ℕ) p) = _
  rw [← Measure.map_map (hsum.prodMap measurable_id) hsplitMeas, hsplit]
  rw [← Measure.map_prod_map activeFullLaw complementLaw hsum measurable_id]
  rw [hactive, Measure.map_id]

theorem stoppedPaperBlockVector_preimage_mixedRunEvent {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (m : ℕ)
    (C : Finset Site)
    (externalLeft externalRight : StoppedExternalBase a labels → ℕ) :
    stoppedPaperBlockVector a labels ⁻¹'
        stoppedMixedBlockRunEvent a labels m C
          externalLeft externalRight =
      (fun v ↦ stoppedPaperBlockSums a labels
        (stoppedPaperBlockVector a labels v)) ⁻¹'
        stoppedMixedBlockSumEvent a labels m C
          externalLeft externalRight := by
  rw [stoppedMixedBlockSumEvent_eq_blockEvent]
  ext v
  simp [stoppedMixedBlockRunEvent, HLOZConditionalProduct.blockEvent,
    stoppedPaperBlockSums]

/-- Generic source-law form of the full chronological complement split.
The input is the literal stopped run-vector law plus its fresh direction;
the output keeps all nonactive chronological coordinates rather than only
their per-base sums. -/
theorem activeFree_fullComplement_capped_hasLaw_of_joint {q : ℕ}
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
        (((fun b : ActiveFreeStoppedBase a labels C activeBases ↦
            ∑ i, stoppedPaperBlockVector a labels (X omega) b.1 i),
          D omega),
        restrictComplementStoppedRuns a labels C activeBases
          (stoppedPaperBlockVector a labels (X omega))))
      (((sourceCappedProfileMeasure m
          (activeFreeStoppedShape a labels C activeBases)
          (activeFreeCapProfile a labels C activeBases
            externalLeft externalRight)).prod directionLaw).prod
        (stoppedMixedComplementRunMeasure a labels m C activeBases
          externalLeft externalRight)) P := by
  let B := ∀ b : StoppedExternalBase a labels,
    StoppedExternalIndex a labels b → ℕ
  let f : B →
      (ActiveFreeStoppedBase a labels C activeBases → ℕ) ×
        ComplementStoppedRuns a labels C activeBases := fun w ↦
    ((fun b ↦ ∑ i, w b.1 i),
      restrictComplementStoppedRuns a labels C activeBases w)
  have hV : (V : Set (Fin (q + 1) → ℕ)) =
      stoppedPaperBlockVector a labels ⁻¹'
        stoppedMixedBlockRunEvent a labels m C
          externalLeft externalRight := by
    rw [hGroupedEvent,
      stoppedPaperBlockVector_preimage_mixedRunEvent]
  have hmapBlock :
      ((HLOZUrn.runVectorMeasure (q + 1))[|(V : Set _)]).map
          (stoppedPaperBlockVector a labels) =
        (stoppedBlockRunMeasure a labels)[|
          stoppedMixedBlockRunEvent a labels m C
            externalLeft externalRight] := by
    rw [hV]
    rw [cond_preimage_map]
    · exact runVectorMeasure_map_stoppedPaperBlockVector a labels ▸ rfl
    · exact measurable_stoppedPaperBlockVector a labels
    · exact MeasurableSet.of_discrete
  have hf : Measurable f := measurable_of_countable _
  have hmapF :
      ((HLOZUrn.runVectorMeasure (q + 1))[|(V : Set _)]).map
          (f ∘ stoppedPaperBlockVector a labels) =
        (sourceCappedProfileMeasure m
          (activeFreeStoppedShape a labels C activeBases)
          (activeFreeCapProfile a labels C activeBases
            externalLeft externalRight)).prod
          (stoppedMixedComplementRunMeasure a labels m C activeBases
            externalLeft externalRight) := by
    rw [← Measure.map_map hf (measurable_stoppedPaperBlockVector a labels),
      hmapBlock]
    simpa only [f, B] using
      stoppedBlockRunMeasure_cond_mixed_map_active_fullComplement
        a labels m C activeBases externalLeft externalRight
          hMixedCoordinatePos
  simpa only [f, B, Function.comp_apply] using
    hasLaw_split_prod_direction hjoint
      (f ∘ stoppedPaperBlockVector a labels)
      (hf.comp (measurable_stoppedPaperBlockVector a labels)) hmapF

/-! ### Unprimed-even path specialization -/

/-- Every unsummed chronological run coordinate on a complementary base. -/
noncomputable def unprimedEvenFullComplementStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    (ℕ → Direction) → ComplementStoppedRuns (0, 0) labels C activeBases :=
  fun omega ↦
    restrictComplementStoppedRuns (0, 0) labels C activeBases
      (stoppedPaperBlockVector (0, 0) labels
        (actualStoppedVector m k labels
          (unprimedEvenSourceConstraint m k C labels) omega))

theorem measurable_unprimedEvenFullComplementStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    Measurable
      (unprimedEvenFullComplementStatistic m k C labels activeBases) := by
  exact (measurable_restrictComplementStoppedRuns
    (0, 0) labels C activeBases).comp
      ((measurable_stoppedPaperBlockVector (0, 0) labels).comp
        (measurable_actualStoppedVector m k labels hnondist
          (unprimedEvenSourceConstraint m k C labels)))

noncomputable def unprimedEvenActiveFullComplementStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    (ℕ → Direction) →
      ((ActiveFreeStoppedBase (0, 0) labels C activeBases → ℕ) ×
        Direction) × ComplementStoppedRuns (0, 0) labels C activeBases :=
  fun omega ↦
    (((fun b ↦ ∑ i,
        stoppedPaperBlockVector (0, 0) labels
          (actualStoppedVector m k labels
            (unprimedEvenSourceConstraint m k C labels) omega) b.1 i),
      incrementShiftAfter (stoppedCreationTime m k) omega 0),
    unprimedEvenFullComplementStatistic m k C labels activeBases omega)

theorem measurable_unprimedEvenActiveFullComplementStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    Measurable
      (unprimedEvenActiveFullComplementStatistic
        m k C labels activeBases) := by
  exact (measurable_unprimedEvenActiveFreeStatistic
    m k C labels hnondist activeBases).prodMk
      (measurable_unprimedEvenFullComplementStatistic
        m k C labels hnondist activeBases)

/-- Literal unprimed-even stopped law with the full chronological
complement. -/
theorem unprimedEven_active_fullComplement_direction_hasLaw_reduced {q : ℕ}
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
      (unprimedEvenActiveFullComplementStatistic
        m k C labels activeBases)
      (((sourceCappedProfileMeasure m
          (activeFreeStoppedShape (0, 0) labels C activeBases)
          (activeFreeCapProfile (0, 0) labels C activeBases
            (stoppedExternalLeft (0, 0) labels)
            (stoppedExternalRight (0, 0) labels))).prod directionLaw).prod
        (stoppedMixedComplementRunMeasure (0, 0) labels m C activeBases
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
    apply hasLaw_prod_direction_after tau A X _
      (measurable_stoppedCreationTime m k)
    · intro n
      simpa only [A, tau] using
        unprimedEven_sourcePast m k C labels hnondist hm hk hfree n
    · exact hX
    · intro v n
      simpa only [A, X, tau, Set.inter_assoc] using
        unprimedEven_vectorFiberPast m k C labels
          hnondist hm hk hfree v n
    · exact hsource
  have hpos := unprimedEven_mixedCoordinatePos_of_nonempty
    m k C labels hm hcard hfree hoff hterminal hne
  have hgrouped :=
    actualAdmissible_unprimedEvenSourceConstraint_eq_mixedBlockPreimage
      m k C labels hm hcard hfree hoff hterminal
  have h := activeFree_fullComplement_capped_hasLaw_of_joint
    (0, 0) labels m C activeBases
      (stoppedExternalLeft (0, 0) labels)
      (stoppedExternalRight (0, 0) labels)
      (actualAdmissibleStoppedVectors m k labels E)
      incrementLaw[|A] X
      (fun omega ↦ incrementShiftAfter tau omega 0)
      hjoint (by simpa only [E] using hgrouped) hpos
  change HasLaw
    (fun omega ↦
      (((fun b : ActiveFreeStoppedBase (0, 0) labels C activeBases ↦
          ∑ i, stoppedPaperBlockVector (0, 0) labels
            (actualStoppedVector m k labels
              (unprimedEvenSourceConstraint m k C labels) omega) b.1 i),
        incrementShiftAfter (stoppedCreationTime m k) omega 0),
      restrictComplementStoppedRuns (0, 0) labels C activeBases
        (stoppedPaperBlockVector (0, 0) labels
          (actualStoppedVector m k labels
            (unprimedEvenSourceConstraint m k C labels) omega))))
    (((sourceCappedProfileMeasure m
        (activeFreeStoppedShape (0, 0) labels C activeBases)
        (activeFreeCapProfile (0, 0) labels C activeBases
          (stoppedExternalLeft (0, 0) labels)
          (stoppedExternalRight (0, 0) labels))).prod directionLaw).prod
      (stoppedMixedComplementRunMeasure (0, 0) labels m C activeBases
        (stoppedExternalLeft (0, 0) labels)
        (stoppedExternalRight (0, 0) labels)))
    incrementLaw[|A]
  simpa only [A, E, X, tau] using h

/-- The active first component becomes the canonical truncated profile on
the tie-left winner filter, while the full chronological complement remains
unchanged. -/
theorem unprimedEven_leftWinner_active_fullComplement_direction_hasLaw
    {q : ℕ}
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
      (unprimedEvenActiveFullComplementStatistic
        m k C labels activeBases)
      (((sourceTruncatedProfileMeasure m
          (activeFreeStoppedShape (0, 0) labels C activeBases)).prod
            directionLaw).prod
        (stoppedMixedComplementRunMeasure (0, 0) labels m C activeBases
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
  have h := unprimedEven_active_fullComplement_direction_hasLaw_reduced
    m k C labels hnondist hm hk hcard hfree hoff hterminal hne activeBases
  rw [sourceCappedProfileMeasure_eq_truncated m
    (activeFreeStoppedShape (0, 0) labels C activeBases)
    (activeFreeCapProfile (0, 0) labels C activeBases
      (stoppedExternalLeft (0, 0) labels)
      (stoppedExternalRight (0, 0) labels)) hwinning] at h
  exact h

/-- Full chronological complement on walk-path space. -/
noncomputable def unprimedEvenFullComplementPath {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    (ℕ → Site) → ComplementStoppedRuns (0, 0) labels C activeBases :=
  fun s ↦ (liftIncrementStatisticToPath
    (unprimedEvenActiveFullComplementStatistic
      m k C labels activeBases) s).2

theorem measurable_unprimedEvenFullComplementPath {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    Measurable
      (unprimedEvenFullComplementPath m k C labels activeBases) :=
  measurable_snd.comp (measurable_liftIncrementStatisticToPath
    (measurable_unprimedEvenActiveFullComplementStatistic
      m k C labels hnondist activeBases))

/-- Unnormalized path-space version of the full chronological complement
factorization. -/
theorem unprimedEven_leftWinner_active_fullComplement_path_map_law {q : ℕ}
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
            unprimedEvenFullComplementPath m k C labels activeBases s)) =
      simpleRandomWalkLaw
          (simpleRandomWalk ''
            (actualStoppedVectorEvent m k labels (stoppedRunVectorBox q m) ∩
              stoppedSourceCondition m k C)) •
        (((sourceTruncatedProfileMeasure m
          (activeFreeStoppedShape (0, 0) labels C activeBases)).prod
            directionLaw).prod
          (stoppedMixedComplementRunMeasure (0, 0) labels m C activeBases
            (stoppedExternalLeft (0, 0) labels)
            (stoppedExternalRight (0, 0) labels))) := by
  dsimp only
  let activeBases := unprimedEvenLeftWinnerBases labels candidateBases
  let A := actualStoppedVectorEvent m k labels (stoppedRunVectorBox q m) ∩
    stoppedSourceCondition m k C
  let J := unprimedEvenActiveFullComplementStatistic
    m k C labels activeBases
  have hA : MeasurableSet A := by
    dsimp only [A]
    rw [unprimedEven_source_partition m k C labels hm hk hfree]
    exact measurableSet_actualStoppedVectorEvent _ _ _ _
  have hJ : Measurable J :=
    measurable_unprimedEvenActiveFullComplementStatistic
      m k C labels hnondist activeBases
  have hLaw := liftIncrementStatistic_path_map_law hA hJ
    (unprimedEven_leftWinner_active_fullComplement_direction_hasLaw
      m k C labels hnondist hm hk hcard hfree hoff hterminal hne
        candidateBases)
  have hPath : MeasurableSet (simpleRandomWalk '' A) :=
    HLOZSourceInstantiation.measurableEmbedding_simpleRandomWalk.measurableSet_image.2 hA
  calc
    (simpleRandomWalkLaw.restrict (simpleRandomWalk '' A)).map
        (fun s ↦
          ((unprimedEvenActiveFreePathLazy m k C labels activeBases s,
              unprimedEvenActiveFreePathNext m k C labels activeBases s),
            unprimedEvenFullComplementPath m k C labels activeBases s)) =
      (simpleRandomWalkLaw.restrict (simpleRandomWalk '' A)).map
        (liftIncrementStatisticToPath J) := by
          apply Measure.map_congr
          filter_upwards [ae_restrict_mem hPath] with s hs
          rcases hs with ⟨omega, homega, rfl⟩
          simp only [unprimedEvenActiveFreePathLazy,
            unprimedEvenActiveFreePathNext,
            unprimedEvenFullComplementPath,
            liftIncrementStatisticToPath_simpleRandomWalk, J,
            unprimedEvenActiveFullComplementStatistic,
            unprimedEvenActiveFreeStatistic,
            unprimedEvenFullComplementStatistic]
          rfl
    _ = _ := by simpa only [A, activeBases, J] using hLaw

/-- The Proposition-4.9 tower with the information-preserving chronological
complement.  Relative to the earlier block-sum version, the sole residual
fiberwise premise is strictly weaker: equality now fixes every nonactive run
coordinate, not merely its total on each repeated base. -/
theorem unprimedEvenLeftWinnerProp49_fullComplement_orderedHistory_screenEstimate_of_fiberwise
    {m A : ℕ} {alpha : ℝ} {screen : Set (ℕ → Site)}
    {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    (D : UnprimedEvenLeftWinnerProp49AtomData
      m (stageNumber r) A alpha screen)
    (c : Fin (stageNumber r) → Site)
    (hdet : EventDeterminedByOn D.atom
      (orderedCanonicalHistoryEvent m i a r c)
      (unprimedEvenFullComplementPath m (stageNumber r) D.C D.labels
        (unprimedEvenLeftWinnerBases D.labels D.candidateBases))) :
    RefinedAtomScreenEstimate
      (unprimedEvenOrderedHistoryPathAtom
        m i a r D.C D.labels c) screen
      (sourceProp49ScreenRate m A alpha) := by
  let activeBases :=
    unprimedEvenLeftWinnerBases D.labels D.candidateBases
  let z := unprimedEvenFullComplementPath
    m (stageNumber r) D.C D.labels activeBases
  let history := orderedCanonicalHistoryEvent m i a r c
  let H : Set (ComplementStoppedRuns (0, 0) D.labels D.C activeBases) :=
    {v | ∃ s ∈ D.atom, s ∈ history ∧ z s = v}
  have hH : MeasurableSet H := MeasurableSet.of_discrete
  have heq : D.atom ∩ history = D.atom ∩ z ⁻¹' H := by
    exact inter_eq_inter_preimage_of_eventDeterminedByOn
      D.atom history z hdet
  let complementLaw := stoppedMixedComplementRunMeasure
    (0, 0) D.labels m D.C activeBases
      (stoppedExternalLeft (0, 0) D.labels)
      (stoppedExternalRight (0, 0) D.labels)
  have hpos := unprimedEven_mixedCoordinatePos_of_nonempty
    m (stageNumber r) D.C D.labels D.m_pos D.creation_card
      D.creation_pairFree D.offBase D.terminal_mem D.admissible_nonempty
  letI : IsProbabilityMeasure complementLaw := by
    dsimp only [complementLaw]
    exact stoppedMixedComplementRunMeasure_isProbabilityMeasure
      (0, 0) D.labels m D.C activeBases
        (stoppedExternalLeft (0, 0) D.labels)
        (stoppedExternalRight (0, 0) D.labels) hpos
  let F : StoppedTruncatedProp49HistoryFactorization D.toInput history :=
    { Z := ComplementStoppedRuns (0, 0) D.labels D.C activeBases
      measurableSpaceZ := inferInstance
      complementLaw := complementLaw
      sFiniteComplementLaw := inferInstance
      complement := z
      measurable_complement :=
        measurable_unprimedEvenFullComplementPath
          m (stageNumber r) D.C D.labels D.nondistinguished activeBases
      historySet := H
      measurable_historySet := hH
      history_eq := heq
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
                  unprimedEvenFullComplementPath m (stageNumber r) D.C
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
          unprimedEven_leftWinner_active_fullComplement_path_map_law
            m (stageNumber r) D.C D.labels D.nondistinguished D.m_pos
              D.k_pos D.creation_card D.creation_pairFree D.offBase
              D.terminal_mem D.admissible_nonempty D.candidateBases }
  rw [unprimedEvenOrderedHistoryPathAtom_eq_coarse_inter_history]
  exact F.history_screen_le D.toInput

/-- Profile-generic form of the same tower.  In particular this applies to
`sourceCanonicalProfiles`, so the checked stopped law does not force the
auxiliary pairing-adapted profile family into the final Proposition-4.9
interface. -/
theorem unprimedEvenLeftWinnerProp49_fullComplement_orderedProfileHistory_screenEstimate_of_fiberwise
    {m A : ℕ} {alpha : ℝ} {screen : Set (ℕ → Site)}
    {profiles : Fin 6 → HLOZProp47SourceObjects.ExternalProfilePair}
    {cStar : Fin 6 → ℝ}
    {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    (D : UnprimedEvenLeftWinnerProp49AtomData
      m (stageNumber r) A alpha screen)
    (c : Fin (stageNumber r) → Site)
    (hdet : EventDeterminedByOn D.atom
      (orderedProfileHistoryEvent profiles cStar m i a r c)
      (unprimedEvenFullComplementPath m (stageNumber r) D.C D.labels
        (unprimedEvenLeftWinnerBases D.labels D.candidateBases))) :
    RefinedAtomScreenEstimate
      (orderedProfileHistoryPathAtom profiles cStar m i a r c D.atom) screen
      (sourceProp49ScreenRate m A alpha) := by
  let activeBases :=
    unprimedEvenLeftWinnerBases D.labels D.candidateBases
  let z := unprimedEvenFullComplementPath
    m (stageNumber r) D.C D.labels activeBases
  let complementLaw := stoppedMixedComplementRunMeasure
    (0, 0) D.labels m D.C activeBases
      (stoppedExternalLeft (0, 0) D.labels)
      (stoppedExternalRight (0, 0) D.labels)
  have hpos := unprimedEven_mixedCoordinatePos_of_nonempty
    m (stageNumber r) D.C D.labels D.m_pos D.creation_card
      D.creation_pairFree D.offBase D.terminal_mem D.admissible_nonempty
  letI : IsProbabilityMeasure complementLaw := by
    dsimp only [complementLaw]
    exact stoppedMixedComplementRunMeasure_isProbabilityMeasure
      (0, 0) D.labels m D.C activeBases
        (stoppedExternalLeft (0, 0) D.labels)
        (stoppedExternalRight (0, 0) D.labels) hpos
  change RefinedAtomScreenEstimate
    (D.atom ∩ orderedProfileHistoryEvent profiles cStar m i a r c) screen
      (sourceProp49ScreenRate m A alpha)
  apply refinedAtomScreenEstimate_of_joint_complement_determined
    D.toInput complementLaw z
  · exact measurable_unprimedEvenFullComplementPath
      m (stageNumber r) D.C D.labels D.nondistinguished activeBases
  · exact MeasurableSet.of_discrete
  · exact hdet
  · simpa only [UnprimedEvenLeftWinnerProp49AtomData.toInput,
      unprimedEvenLeftWinnerProp49AtomInput,
      UnprimedEvenLeftWinnerProp49AtomData.atom, activeBases, complementLaw,
      z] using
      unprimedEven_leftWinner_active_fullComplement_path_map_law
        m (stageNumber r) D.C D.labels D.nondistinguished D.m_pos
          D.k_pos D.creation_card D.creation_pairFree D.offBase
          D.terminal_mem D.admissible_nonempty D.candidateBases

/-! ### Primed-odd path specialization -/

noncomputable def primedOddFullComplementStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    (ℕ → Direction) → ComplementStoppedRuns
      (primedInitialBase first) labels C activeBases :=
  fun omega ↦
    restrictComplementStoppedRuns (primedInitialBase first) labels C
      activeBases
      (stoppedPaperBlockVector (primedInitialBase first) labels
        (actualPrimedStoppedVector m k first labels
          (primedOddSourceConstraint m k C first labels) omega))

theorem measurable_primedOddFullComplementStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    Measurable
      (primedOddFullComplementStatistic
        m k C first labels activeBases) := by
  exact (measurable_restrictComplementStoppedRuns
    (primedInitialBase first) labels C activeBases).comp
      ((measurable_stoppedPaperBlockVector
        (primedInitialBase first) labels).comp
        (measurable_actualPrimedStoppedVector m k first labels hnondist
          (primedOddSourceConstraint m k C first labels)))

noncomputable def primedOddActiveFullComplementStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    (ℕ → Direction) →
      ((ActiveFreeStoppedBase (primedInitialBase first) labels C
          activeBases → ℕ) × Direction) ×
        ComplementStoppedRuns (primedInitialBase first) labels C activeBases :=
  fun omega ↦
    (((fun b ↦ ∑ i,
        stoppedPaperBlockVector (primedInitialBase first) labels
          (actualPrimedStoppedVector m k first labels
            (primedOddSourceConstraint m k C first labels) omega) b.1 i),
      incrementShiftAfter (stoppedCreationTime m k) omega 0),
    primedOddFullComplementStatistic m k C first labels activeBases omega)

theorem measurable_primedOddActiveFullComplementStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    Measurable
      (primedOddActiveFullComplementStatistic
        m k C first labels activeBases) := by
  exact (measurable_primedOddActiveFreeStatistic
    m k C first labels hnondist activeBases).prodMk
      (measurable_primedOddFullComplementStatistic
        m k C first labels hnondist activeBases)

/-- Literal primed-odd strict-right stopped law retaining every chronological
run coordinate on the complementary bases. -/
theorem primedOdd_strictRightWinner_active_fullComplement_direction_hasLaw
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
      (primedOddActiveFullComplementStatistic
        m k C first labels activeBases)
      (((sourceTruncatedProfileMeasure m
          (activeFreeStoppedShape (primedInitialBase first) labels C
            activeBases)).prod directionLaw).prod
        (stoppedMixedComplementRunMeasure (primedInitialBase first) labels m C
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
  have h := activeFree_fullComplement_capped_hasLaw_of_joint
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
    (primedOddActiveFullComplementStatistic
      m k C first labels activeBases)
    (((sourceTruncatedProfileMeasure m
        (activeFreeStoppedShape (primedInitialBase first) labels C
          activeBases)).prod directionLaw).prod
      (stoppedMixedComplementRunMeasure (primedInitialBase first) labels m C
        activeBases (primedStoppedExternalLeft first labels)
          (primedStoppedExternalRight first labels)))
    incrementLaw[|A] at h
  simpa only [A, activeBases] using h

noncomputable def primedOddFullComplementPath {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    (ℕ → Site) → ComplementStoppedRuns
      (primedInitialBase first) labels C activeBases :=
  fun s ↦ (liftIncrementStatisticToPath
    (primedOddActiveFullComplementStatistic
      m k C first labels activeBases) s).2

theorem measurable_primedOddFullComplementPath {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    Measurable
      (primedOddFullComplementPath m k C first labels activeBases) :=
  measurable_snd.comp (measurable_liftIncrementStatisticToPath
    (measurable_primedOddActiveFullComplementStatistic
      m k C first labels hnondist activeBases))

theorem primedOdd_strictRightWinner_active_fullComplement_path_map_law
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
            primedOddFullComplementPath m k C first labels activeBases s)) =
      simpleRandomWalkLaw
          (simpleRandomWalk ''
            (actualPrimedStoppedVectorEvent m k first labels
                (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C)) •
        (((sourceTruncatedProfileMeasure m
          (activeFreeStoppedShape (primedInitialBase first) labels C
            activeBases)).prod directionLaw).prod
          (stoppedMixedComplementRunMeasure (primedInitialBase first) labels m C
            activeBases (primedStoppedExternalLeft first labels)
              (primedStoppedExternalRight first labels))) := by
  dsimp only
  let activeBases :=
    primedOddStrictRightWinnerBases first labels candidateBases
  let A := actualPrimedStoppedVectorEvent m k first labels
      (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C
  let J := primedOddActiveFullComplementStatistic
    m k C first labels activeBases
  have hA : MeasurableSet A := by
    dsimp only [A]
    rw [primedOdd_source_partition m k C first labels hm hk hfree]
    unfold actualPrimedStoppedVectorEvent
    exact MeasurableSet.iUnion fun v ↦ MeasurableSet.iUnion fun _ ↦
      measurableSet_stoppedPrefixAtom
        (reconstructedPrimedStoppedPrefix first labels v)
  have hJ : Measurable J :=
    measurable_primedOddActiveFullComplementStatistic
      m k C first labels hnondist activeBases
  have hLaw := liftIncrementStatistic_path_map_law hA hJ
    (primedOdd_strictRightWinner_active_fullComplement_direction_hasLaw
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
            primedOddFullComplementPath m k C first labels activeBases s)) =
      (simpleRandomWalkLaw.restrict (simpleRandomWalk '' A)).map
        (liftIncrementStatisticToPath J) := by
          apply Measure.map_congr
          filter_upwards [ae_restrict_mem hPath] with s hs
          rcases hs with ⟨omega, homega, rfl⟩
          simp only [primedOddActiveFreePathLazy,
            primedOddActiveFreePathNext, primedOddFullComplementPath,
            liftIncrementStatisticToPath_simpleRandomWalk, J,
            primedOddActiveFullComplementStatistic,
            primedOddActiveFreeStatistic,
            primedOddFullComplementStatistic]
          rfl
    _ = _ := by simpa only [A, activeBases, J] using hLaw

theorem primedOddStrictRightWinnerProp49_fullComplement_orderedHistory_screenEstimate_of_fiberwise
    {m A : ℕ} {alpha : ℝ} {screen : Set (ℕ → Site)}
    {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    (D : PrimedOddStrictRightWinnerProp49AtomData
      m (stageNumber r) A alpha screen)
    (c : Fin (stageNumber r) → Site)
    (hdet : EventDeterminedByOn D.atom
      (orderedCanonicalHistoryEvent m i a r c)
      (primedOddFullComplementPath m (stageNumber r) D.C D.first D.labels
        (primedOddStrictRightWinnerBases D.first D.labels
          D.candidateBases))) :
    RefinedAtomScreenEstimate
      (primedOddOrderedHistoryPathAtom
        m i a r D.C D.first D.labels c) screen
      (sourceProp49ScreenRate m A alpha) := by
  let activeBases :=
    primedOddStrictRightWinnerBases D.first D.labels D.candidateBases
  let z := primedOddFullComplementPath
    m (stageNumber r) D.C D.first D.labels activeBases
  let history := orderedCanonicalHistoryEvent m i a r c
  let H : Set (ComplementStoppedRuns
      (primedInitialBase D.first) D.labels D.C activeBases) :=
    {v | ∃ s ∈ D.atom, s ∈ history ∧ z s = v}
  have hH : MeasurableSet H := MeasurableSet.of_discrete
  have heq : D.atom ∩ history = D.atom ∩ z ⁻¹' H := by
    exact inter_eq_inter_preimage_of_eventDeterminedByOn
      D.atom history z hdet
  let complementLaw := stoppedMixedComplementRunMeasure
    (primedInitialBase D.first) D.labels m D.C activeBases
      (primedStoppedExternalLeft D.first D.labels)
      (primedStoppedExternalRight D.first D.labels)
  have hpos := primedOdd_mixedCoordinatePos_of_nonempty
    m (stageNumber r) D.C D.first D.labels D.m_pos D.creation_card
      D.creation_pairFree D.offBase D.terminal_mem D.admissible_nonempty
  letI : IsProbabilityMeasure complementLaw := by
    dsimp only [complementLaw]
    exact stoppedMixedComplementRunMeasure_isProbabilityMeasure
      (primedInitialBase D.first) D.labels m D.C activeBases
        (primedStoppedExternalLeft D.first D.labels)
        (primedStoppedExternalRight D.first D.labels) hpos
  let F : StoppedTruncatedProp49HistoryFactorization D.toInput history :=
    { Z := ComplementStoppedRuns
        (primedInitialBase D.first) D.labels D.C activeBases
      measurableSpaceZ := inferInstance
      complementLaw := complementLaw
      sFiniteComplementLaw := inferInstance
      complement := z
      measurable_complement :=
        measurable_primedOddFullComplementPath
          m (stageNumber r) D.C D.first D.labels D.nondistinguished
            activeBases
      historySet := H
      measurable_historySet := hH
      history_eq := heq
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
                  primedOddFullComplementPath m (stageNumber r) D.C
                    D.first D.labels activeBases s)) =
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
          primedOdd_strictRightWinner_active_fullComplement_path_map_law
            m (stageNumber r) D.C D.first D.labels D.nondistinguished
              D.m_pos D.k_pos D.creation_card D.creation_pairFree D.offBase
              D.terminal_mem D.admissible_nonempty D.candidateBases }
  rw [primedOddOrderedHistoryPathAtom_eq_coarse_inter_history]
  exact F.history_screen_le D.toInput

theorem primedOddStrictRightWinnerProp49_fullComplement_orderedProfileHistory_screenEstimate_of_fiberwise
    {m A : ℕ} {alpha : ℝ} {screen : Set (ℕ → Site)}
    {profiles : Fin 6 → HLOZProp47SourceObjects.ExternalProfilePair}
    {cStar : Fin 6 → ℝ} {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    (D : PrimedOddStrictRightWinnerProp49AtomData
      m (stageNumber r) A alpha screen)
    (c : Fin (stageNumber r) → Site)
    (hdet : EventDeterminedByOn D.atom
      (orderedProfileHistoryEvent profiles cStar m i a r c)
      (primedOddFullComplementPath m (stageNumber r) D.C D.first D.labels
        (primedOddStrictRightWinnerBases D.first D.labels
          D.candidateBases))) :
    RefinedAtomScreenEstimate
      (orderedProfileHistoryPathAtom profiles cStar m i a r c D.atom) screen
      (sourceProp49ScreenRate m A alpha) := by
  let activeBases :=
    primedOddStrictRightWinnerBases D.first D.labels D.candidateBases
  let z := primedOddFullComplementPath
    m (stageNumber r) D.C D.first D.labels activeBases
  let complementLaw := stoppedMixedComplementRunMeasure
    (primedInitialBase D.first) D.labels m D.C activeBases
      (primedStoppedExternalLeft D.first D.labels)
      (primedStoppedExternalRight D.first D.labels)
  have hpos := primedOdd_mixedCoordinatePos_of_nonempty
    m (stageNumber r) D.C D.first D.labels D.m_pos D.creation_card
      D.creation_pairFree D.offBase D.terminal_mem D.admissible_nonempty
  letI : IsProbabilityMeasure complementLaw := by
    dsimp only [complementLaw]
    exact stoppedMixedComplementRunMeasure_isProbabilityMeasure
      (primedInitialBase D.first) D.labels m D.C activeBases
        (primedStoppedExternalLeft D.first D.labels)
        (primedStoppedExternalRight D.first D.labels) hpos
  change RefinedAtomScreenEstimate
    (D.atom ∩ orderedProfileHistoryEvent profiles cStar m i a r c) screen
      (sourceProp49ScreenRate m A alpha)
  apply refinedAtomScreenEstimate_of_joint_complement_determined
    D.toInput complementLaw z
  · exact measurable_primedOddFullComplementPath
      m (stageNumber r) D.C D.first D.labels D.nondistinguished activeBases
  · exact MeasurableSet.of_discrete
  · exact hdet
  · simpa only [PrimedOddStrictRightWinnerProp49AtomData.toInput,
      primedOddStrictRightWinnerProp49AtomInput,
      PrimedOddStrictRightWinnerProp49AtomData.atom, activeBases,
      complementLaw, z] using
      primedOdd_strictRightWinner_active_fullComplement_path_map_law
        m (stageNumber r) D.C D.first D.labels D.nondistinguished
          D.m_pos D.k_pos D.creation_card D.creation_pairFree D.offBase
          D.terminal_mem D.admissible_nonempty D.candidateBases

/-! ### Unprimed-odd terminal path specialization -/

noncomputable def unprimedOddTerminalFullComplementStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    (ℕ → Direction) → ComplementStoppedRuns (0, 0) labels C activeBases :=
  fun omega ↦
    restrictComplementStoppedRuns (0, 0) labels C activeBases
      (stoppedPaperBlockVector (0, 0) labels
        (actualOddStoppedVector m k labels terminal
          (unprimedOddSourceConstraint m k C labels terminal) omega))

theorem measurable_unprimedOddTerminalFullComplementStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (terminal : IncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    Measurable (unprimedOddTerminalFullComplementStatistic
      m k C labels terminal activeBases) := by
  exact (measurable_restrictComplementStoppedRuns
    (0, 0) labels C activeBases).comp
      ((measurable_stoppedPaperBlockVector (0, 0) labels).comp
        (measurable_actualOddStoppedVector m k labels hnondist terminal
          (unprimedOddSourceConstraint m k C labels terminal)))

noncomputable def unprimedOddTerminalActiveFullComplementStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    (ℕ → Direction) →
      ((ActiveFreeStoppedBase (0, 0) labels C activeBases → ℕ) ×
        Direction) × ComplementStoppedRuns (0, 0) labels C activeBases :=
  fun omega ↦
    (((fun b ↦ ∑ i,
        stoppedPaperBlockVector (0, 0) labels
          (actualOddStoppedVector m k labels terminal
            (unprimedOddSourceConstraint m k C labels terminal) omega)
          b.1 i),
      incrementShiftAfter (stoppedCompletionTime m k) omega 0),
    unprimedOddTerminalFullComplementStatistic
      m k C labels terminal activeBases omega)

theorem measurable_unprimedOddTerminalActiveFullComplementStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (terminal : IncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    Measurable (unprimedOddTerminalActiveFullComplementStatistic
      m k C labels terminal activeBases) := by
  exact (measurable_unprimedOddActiveFreeStatistic
    m k C labels hnondist terminal activeBases).prodMk
      (measurable_unprimedOddTerminalFullComplementStatistic
        m k C labels hnondist terminal activeBases)

theorem unprimedOdd_tieLeftWinner_active_fullComplement_direction_hasLaw
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
      (unprimedOddTerminalActiveFullComplementStatistic
        m k C labels terminal activeBases)
      (((sourceTruncatedProfileMeasure m
          (activeFreeStoppedShape (0, 0) labels C activeBases)).prod
            directionLaw).prod
        (stoppedMixedComplementRunMeasure (0, 0) labels m C activeBases
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
  have h := activeFree_fullComplement_capped_hasLaw_of_joint
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
    (unprimedOddTerminalActiveFullComplementStatistic
      m k C labels terminal activeBases)
    (((sourceTruncatedProfileMeasure m
        (activeFreeStoppedShape (0, 0) labels C activeBases)).prod
          directionLaw).prod
      (stoppedMixedComplementRunMeasure (0, 0) labels m C activeBases
        (stoppedExternalLeft (0, 0) labels)
        (unprimedOddTerminalExternalRight labels terminal)))
    incrementLaw[|A] at h
  simpa only [A, activeBases] using h

noncomputable def unprimedOddTerminalFullComplementPath {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    (ℕ → Site) → ComplementStoppedRuns (0, 0) labels C activeBases :=
  fun s ↦ (liftIncrementStatisticToPath
    (unprimedOddTerminalActiveFullComplementStatistic
      m k C labels terminal activeBases) s).2

theorem measurable_unprimedOddTerminalFullComplementPath {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (terminal : IncrementPair)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels)) :
    Measurable (unprimedOddTerminalFullComplementPath
      m k C labels terminal activeBases) :=
  measurable_snd.comp (measurable_liftIncrementStatisticToPath
    (measurable_unprimedOddTerminalActiveFullComplementStatistic
      m k C labels hnondist terminal activeBases))

theorem unprimedOdd_tieLeftWinner_active_fullComplement_path_map_law
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
            unprimedOddTerminalFullComplementPath m k C labels terminal
              activeBases s)) =
      simpleRandomWalkLaw
          (simpleRandomWalk ''
            (actualOddStoppedVectorEvent m k labels terminal
                (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C)) •
        (((sourceTruncatedProfileMeasure m
          (activeFreeStoppedShape (0, 0) labels C activeBases)).prod
            directionLaw).prod
          (stoppedMixedComplementRunMeasure (0, 0) labels m C activeBases
            (stoppedExternalLeft (0, 0) labels)
            (unprimedOddTerminalExternalRight labels terminal))) := by
  dsimp only
  let activeBases := unprimedOddTieLeftWinnerBases labels
    (unprimedOddTerminalExternalRight labels terminal) candidateBases
  let A := actualOddStoppedVectorEvent m k labels terminal
    (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C
  let J := unprimedOddTerminalActiveFullComplementStatistic
    m k C labels terminal activeBases
  have hA : MeasurableSet A := by
    dsimp only [A]
    rw [unprimedOdd_source_partition m k C labels terminal hm hk hfree]
    unfold actualOddStoppedVectorEvent
    exact MeasurableSet.iUnion fun v ↦ MeasurableSet.iUnion fun _ ↦
      measurableSet_stoppedPrefixAtom
        (reconstructedOddStoppedPrefix labels v terminal)
  have hJ : Measurable J :=
    measurable_unprimedOddTerminalActiveFullComplementStatistic
      m k C labels hnondist terminal activeBases
  have hLaw := liftIncrementStatistic_path_map_law hA hJ
    (unprimedOdd_tieLeftWinner_active_fullComplement_direction_hasLaw
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
            unprimedOddTerminalFullComplementPath m k C labels terminal
              activeBases s)) =
      (simpleRandomWalkLaw.restrict (simpleRandomWalk '' A)).map
        (liftIncrementStatisticToPath J) := by
          apply Measure.map_congr
          filter_upwards [ae_restrict_mem hPath] with s hs
          rcases hs with ⟨omega, homega, rfl⟩
          simp only [unprimedOddActiveFreePathLazy,
            unprimedOddActiveFreePathNext,
            unprimedOddTerminalFullComplementPath,
            liftIncrementStatisticToPath_simpleRandomWalk, J,
            unprimedOddTerminalActiveFullComplementStatistic,
            unprimedOddActiveFreeStatistic,
            unprimedOddTerminalFullComplementStatistic]
          rfl
    _ = _ := by simpa only [A, activeBases, J] using hLaw

theorem unprimedOddTerminalTieLeftProp49_fullComplement_orderedHistory_screenEstimate_of_fiberwise
    {m A : ℕ} {alpha : ℝ} {screen : Set (ℕ → Site)}
    {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    (D : UnprimedOddTerminalTieLeftProp49AtomData
      m (stageNumber r) A alpha screen)
    (c : Fin (stageNumber r) → Site)
    (hdet : EventDeterminedByOn D.atom
      (orderedCanonicalHistoryEvent m i a r c)
      (unprimedOddTerminalFullComplementPath m (stageNumber r) D.C D.labels
        D.terminal
        (unprimedOddTieLeftWinnerBases D.labels
          (unprimedOddTerminalExternalRight D.labels D.terminal)
            D.candidateBases))) :
    RefinedAtomScreenEstimate
      (unprimedOddTerminalOrderedHistoryPathAtom
        m i a r D.C D.labels D.terminal c) screen
      (sourceProp49ScreenRate m A alpha) := by
  let externalRight :=
    unprimedOddTerminalExternalRight D.labels D.terminal
  let activeBases := unprimedOddTieLeftWinnerBases D.labels
    externalRight D.candidateBases
  let z := unprimedOddTerminalFullComplementPath
    m (stageNumber r) D.C D.labels D.terminal activeBases
  let history := orderedCanonicalHistoryEvent m i a r c
  let H : Set (ComplementStoppedRuns
      (0, 0) D.labels D.C activeBases) :=
    {v | ∃ s ∈ D.atom, s ∈ history ∧ z s = v}
  have hH : MeasurableSet H := MeasurableSet.of_discrete
  have heq : D.atom ∩ history = D.atom ∩ z ⁻¹' H := by
    exact inter_eq_inter_preimage_of_eventDeterminedByOn
      D.atom history z hdet
  let complementLaw := stoppedMixedComplementRunMeasure
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
    exact stoppedMixedComplementRunMeasure_isProbabilityMeasure
      (0, 0) D.labels m D.C activeBases
        (stoppedExternalLeft (0, 0) D.labels) externalRight hpos
  let F : StoppedTruncatedProp49HistoryFactorization D.toInput history :=
    { Z := ComplementStoppedRuns (0, 0) D.labels D.C activeBases
      measurableSpaceZ := inferInstance
      complementLaw := complementLaw
      sFiniteComplementLaw := inferInstance
      complement := z
      measurable_complement :=
        measurable_unprimedOddTerminalFullComplementPath
          m (stageNumber r) D.C D.labels D.nondistinguished D.terminal
            activeBases
      historySet := H
      measurable_historySet := hH
      history_eq := heq
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
                  unprimedOddTerminalFullComplementPath m (stageNumber r)
                    D.C D.labels D.terminal activeBases s)) =
            simpleRandomWalkLaw
                (simpleRandomWalk ''
                  (actualOddStoppedVectorEvent m (stageNumber r) D.labels
                      D.terminal (stoppedRunVectorBox D.q m) ∩
                    stoppedSourceCondition m (stageNumber r) D.C)) •
              (((sourceTruncatedProfileMeasure m
                (activeFreeStoppedShape (0, 0) D.labels D.C
                  activeBases)).prod directionLaw).prod complementLaw)
        simpa only [activeBases, externalRight, complementLaw] using
          unprimedOdd_tieLeftWinner_active_fullComplement_path_map_law
            m (stageNumber r) D.C D.labels D.nondistinguished D.terminal
              D.m_pos D.k_pos D.creation_card D.creation_pairFree D.offBase
              D.terminal_mem D.admissible_nonempty D.candidateBases }
  rw [unprimedOddTerminalOrderedHistoryPathAtom_eq_coarse_inter_history]
  exact F.history_screen_le D.toInput

theorem unprimedOddTerminalTieLeftProp49_fullComplement_orderedProfileHistory_screenEstimate_of_fiberwise
    {m A : ℕ} {alpha : ℝ} {screen : Set (ℕ → Site)}
    {profiles : Fin 6 → HLOZProp47SourceObjects.ExternalProfilePair}
    {cStar : Fin 6 → ℝ} {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    (D : UnprimedOddTerminalTieLeftProp49AtomData
      m (stageNumber r) A alpha screen)
    (c : Fin (stageNumber r) → Site)
    (hdet : EventDeterminedByOn D.atom
      (orderedProfileHistoryEvent profiles cStar m i a r c)
      (unprimedOddTerminalFullComplementPath m (stageNumber r) D.C D.labels
        D.terminal
        (unprimedOddTieLeftWinnerBases D.labels
          (unprimedOddTerminalExternalRight D.labels D.terminal)
            D.candidateBases))) :
    RefinedAtomScreenEstimate
      (orderedProfileHistoryPathAtom profiles cStar m i a r c D.atom) screen
      (sourceProp49ScreenRate m A alpha) := by
  let externalRight :=
    unprimedOddTerminalExternalRight D.labels D.terminal
  let activeBases := unprimedOddTieLeftWinnerBases D.labels
    externalRight D.candidateBases
  let z := unprimedOddTerminalFullComplementPath
    m (stageNumber r) D.C D.labels D.terminal activeBases
  let complementLaw := stoppedMixedComplementRunMeasure
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
    exact stoppedMixedComplementRunMeasure_isProbabilityMeasure
      (0, 0) D.labels m D.C activeBases
        (stoppedExternalLeft (0, 0) D.labels) externalRight hpos
  change RefinedAtomScreenEstimate
    (D.atom ∩ orderedProfileHistoryEvent profiles cStar m i a r c) screen
      (sourceProp49ScreenRate m A alpha)
  apply refinedAtomScreenEstimate_of_joint_complement_determined
    D.toInput complementLaw z
  · exact measurable_unprimedOddTerminalFullComplementPath
      m (stageNumber r) D.C D.labels D.nondistinguished D.terminal
        activeBases
  · exact MeasurableSet.of_discrete
  · exact hdet
  · simpa only [UnprimedOddTerminalTieLeftProp49AtomData.toInput,
      unprimedOddTerminalTieLeftProp49AtomInput,
      UnprimedOddTerminalTieLeftProp49AtomData.atom, activeBases,
      externalRight, complementLaw, z] using
      unprimedOdd_tieLeftWinner_active_fullComplement_path_map_law
        m (stageNumber r) D.C D.labels D.nondistinguished D.terminal
          D.m_pos D.k_pos D.creation_card D.creation_pairFree D.offBase
          D.terminal_mem D.admissible_nonempty D.candidateBases

/-! ### Primed-even terminal path specialization -/

noncomputable def primedEvenTerminalFullComplementStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair) (terminal : IncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    (ℕ → Direction) → ComplementStoppedRuns
      (primedInitialBase first) labels C activeBases :=
  fun omega ↦
    restrictComplementStoppedRuns (primedInitialBase first) labels C
      activeBases
      (stoppedPaperBlockVector (primedInitialBase first) labels
        (actualPrimedTerminalVector m k first labels terminal
          (primedEvenSourceConstraint m k C first labels terminal) omega))

theorem measurable_primedEvenTerminalFullComplementStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (terminal : IncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    Measurable (primedEvenTerminalFullComplementStatistic
      m k C first labels terminal activeBases) := by
  exact (measurable_restrictComplementStoppedRuns
    (primedInitialBase first) labels C activeBases).comp
      ((measurable_stoppedPaperBlockVector
        (primedInitialBase first) labels).comp
        (measurable_actualPrimedTerminalVector
          m k first labels hnondist terminal
            (primedEvenSourceConstraint m k C first labels terminal)))

noncomputable def primedEvenTerminalActiveFullComplementStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair) (terminal : IncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    (ℕ → Direction) →
      ((ActiveFreeStoppedBase (primedInitialBase first) labels C
        activeBases → ℕ) × Direction) ×
      ComplementStoppedRuns (primedInitialBase first) labels C activeBases :=
  fun omega ↦
    (primedEvenActiveFreeStatistic
        m k C first labels terminal activeBases omega,
      primedEvenTerminalFullComplementStatistic
        m k C first labels terminal activeBases omega)

theorem measurable_primedEvenTerminalActiveFullComplementStatistic {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (terminal : IncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    Measurable (primedEvenTerminalActiveFullComplementStatistic
      m k C first labels terminal activeBases) := by
  exact (measurable_primedEvenActiveFreeStatistic
    m k C first labels hnondist terminal activeBases).prodMk
      (measurable_primedEvenTerminalFullComplementStatistic
        m k C first labels hnondist terminal activeBases)

theorem primedEven_strictRightWinner_active_fullComplement_direction_hasLaw
    {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (terminal : IncrementPair) (hm : 0 < m) (hk : 0 < k)
    (hcard : C.card = k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : PrimedEvenOffBaseMixedCondition first labels terminal m C)
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
    HasLaw
      (primedEvenTerminalActiveFullComplementStatistic
        m k C first labels terminal activeBases)
      (((sourceTruncatedProfileMeasure m
          (activeFreeStoppedShape (primedInitialBase first) labels C
            activeBases)).prod directionLaw).prod
        (stoppedMixedComplementRunMeasure (primedInitialBase first) labels m C
          activeBases externalLeft
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
  have h := activeFree_fullComplement_capped_hasLaw_of_joint
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
    (primedEvenTerminalActiveFullComplementStatistic
      m k C first labels terminal activeBases)
    (((sourceTruncatedProfileMeasure m
        (activeFreeStoppedShape (primedInitialBase first) labels C
          activeBases)).prod directionLaw).prod
      (stoppedMixedComplementRunMeasure (primedInitialBase first) labels m C
        activeBases externalLeft (primedStoppedExternalRight first labels)))
    incrementLaw[|A] at h
  simpa only [A, activeBases, externalLeft] using h

noncomputable def primedEvenTerminalFullComplementPath {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair) (terminal : IncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    (ℕ → Site) → ComplementStoppedRuns
      (primedInitialBase first) labels C activeBases :=
  fun s ↦ (liftIncrementStatisticToPath
    (primedEvenTerminalActiveFullComplementStatistic
      m k C first labels terminal activeBases) s).2

theorem measurable_primedEvenTerminalFullComplementPath {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (terminal : IncrementPair)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels)) :
    Measurable (primedEvenTerminalFullComplementPath
      m k C first labels terminal activeBases) :=
  measurable_snd.comp (measurable_liftIncrementStatisticToPath
    (measurable_primedEvenTerminalActiveFullComplementStatistic
      m k C first labels hnondist terminal activeBases))

theorem primedEven_strictRightWinner_active_fullComplement_path_map_law
    {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (terminal : IncrementPair) (hm : 0 < m) (hk : 0 < k)
    (hcard : C.card = k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : PrimedEvenOffBaseMixedCondition first labels terminal m C)
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
            primedEvenTerminalFullComplementPath
              m k C first labels terminal activeBases s)) =
      simpleRandomWalkLaw
          (simpleRandomWalk ''
            (actualPrimedTerminalVectorEvent m k first labels terminal
                (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C)) •
        (((sourceTruncatedProfileMeasure m
          (activeFreeStoppedShape (primedInitialBase first) labels C
            activeBases)).prod directionLaw).prod
          (stoppedMixedComplementRunMeasure (primedInitialBase first) labels m C
            activeBases externalLeft
              (primedStoppedExternalRight first labels))) := by
  dsimp only
  let externalLeft := primedEvenTerminalExternalLeft first labels terminal
  let activeBases := primedEvenStrictRightWinnerBases first labels
    externalLeft candidateBases
  let A := actualPrimedTerminalVectorEvent m k first labels terminal
    (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C
  let J := primedEvenTerminalActiveFullComplementStatistic
    m k C first labels terminal activeBases
  have hA : MeasurableSet A := by
    dsimp only [A]
    rw [primedEven_source_partition m k C first labels terminal hm hk hfree]
    unfold actualPrimedTerminalVectorEvent
    exact MeasurableSet.iUnion fun v ↦ MeasurableSet.iUnion fun _ ↦
      measurableSet_stoppedPrefixAtom
        (reconstructedPrimedTerminalStoppedPrefix first labels v terminal)
  have hJ : Measurable J :=
    measurable_primedEvenTerminalActiveFullComplementStatistic
      m k C first labels hnondist terminal activeBases
  have hLaw := liftIncrementStatistic_path_map_law hA hJ
    (primedEven_strictRightWinner_active_fullComplement_direction_hasLaw
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
            primedEvenTerminalFullComplementPath
              m k C first labels terminal activeBases s)) =
      (simpleRandomWalkLaw.restrict (simpleRandomWalk '' A)).map
        (liftIncrementStatisticToPath J) := by
          apply Measure.map_congr
          filter_upwards [ae_restrict_mem hPath] with s hs
          rcases hs with ⟨omega, homega, rfl⟩
          simp only [primedEvenActiveFreePathLazy,
            primedEvenActiveFreePathNext,
            primedEvenTerminalFullComplementPath,
            liftIncrementStatisticToPath_simpleRandomWalk, J,
            primedEvenTerminalActiveFullComplementStatistic,
            primedEvenTerminalFullComplementStatistic]
    _ = _ := by simpa only [A, activeBases, externalLeft, J] using hLaw

theorem
    primedEvenTerminalStrictRightProp49_fullComplement_orderedHistory_screenEstimate_of_fiberwise
    {m A : ℕ} {alpha : ℝ} {screen : Set (ℕ → Site)}
    {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    (D : PrimedEvenTerminalStrictRightProp49AtomData
      m (stageNumber r) A alpha screen)
    (c : Fin (stageNumber r) → Site)
    (hdet : EventDeterminedByOn D.atom
      (orderedCanonicalHistoryEvent m i a r c)
      (primedEvenTerminalFullComplementPath m (stageNumber r) D.C D.first
        D.labels D.terminal
        (primedEvenStrictRightWinnerBases D.first D.labels
          (primedEvenTerminalExternalLeft D.first D.labels D.terminal)
            D.candidateBases))) :
    RefinedAtomScreenEstimate
      (primedEvenTerminalOrderedHistoryPathAtom
        m i a r D.C D.first D.labels D.terminal c) screen
      (sourceProp49ScreenRate m A alpha) := by
  let externalLeft :=
    primedEvenTerminalExternalLeft D.first D.labels D.terminal
  let activeBases := primedEvenStrictRightWinnerBases D.first D.labels
    externalLeft D.candidateBases
  let z := primedEvenTerminalFullComplementPath
    m (stageNumber r) D.C D.first D.labels D.terminal activeBases
  let history := orderedCanonicalHistoryEvent m i a r c
  let H : Set (ComplementStoppedRuns
      (primedInitialBase D.first) D.labels D.C activeBases) :=
    {v | ∃ s ∈ D.atom, s ∈ history ∧ z s = v}
  have hH : MeasurableSet H := MeasurableSet.of_discrete
  have heq : D.atom ∩ history = D.atom ∩ z ⁻¹' H := by
    exact inter_eq_inter_preimage_of_eventDeterminedByOn
      D.atom history z hdet
  let complementLaw := stoppedMixedComplementRunMeasure
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
    exact stoppedMixedComplementRunMeasure_isProbabilityMeasure
      (primedInitialBase D.first) D.labels m D.C activeBases externalLeft
        (primedStoppedExternalRight D.first D.labels) hpos
  let F : StoppedTruncatedProp49HistoryFactorization D.toInput history :=
    { Z := ComplementStoppedRuns
        (primedInitialBase D.first) D.labels D.C activeBases
      measurableSpaceZ := inferInstance
      complementLaw := complementLaw
      sFiniteComplementLaw := inferInstance
      complement := z
      measurable_complement :=
        measurable_primedEvenTerminalFullComplementPath
          m (stageNumber r) D.C D.first D.labels D.nondistinguished
            D.terminal activeBases
      historySet := H
      measurable_historySet := hH
      history_eq := heq
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
                  primedEvenTerminalFullComplementPath m (stageNumber r)
                    D.C D.first D.labels D.terminal activeBases s)) =
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
          primedEven_strictRightWinner_active_fullComplement_path_map_law
            m (stageNumber r) D.C D.first D.labels D.nondistinguished
              D.terminal D.m_pos D.k_pos D.creation_card
              D.creation_pairFree D.offBase D.terminal_mem
              D.admissible_nonempty D.candidateBases }
  rw [primedEvenTerminalOrderedHistoryPathAtom_eq_coarse_inter_history]
  exact F.history_screen_le D.toInput

theorem primedEvenTerminalStrictRightProp49_fullComplement_orderedProfileHistory_screenEstimate_of_fiberwise
    {m A : ℕ} {alpha : ℝ} {screen : Set (ℕ → Site)}
    {profiles : Fin 6 → HLOZProp47SourceObjects.ExternalProfilePair}
    {cStar : Fin 6 → ℝ} {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    (D : PrimedEvenTerminalStrictRightProp49AtomData
      m (stageNumber r) A alpha screen)
    (c : Fin (stageNumber r) → Site)
    (hdet : EventDeterminedByOn D.atom
      (orderedProfileHistoryEvent profiles cStar m i a r c)
      (primedEvenTerminalFullComplementPath m (stageNumber r) D.C D.first
        D.labels D.terminal
        (primedEvenStrictRightWinnerBases D.first D.labels
          (primedEvenTerminalExternalLeft D.first D.labels D.terminal)
            D.candidateBases))) :
    RefinedAtomScreenEstimate
      (orderedProfileHistoryPathAtom profiles cStar m i a r c D.atom) screen
      (sourceProp49ScreenRate m A alpha) := by
  let externalLeft :=
    primedEvenTerminalExternalLeft D.first D.labels D.terminal
  let activeBases := primedEvenStrictRightWinnerBases D.first D.labels
    externalLeft D.candidateBases
  let z := primedEvenTerminalFullComplementPath
    m (stageNumber r) D.C D.first D.labels D.terminal activeBases
  let complementLaw := stoppedMixedComplementRunMeasure
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
    exact stoppedMixedComplementRunMeasure_isProbabilityMeasure
      (primedInitialBase D.first) D.labels m D.C activeBases externalLeft
        (primedStoppedExternalRight D.first D.labels) hpos
  change RefinedAtomScreenEstimate
    (D.atom ∩ orderedProfileHistoryEvent profiles cStar m i a r c) screen
      (sourceProp49ScreenRate m A alpha)
  apply refinedAtomScreenEstimate_of_joint_complement_determined
    D.toInput complementLaw z
  · exact measurable_primedEvenTerminalFullComplementPath
      m (stageNumber r) D.C D.first D.labels D.nondistinguished
        D.terminal activeBases
  · exact MeasurableSet.of_discrete
  · exact hdet
  · simpa only [PrimedEvenTerminalStrictRightProp49AtomData.toInput,
      primedEvenTerminalStrictRightProp49AtomInput,
      PrimedEvenTerminalStrictRightProp49AtomData.atom, activeBases,
      externalLeft, complementLaw, z] using
      primedEven_strictRightWinner_active_fullComplement_path_map_law
        m (stageNumber r) D.C D.first D.labels D.nondistinguished
          D.terminal D.m_pos D.k_pos D.creation_card
          D.creation_pairFree D.offBase D.terminal_mem
          D.admissible_nonempty D.candidateBases

/-! ### A branch-independent full-complement interface

The four stopped encodings have different complement-coordinate types.  A
single product-valued complement map would therefore erase useful dependent
type information.  The following predicate instead dispatches on the literal
stopped atom.  It says exactly that, on that coarse atom, the complete
chronological coordinates outside the active winner bases determine the
ordered preceding history.  The probability estimate is then a theorem, not
an additional field of the source package. -/

noncomputable def ConcreteStoppedProp49AtomData.FullComplementHistoryDetermined
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    {profiles : Fin 6 → HLOZProp47SourceObjects.ExternalProfilePair}
    {cStar : Fin 6 → ℝ} {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    (D : ConcreteStoppedProp49AtomData
      m (stageNumber r) A alpha screen)
    (c : Fin (stageNumber r) → Site) : Prop :=
  match D with
  | .unprimedEvenLeft data =>
      EventDeterminedByOn data.atom
        (orderedProfileHistoryEvent profiles cStar m i a r c)
        (unprimedEvenFullComplementPath m (stageNumber r) data.C data.labels
          (unprimedEvenLeftWinnerBases data.labels data.candidateBases))
  | .primedOddStrictRight data =>
      EventDeterminedByOn data.atom
        (orderedProfileHistoryEvent profiles cStar m i a r c)
        (primedOddFullComplementPath m (stageNumber r) data.C data.first
          data.labels
          (primedOddStrictRightWinnerBases data.first data.labels
            data.candidateBases))
  | .unprimedOddTerminalTieLeft data =>
      EventDeterminedByOn data.atom
        (orderedProfileHistoryEvent profiles cStar m i a r c)
        (unprimedOddTerminalFullComplementPath m (stageNumber r) data.C
          data.labels data.terminal
          (unprimedOddTieLeftWinnerBases data.labels
            (unprimedOddTerminalExternalRight data.labels data.terminal)
              data.candidateBases))
  | .primedEvenTerminalStrictRight data =>
      EventDeterminedByOn data.atom
        (orderedProfileHistoryEvent profiles cStar m i a r c)
        (primedEvenTerminalFullComplementPath m (stageNumber r) data.C
          data.first data.labels data.terminal
          (primedEvenStrictRightWinnerBases data.first data.labels
            (primedEvenTerminalExternalLeft data.first data.labels
              data.terminal) data.candidateBases))

/-- Branch-independent statement that the chronological complement fixes
the ordered creation tuple on a literal checkerboard atom. -/
noncomputable def ConcreteStoppedProp49AtomData.FullComplementOrderedCreationDetermined
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    {r : StageIndex}
    (D : ConcreteStoppedProp49AtomData
      m (stageNumber r) A alpha screen)
    (c : Fin (stageNumber r) → Site) : Prop :=
  match D with
  | .unprimedEvenLeft data =>
      EventDeterminedByOn data.atom
        (orderedCreationSitesEvent m (stageNumber r) c)
        (unprimedEvenFullComplementPath m (stageNumber r) data.C data.labels
          (unprimedEvenLeftWinnerBases data.labels data.candidateBases))
  | .primedOddStrictRight data =>
      EventDeterminedByOn data.atom
        (orderedCreationSitesEvent m (stageNumber r) c)
        (primedOddFullComplementPath m (stageNumber r) data.C data.first
          data.labels
          (primedOddStrictRightWinnerBases data.first data.labels
            data.candidateBases))
  | .unprimedOddTerminalTieLeft data =>
      EventDeterminedByOn data.atom
        (orderedCreationSitesEvent m (stageNumber r) c)
        (unprimedOddTerminalFullComplementPath m (stageNumber r) data.C
          data.labels data.terminal
          (unprimedOddTieLeftWinnerBases data.labels
            (unprimedOddTerminalExternalRight data.labels data.terminal)
              data.candidateBases))
  | .primedEvenTerminalStrictRight data =>
      EventDeterminedByOn data.atom
        (orderedCreationSitesEvent m (stageNumber r) c)
        (primedEvenTerminalFullComplementPath m (stageNumber r) data.C
          data.first data.labels data.terminal
          (primedEvenStrictRightWinnerBases data.first data.labels
            (primedEvenTerminalExternalLeft data.first data.labels
              data.terminal) data.candidateBases))

/-- Branch-independent determination of the initial one-site pairing event. -/
noncomputable def ConcreteStoppedProp49AtomData.FullComplementBasePairingDetermined
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    {i : Fin 6} {r : StageIndex}
    (D : ConcreteStoppedProp49AtomData
      m (stageNumber r) A alpha screen) : Prop :=
  match D with
  | .unprimedEvenLeft data =>
      EventDeterminedByOn data.atom (prefixPairingEvent m i 1)
        (unprimedEvenFullComplementPath m (stageNumber r) data.C data.labels
          (unprimedEvenLeftWinnerBases data.labels data.candidateBases))
  | .primedOddStrictRight data =>
      EventDeterminedByOn data.atom (prefixPairingEvent m i 1)
        (primedOddFullComplementPath m (stageNumber r) data.C data.first
          data.labels
          (primedOddStrictRightWinnerBases data.first data.labels
            data.candidateBases))
  | .unprimedOddTerminalTieLeft data =>
      EventDeterminedByOn data.atom (prefixPairingEvent m i 1)
        (unprimedOddTerminalFullComplementPath m (stageNumber r) data.C
          data.labels data.terminal
          (unprimedOddTieLeftWinnerBases data.labels
            (unprimedOddTerminalExternalRight data.labels data.terminal)
              data.candidateBases))
  | .primedEvenTerminalStrictRight data =>
      EventDeterminedByOn data.atom (prefixPairingEvent m i 1)
        (primedEvenTerminalFullComplementPath m (stageNumber r) data.C
          data.first data.labels data.terminal
          (primedEvenStrictRightWinnerBases data.first data.labels
            (primedEvenTerminalExternalLeft data.first data.labels
              data.terminal) data.candidateBases))

/-- Any stopped-source atom with a pair-free `k`-site creation set lies in
the one-site pairing history.  This is independent of the stopped vector
encoding and is shared by all four temporal-parity/winner branches. -/
theorem levelCreationSite_eq_stoppedTerminalBase_of_mem_actualStoppedVectorEvent
    {q m k : ℕ} {labels : Fin q → IncrementPair}
    {E : Finset (Fin (q + 1) → ℕ)} {omega : ℕ → Direction}
    (homega : omega ∈ actualStoppedVectorEvent m k labels E) :
    levelCreationSite (simpleRandomWalk omega) m k =
      stoppedTerminalBase labels := by
  classical
  let v := actualStoppedVector m k labels E omega
  have hv := actualStoppedVector_spec m k labels E homega
  have hfirst : IsFirstKStoppedPrefix m k
      (reconstructedStoppedPrefix labels v) :=
    (Finset.mem_filter.mp hv.1).2
  have htime := prefixAtom_subset_firstKSitesReachLevel_fiber hfirst hv.2
  have hposition := simpleRandomWalk_congr_extendPrefix
    (reconstructedStoppedPrefix labels v).2 omega hv.2
      (reconstructedStoppedPrefix labels v).1 (le_refl _)
  unfold levelCreationSite
  change firstKSitesReachLevel m k (simpleRandomWalk omega) =
    ((reconstructedStoppedPrefix labels v).1 : WithTop ℕ) at htime
  rw [htime]
  simp only [HLOZFoundation.untopA_coe_nat]
  exact hposition.trans
    (reconstructedStoppedPrefix_current labels v)

theorem levelCreationSite_eq_primedStoppedTerminalSite_of_mem_actualPrimedStoppedVectorEvent
    {q m k : ℕ} {first : Direction} {labels : Fin q → IncrementPair}
    {E : Finset (Fin (q + 1) → ℕ)} {omega : ℕ → Direction}
    (homega : omega ∈ actualPrimedStoppedVectorEvent
      m k first labels E) :
    levelCreationSite (simpleRandomWalk omega) m k =
      primedStoppedTerminalSite first labels := by
  classical
  rcases Set.mem_iUnion.mp homega with ⟨v, hv⟩
  rcases Set.mem_iUnion.mp hv with ⟨hvadmissible, hatom⟩
  have hfirst : IsFirstKStoppedPrefix m k
      (reconstructedPrimedStoppedPrefix first labels v) :=
    (Finset.mem_filter.mp hvadmissible).2
  have htime := prefixAtom_subset_firstKSitesReachLevel_fiber hfirst hatom
  have hposition := simpleRandomWalk_congr_extendPrefix
    (reconstructedPrimedStoppedPrefix first labels v).2 omega hatom
      (reconstructedPrimedStoppedPrefix first labels v).1 (le_refl _)
  unfold levelCreationSite
  change firstKSitesReachLevel m k (simpleRandomWalk omega) =
    ((reconstructedPrimedStoppedPrefix first labels v).1 : WithTop ℕ) at htime
  rw [htime]
  simp only [HLOZFoundation.untopA_coe_nat]
  exact hposition.trans
    (reconstructedPrimedStoppedPrefix_current first labels v)

theorem levelCreationSite_eq_unprimedOddTerminal_of_mem_actualOddStoppedVectorEvent
    {q m k : ℕ} {labels : Fin q → IncrementPair}
    {terminal : IncrementPair} {E : Finset (Fin (q + 1) → ℕ)}
    {omega : ℕ → Direction}
    (homega : omega ∈ actualOddStoppedVectorEvent
      m k labels terminal E) :
    levelCreationSite (simpleRandomWalk omega) m k =
      stoppedTerminalBase labels + directionStep (terminal 0) := by
  classical
  rcases Set.mem_iUnion.mp homega with ⟨v, hv⟩
  rcases Set.mem_iUnion.mp hv with ⟨hvadmissible, hatom⟩
  let p := reconstructedOddStoppedPrefix labels v terminal
  let T := p.1 - 1
  have hfirst : IsFirstKPrefixAt m k T p.2 :=
    (Finset.mem_filter.mp hvadmissible).2
  have htime := prefixAtom_subset_firstKSitesReachLevel_fiber_at
    (Nat.sub_le _ _) hfirst hatom
  have hposition := simpleRandomWalk_congr_extendPrefix p.2 omega hatom T
    (Nat.sub_le _ _)
  unfold levelCreationSite
  change firstKSitesReachLevel m k (simpleRandomWalk omega) =
    (T : WithTop ℕ) at htime
  rw [htime]
  simp only [HLOZFoundation.untopA_coe_nat]
  exact hposition.trans (by
    simpa only [p, T] using
      reconstructedOddStoppedPrefix_threshold_current labels v terminal)

theorem levelCreationSite_eq_primedEvenTerminal_of_mem_actualPrimedTerminalVectorEvent
    {q m k : ℕ} {first : Direction} {labels : Fin q → IncrementPair}
    {terminal : IncrementPair} {E : Finset (Fin (q + 1) → ℕ)}
    {omega : ℕ → Direction}
    (homega : omega ∈ actualPrimedTerminalVectorEvent
      m k first labels terminal E) :
    levelCreationSite (simpleRandomWalk omega) m k =
      primedStoppedTerminalSite first labels + directionStep (terminal 0) := by
  classical
  rcases Set.mem_iUnion.mp homega with ⟨v, hv⟩
  rcases Set.mem_iUnion.mp hv with ⟨hvadmissible, hatom⟩
  let p := reconstructedPrimedTerminalStoppedPrefix first labels v terminal
  let T := p.1 - 1
  have hfirst : IsFirstKPrefixAt m k T p.2 :=
    (Finset.mem_filter.mp hvadmissible).2
  have htime := prefixAtom_subset_firstKSitesReachLevel_fiber_at
    (Nat.sub_le _ _) hfirst hatom
  have hposition := simpleRandomWalk_congr_extendPrefix p.2 omega hatom T
    (Nat.sub_le _ _)
  unfold levelCreationSite
  change firstKSitesReachLevel m k (simpleRandomWalk omega) =
    (T : WithTop ℕ) at htime
  rw [htime]
  simp only [HLOZFoundation.untopA_coe_nat]
  exact hposition.trans (by
    simpa only [p, T] using
      reconstructedPrimedTerminalStoppedPrefix_threshold_current
        first labels v terminal)

/-- At the two-site threshold, the unordered creation set and the fixed
last-created site determine the complete ordered creation tuple. -/
theorem orderedCreationSites_two_eq_of_set_eq_of_last_eq
    {s t : Path} {m : ℕ}
    (hsets : levelCreationSitesUpTo s m 2 =
      levelCreationSitesUpTo t m 2)
    (hlast : levelCreationSite s m 2 = levelCreationSite t m 2)
    (hne : levelCreationSite s m 1 ≠ levelCreationSite s m 2) :
    orderedCreationSites m 2 s = orderedCreationSites m 2 t := by
  funext j
  fin_cases j
  · change levelCreationSite s m 1 = levelCreationSite t m 1
    have hmem : levelCreationSite s m 1 ∈
        levelCreationSitesUpTo t m 2 := by
      rw [← hsets]
      apply Finset.mem_image.mpr
      exact ⟨1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩
    have hor : levelCreationSite s m 1 = levelCreationSite t m 1 ∨
        levelCreationSite s m 1 = levelCreationSite t m 2 := by
      rw [levelCreationSitesUpTo, Finset.mem_image] at hmem
      rcases hmem with ⟨j, hj, heq⟩
      have hj' : j = 1 ∨ j = 2 := by
        rw [Finset.mem_Icc] at hj
        omega
      rcases hj' with rfl | rfl
      · exact Or.inl heq.symm
      · exact Or.inr heq.symm
    rcases hor with hfirst | hlast'
    · exact hfirst
    · exact False.elim (hne (hlast'.trans hlast.symm))
  · simpa [orderedCreationSites] using hlast

/-- If a two-site stopped atom fixes both the unordered creation set and the
last-created site, then every ordered two-site creation event is constant on
that atom.  Finiteness of the second threshold is used only to rule out the
two creation sites coinciding. -/
theorem eventDeterminedByOn_orderedCreationSitesEvent_two_of_fixed_source_last
    {Z : Type*} (atom : Set Path) (z : Path → Z) (m : ℕ)
    (C : Finset Site) (last : Site) (c : Fin 2 → Site)
    (hm : 0 < m)
    (hthreshold : atom ⊆ hlozThresholdTimeEventK m 2)
    (hfixed : ∀ s ∈ atom, levelCreationSitesUpTo s m 2 = C)
    (hlast : ∀ s ∈ atom, levelCreationSite s m 2 = last) :
    EventDeterminedByOn atom (orderedCreationSitesEvent m 2 c) z := by
  intro s hs t ht _hz
  have hsets : levelCreationSitesUpTo s m 2 =
      levelCreationSitesUpTo t m 2 :=
    (hfixed s hs).trans (hfixed t ht).symm
  have hlast' : levelCreationSite s m 2 = levelCreationSite t m 2 :=
    (hlast s hs).trans (hlast t ht).symm
  have hfinite : firstKSitesReachLevel m 2 s ≠ ⊤ :=
    ne_top_of_lt (hthreshold hs)
  have hne : levelCreationSite s m 1 ≠ levelCreationSite s m 2 :=
    levelCreationSite_ne_of_lt s m hm (by omega) (by omega) hfinite
  have hordered : orderedCreationSites m 2 s =
      orderedCreationSites m 2 t :=
    orderedCreationSites_two_eq_of_set_eq_of_last_eq hsets hlast' hne
  change orderedCreationSites m 2 s = c ↔ orderedCreationSites m 2 t = c
  rw [hordered]

theorem image_inter_stoppedSourceCondition_subset_prefixPairingEvent_xEast
    {m k : ℕ} {C : Finset Site} (E : Set (ℕ → Direction))
    (hk : 0 < k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C) :
    simpleRandomWalk '' (E ∩ stoppedSourceCondition m k C) ⊆
      prefixPairingEvent m (xIndex east) 1 := by
  rintro s ⟨omega, ⟨_hE, hsource⟩, rfl⟩
  rcases hsource with ⟨hthreshold, hC⟩
  have hk1 : 1 ≤ k := hk
  have hthresholdOne : simpleRandomWalk omega ∈
      hlozThresholdTimeEventK m 1 := by
    change firstKSitesReachLevel m 1 (simpleRandomWalk omega) <
      firstKSitesReachLevel (m + 1) 1 (simpleRandomWalk omega)
    exact (firstKSitesReachLevel_mono_k
      (simpleRandomWalk omega) m hk1).trans_lt hthreshold
  have hsubset : levelCreationSitesUpTo (simpleRandomWalk omega) m 1 ⊆ C := by
    intro x hx
    rw [← hC]
    rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨j, ?_, rfl⟩
    rcases Finset.mem_Icc.mp hj with ⟨hj0, hj1⟩
    exact Finset.mem_Icc.mpr ⟨hj0, hj1.trans hk1⟩
  refine ⟨hthresholdOne, ?_⟩
  rw [HLOZPairing.pairingRelation_xIndex]
  intro x hx y hy hxy
  exact hfree x (hsubset hx) y (hsubset hy) hxy

/-- The initial-pairing component of the full-complement history condition
is therefore automatic for every literal X-east Proposition-4.9 atom. -/
theorem ConcreteStoppedProp49AtomData.fullComplementBasePairingDetermined_xEast
    {m A : ℕ} {alpha : ℝ} {screen : Set Path} {r : StageIndex}
    (D : ConcreteStoppedProp49AtomData
      m (stageNumber r) A alpha screen) :
    ConcreteStoppedProp49AtomData.FullComplementBasePairingDetermined
      (i := xIndex east) D := by
  cases D with
  | unprimedEvenLeft data =>
      apply EventDeterminedByOn.of_subset
      simpa only [UnprimedEvenLeftWinnerProp49AtomData.atom] using
        image_inter_stoppedSourceCondition_subset_prefixPairingEvent_xEast
          (actualStoppedVectorEvent m (stageNumber r) data.labels
            (stoppedRunVectorBox data.q m))
          data.k_pos data.creation_pairFree
  | primedOddStrictRight data =>
      apply EventDeterminedByOn.of_subset
      simpa only [PrimedOddStrictRightWinnerProp49AtomData.atom] using
        image_inter_stoppedSourceCondition_subset_prefixPairingEvent_xEast
          (actualPrimedStoppedVectorEvent m (stageNumber r) data.first
            data.labels (stoppedRunVectorBox data.q m))
          data.k_pos data.creation_pairFree
  | unprimedOddTerminalTieLeft data =>
      apply EventDeterminedByOn.of_subset
      simpa only [UnprimedOddTerminalTieLeftProp49AtomData.atom] using
        image_inter_stoppedSourceCondition_subset_prefixPairingEvent_xEast
          (actualOddStoppedVectorEvent m (stageNumber r) data.labels
            data.terminal (stoppedRunVectorBox data.q m))
          data.k_pos data.creation_pairFree
  | primedEvenTerminalStrictRight data =>
      apply EventDeterminedByOn.of_subset
      simpa only [PrimedEvenTerminalStrictRightProp49AtomData.atom] using
        image_inter_stoppedSourceCondition_subset_prefixPairingEvent_xEast
          (actualPrimedTerminalVectorEvent m (stageNumber r) data.first
            data.labels data.terminal (stoppedRunVectorBox data.q m))
          data.k_pos data.creation_pairFree

/-- Branch-independent determination of each concrete stage before the
current Proposition-4.9 screen. -/
noncomputable def ConcreteStoppedProp49AtomData.FullComplementPriorStagesDetermined
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    {profiles : Fin 6 → HLOZProp47SourceObjects.ExternalProfilePair}
    {cStar : Fin 6 → ℝ} {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    (D : ConcreteStoppedProp49AtomData
      m (stageNumber r) A alpha screen) : Prop :=
  match D with
  | .unprimedEvenLeft data =>
      ∀ (j : Fin 3), j.1 < r.1 →
        EventDeterminedByOn data.atom
          (prop47StageEvent profiles cStar i m j
            (alphaValue (tripleAlphaIndex a j)))
          (unprimedEvenFullComplementPath m (stageNumber r) data.C
            data.labels
            (unprimedEvenLeftWinnerBases data.labels data.candidateBases))
  | .primedOddStrictRight data =>
      ∀ (j : Fin 3), j.1 < r.1 →
        EventDeterminedByOn data.atom
          (prop47StageEvent profiles cStar i m j
            (alphaValue (tripleAlphaIndex a j)))
          (primedOddFullComplementPath m (stageNumber r) data.C data.first
            data.labels
            (primedOddStrictRightWinnerBases data.first data.labels
              data.candidateBases))
  | .unprimedOddTerminalTieLeft data =>
      ∀ (j : Fin 3), j.1 < r.1 →
        EventDeterminedByOn data.atom
          (prop47StageEvent profiles cStar i m j
            (alphaValue (tripleAlphaIndex a j)))
          (unprimedOddTerminalFullComplementPath m (stageNumber r) data.C
            data.labels data.terminal
            (unprimedOddTieLeftWinnerBases data.labels
              (unprimedOddTerminalExternalRight data.labels data.terminal)
                data.candidateBases))
  | .primedEvenTerminalStrictRight data =>
      ∀ (j : Fin 3), j.1 < r.1 →
        EventDeterminedByOn data.atom
          (prop47StageEvent profiles cStar i m j
            (alphaValue (tripleAlphaIndex a j)))
          (primedEvenTerminalFullComplementPath m (stageNumber r) data.C
            data.first data.labels data.terminal
            (primedEvenStrictRightWinnerBases data.first data.labels
              (primedEvenTerminalExternalLeft data.first data.labels
                data.terminal) data.candidateBases))

/-- At the second source stage there is exactly one preceding screen.  This
specialized predicate records that screen directly, avoiding a vacuous
finite-index function in the literal source interface. -/
noncomputable def ConcreteStoppedProp49AtomData.FullComplementStageZeroDetermined
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    {profiles : Fin 6 → HLOZProp47SourceObjects.ExternalProfilePair}
    {cStar : Fin 6 → ℝ} {a : AlphaTriple} {r : StageIndex}
    (D : ConcreteStoppedProp49AtomData
      m (stageNumber r) A alpha screen) : Prop :=
  match D with
  | .unprimedEvenLeft data =>
      EventDeterminedByOn data.atom
        (prop47StageEvent profiles cStar (xIndex east) m 0
          (alphaValue (tripleAlphaIndex a 0)))
        (unprimedEvenFullComplementPath m (stageNumber r) data.C data.labels
          (unprimedEvenLeftWinnerBases data.labels data.candidateBases))
  | .primedOddStrictRight data =>
      EventDeterminedByOn data.atom
        (prop47StageEvent profiles cStar (xIndex east) m 0
          (alphaValue (tripleAlphaIndex a 0)))
        (primedOddFullComplementPath m (stageNumber r) data.C data.first data.labels
          (primedOddStrictRightWinnerBases data.first data.labels
            data.candidateBases))
  | .unprimedOddTerminalTieLeft data =>
      EventDeterminedByOn data.atom
        (prop47StageEvent profiles cStar (xIndex east) m 0
          (alphaValue (tripleAlphaIndex a 0)))
        (unprimedOddTerminalFullComplementPath m (stageNumber r) data.C data.labels
          data.terminal
          (unprimedOddTieLeftWinnerBases data.labels
            (unprimedOddTerminalExternalRight data.labels data.terminal)
              data.candidateBases))
  | .primedEvenTerminalStrictRight data =>
      EventDeterminedByOn data.atom
        (prop47StageEvent profiles cStar (xIndex east) m 0
          (alphaValue (tripleAlphaIndex a 0)))
        (primedEvenTerminalFullComplementPath m (stageNumber r) data.C data.first
          data.labels data.terminal
          (primedEvenStrictRightWinnerBases data.first data.labels
            (primedEvenTerminalExternalLeft data.first data.labels
              data.terminal) data.candidateBases))

/-- The genuinely nonautomatic part of the low-scale stage-zero history.
The threshold atom itself supplies the prefix-pairing, avoidance, and
two-creation-site distance factors.  What can still depend on the earlier
active coordinates is precisely candidate membership, the empty-`Theta`
condition, and the logarithmic candidate-cardinality bound. -/
def stageZeroLowScaleResidualEvent
    (profiles : Fin 6 → HLOZProp47SourceObjects.ExternalProfilePair)
    (cStar : Fin 6 → ℝ) (m : ℕ) (a : AlphaTriple) : Set Path :=
  nextCreationIsCandidateEvent (xIndex east) m 1
      (alphaValue (tripleAlphaIndex a 0) + delta) ∩
    {s | stoppedThetaSites (profiles (xIndex east))
        (cStar (xIndex east)) s m 1 = ∅} ∩
    {s | ((nearFavoriteSites (xIndex east) s m 1 kappaOne).card : ℝ) ≤
      Real.log m ^ 2}

/-- Branch-independent fibre determination of just the residual low-scale
part of the stage-zero event.  When the first mesh exponent is above
`kappaTwo`, this premise is not needed at all. -/
noncomputable def
    ConcreteStoppedProp49AtomData.FullComplementStageZeroLowScaleDetermined
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    {profiles : Fin 6 → HLOZProp47SourceObjects.ExternalProfilePair}
    {cStar : Fin 6 → ℝ} {a : AlphaTriple} {r : StageIndex}
    (D : ConcreteStoppedProp49AtomData
      m (stageNumber r) A alpha screen) : Prop :=
  match D with
  | .unprimedEvenLeft data =>
      EventDeterminedByOn data.atom
        (stageZeroLowScaleResidualEvent profiles cStar m a)
        (unprimedEvenFullComplementPath m (stageNumber r) data.C data.labels
          (unprimedEvenLeftWinnerBases data.labels data.candidateBases))
  | .primedOddStrictRight data =>
      EventDeterminedByOn data.atom
        (stageZeroLowScaleResidualEvent profiles cStar m a)
        (primedOddFullComplementPath m (stageNumber r) data.C data.first
          data.labels
          (primedOddStrictRightWinnerBases data.first data.labels
            data.candidateBases))
  | .unprimedOddTerminalTieLeft data =>
      EventDeterminedByOn data.atom
        (stageZeroLowScaleResidualEvent profiles cStar m a)
        (unprimedOddTerminalFullComplementPath m (stageNumber r) data.C
          data.labels data.terminal
          (unprimedOddTieLeftWinnerBases data.labels
            (unprimedOddTerminalExternalRight data.labels data.terminal)
              data.candidateBases))
  | .primedEvenTerminalStrictRight data =>
      EventDeterminedByOn data.atom
        (stageZeroLowScaleResidualEvent profiles cStar m a)
        (primedEvenTerminalFullComplementPath m (stageNumber r) data.C
          data.first data.labels data.terminal
          (primedEvenStrictRightWinnerBases data.first data.labels
            (primedEvenTerminalExternalLeft data.first data.labels
              data.terminal) data.candidateBases))

theorem ConcreteStoppedProp49AtomData.fullComplementPriorStagesDetermined_stageOne_of_stageZero
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    {profiles : Fin 6 → HLOZProp47SourceObjects.ExternalProfilePair}
    {cStar : Fin 6 → ℝ} {a : AlphaTriple}
    (D : ConcreteStoppedProp49AtomData m 2 A alpha screen)
    (hzero : ConcreteStoppedProp49AtomData.FullComplementStageZeroDetermined
      (profiles := profiles) (cStar := cStar) (a := a)
        (r := (1 : StageIndex)) D) :
    ConcreteStoppedProp49AtomData.FullComplementPriorStagesDetermined
      (profiles := profiles) (cStar := cStar) (i := xIndex east)
        (a := a) (r := (1 : StageIndex)) D := by
  cases D <;>
    simpa only [FullComplementStageZeroDetermined,
      FullComplementPriorStagesDetermined] using
        (fun (j : Fin 3) (hj : j.1 < (1 : StageIndex).1) ↦ by
          have hj0 : j = 0 := by apply Fin.ext; omega
          subst j
          exact hzero)

/-- The three literal reconstruction components imply the original
full-history fibre condition for every stopping-parity/winner branch. -/
theorem ConcreteStoppedProp49AtomData.fullComplementHistoryDetermined_of_stages
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    {profiles : Fin 6 → HLOZProp47SourceObjects.ExternalProfilePair}
    {cStar : Fin 6 → ℝ} {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    (D : ConcreteStoppedProp49AtomData
      m (stageNumber r) A alpha screen)
    (c : Fin (stageNumber r) → Site)
    (hordered : ConcreteStoppedProp49AtomData.FullComplementOrderedCreationDetermined
      D c)
    (hbase : ConcreteStoppedProp49AtomData.FullComplementBasePairingDetermined
      (i := i) D)
    (hstage : ConcreteStoppedProp49AtomData.FullComplementPriorStagesDetermined
      (profiles := profiles) (cStar := cStar) (i := i) (a := a) D) :
    ConcreteStoppedProp49AtomData.FullComplementHistoryDetermined D
      (profiles := profiles) (cStar := cStar) (i := i) (a := a) c := by
  cases D with
  | unprimedEvenLeft data =>
      simpa only [FullComplementHistoryDetermined,
        FullComplementOrderedCreationDetermined,
        FullComplementBasePairingDetermined,
        FullComplementPriorStagesDetermined] using
          eventDeterminedByOn_orderedProfileHistoryEvent_of_stages
            data.atom
              (unprimedEvenFullComplementPath m (stageNumber r) data.C
                data.labels
                (unprimedEvenLeftWinnerBases data.labels data.candidateBases))
              profiles cStar m i a r c hordered hbase hstage
  | primedOddStrictRight data =>
      simpa only [FullComplementHistoryDetermined,
        FullComplementOrderedCreationDetermined,
        FullComplementBasePairingDetermined,
        FullComplementPriorStagesDetermined] using
          eventDeterminedByOn_orderedProfileHistoryEvent_of_stages
            data.atom
              (primedOddFullComplementPath m (stageNumber r) data.C
                data.first data.labels
                (primedOddStrictRightWinnerBases data.first data.labels
                  data.candidateBases))
              profiles cStar m i a r c hordered hbase hstage
  | unprimedOddTerminalTieLeft data =>
      simpa only [FullComplementHistoryDetermined,
        FullComplementOrderedCreationDetermined,
        FullComplementBasePairingDetermined,
        FullComplementPriorStagesDetermined] using
          eventDeterminedByOn_orderedProfileHistoryEvent_of_stages
            data.atom
              (unprimedOddTerminalFullComplementPath m (stageNumber r)
                data.C data.labels data.terminal
                (unprimedOddTieLeftWinnerBases data.labels
                  (unprimedOddTerminalExternalRight data.labels data.terminal)
                    data.candidateBases))
              profiles cStar m i a r c hordered hbase hstage
  | primedEvenTerminalStrictRight data =>
      simpa only [FullComplementHistoryDetermined,
        FullComplementOrderedCreationDetermined,
        FullComplementBasePairingDetermined,
        FullComplementPriorStagesDetermined] using
          eventDeterminedByOn_orderedProfileHistoryEvent_of_stages
            data.atom
              (primedEvenTerminalFullComplementPath m (stageNumber r)
                data.C data.first data.labels data.terminal
                (primedEvenStrictRightWinnerBases data.first data.labels
                  (primedEvenTerminalExternalLeft data.first data.labels
                    data.terminal) data.candidateBases))
              profiles cStar m i a r c hordered hbase hstage

/-- Once the literal branch's full complement determines the ordered
preceding history, the checked joint product law and the checked coordinate
tail give the history-refined Proposition-4.9 estimate. -/
theorem ConcreteStoppedProp49AtomData.fullComplement_orderedProfileHistory_screenEstimate
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    {profiles : Fin 6 → HLOZProp47SourceObjects.ExternalProfilePair}
    {cStar : Fin 6 → ℝ} {i : Fin 6} {a : AlphaTriple} {r : StageIndex}
    (D : ConcreteStoppedProp49AtomData
      m (stageNumber r) A alpha screen)
    (c : Fin (stageNumber r) → Site)
    (hdet : ConcreteStoppedProp49AtomData.FullComplementHistoryDetermined D
      (profiles := profiles) (cStar := cStar) (i := i) (a := a) (r := r) c) :
    RefinedAtomScreenEstimate
      (orderedProfileHistoryPathAtom profiles cStar m i a r c D.atom)
      screen (sourceProp49ScreenRate m A alpha) := by
  cases D with
  | unprimedEvenLeft data =>
      exact
        unprimedEvenLeftWinnerProp49_fullComplement_orderedProfileHistory_screenEstimate_of_fiberwise
          data c hdet
  | primedOddStrictRight data =>
      exact
        primedOddStrictRightWinnerProp49_fullComplement_orderedProfileHistory_screenEstimate_of_fiberwise
          data c hdet
  | unprimedOddTerminalTieLeft data =>
      exact
        unprimedOddTerminalTieLeftProp49_fullComplement_orderedProfileHistory_screenEstimate_of_fiberwise
          data c hdet
  | primedEvenTerminalStrictRight data =>
      exact
        primedEvenTerminalStrictRightProp49_fullComplement_orderedProfileHistory_screenEstimate_of_fiberwise
          data c hdet

/-! ### First-stage towers

At stage zero there is only one level-creation site.  The raw source atom
fixes its singleton creation set and already carries the selected pairing
condition.  Consequently its ordered history is constant on the whole atom,
and the four checked complement laws yield Proposition 4.9 without a
separate history-determination premise. -/

theorem UnprimedEvenLeftWinnerProp49AtomData.atom_threshold_fixed
    {m k A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : UnprimedEvenLeftWinnerProp49AtomData m k A alpha screen) :
    D.atom ⊆ hlozThresholdTimeEventK m k ∧
      ∀ s ∈ D.atom, levelCreationSitesUpTo s m k = D.C := by
  constructor
  · rintro s ⟨omega, homega, rfl⟩
    exact homega.2.1
  · rintro s ⟨omega, homega, rfl⟩
    exact homega.2.2

theorem PrimedOddStrictRightWinnerProp49AtomData.atom_threshold_fixed
    {m k A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : PrimedOddStrictRightWinnerProp49AtomData m k A alpha screen) :
    D.atom ⊆ hlozThresholdTimeEventK m k ∧
      ∀ s ∈ D.atom, levelCreationSitesUpTo s m k = D.C := by
  constructor
  · rintro s ⟨omega, homega, rfl⟩
    exact homega.2.1
  · rintro s ⟨omega, homega, rfl⟩
    exact homega.2.2

theorem UnprimedOddTerminalTieLeftProp49AtomData.atom_threshold_fixed
    {m k A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : UnprimedOddTerminalTieLeftProp49AtomData m k A alpha screen) :
    D.atom ⊆ hlozThresholdTimeEventK m k ∧
      ∀ s ∈ D.atom, levelCreationSitesUpTo s m k = D.C := by
  constructor
  · rintro s ⟨omega, homega, rfl⟩
    exact homega.2.1
  · rintro s ⟨omega, homega, rfl⟩
    exact homega.2.2

theorem PrimedEvenTerminalStrictRightProp49AtomData.atom_threshold_fixed
    {m k A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : PrimedEvenTerminalStrictRightProp49AtomData m k A alpha screen) :
    D.atom ⊆ hlozThresholdTimeEventK m k ∧
      ∀ s ∈ D.atom, levelCreationSitesUpTo s m k = D.C := by
  constructor
  · rintro s ⟨omega, homega, rfl⟩
    exact homega.2.1
  · rintro s ⟨omega, homega, rfl⟩
    exact homega.2.2

theorem atom_subset_prefixPairingEvent_xEast_of_threshold_fixed
    {atom : Set Path} {m k : ℕ} {C : Finset Site}
    (hthreshold : atom ⊆ hlozThresholdTimeEventK m k)
    (hfixed : ∀ s ∈ atom, levelCreationSitesUpTo s m k = C)
    (hfree : PairFree (XPair east) C) :
    atom ⊆ prefixPairingEvent m (xIndex east) k := by
  intro s hs
  refine ⟨hthreshold hs, ?_⟩
  change PairFree (pairingRelation (xIndex east))
    (levelCreationSitesUpTo s m k)
  rw [pairingRelation_xIndex, hfixed s hs]
  exact hfree

theorem atom_subset_directAvoidance_two_of_threshold_two
    {atom : Set Path} {m : ℕ} (hm : 0 < m)
    (hthreshold : atom ⊆ hlozThresholdTimeEventK m 2) :
    atom ⊆ hlozDirectAvoidanceEvent m 2 := by
  intro s hs
  exact hlozThresholdTimeEventK_imp_directAvoidance
    s m 2 2 hm (by omega) (by omega) (hthreshold hs)

/-- Every literal two-site X-east stopped atom already lies in the
stage-zero prefix-pairing and avoidance events. -/
theorem ConcreteStoppedProp49AtomData.atom_subset_stageZero_fixed_events_xEast
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : ConcreteStoppedProp49AtomData m 2 A alpha screen) :
    D.atom ⊆ prefixPairingEvent m (xIndex east) 2 ∧
      D.atom ⊆ hlozDirectAvoidanceEvent m 2 := by
  cases D with
  | unprimedEvenLeft data =>
      have hsource :=
        UnprimedEvenLeftWinnerProp49AtomData.atom_threshold_fixed data
      exact ⟨atom_subset_prefixPairingEvent_xEast_of_threshold_fixed
          hsource.1 hsource.2 data.creation_pairFree,
        atom_subset_directAvoidance_two_of_threshold_two
          data.m_pos hsource.1⟩
  | primedOddStrictRight data =>
      have hsource :=
        PrimedOddStrictRightWinnerProp49AtomData.atom_threshold_fixed data
      exact ⟨atom_subset_prefixPairingEvent_xEast_of_threshold_fixed
          hsource.1 hsource.2 data.creation_pairFree,
        atom_subset_directAvoidance_two_of_threshold_two
          data.m_pos hsource.1⟩
  | unprimedOddTerminalTieLeft data =>
      have hsource :=
        UnprimedOddTerminalTieLeftProp49AtomData.atom_threshold_fixed data
      exact ⟨atom_subset_prefixPairingEvent_xEast_of_threshold_fixed
          hsource.1 hsource.2 data.creation_pairFree,
        atom_subset_directAvoidance_two_of_threshold_two
          data.m_pos hsource.1⟩
  | primedEvenTerminalStrictRight data =>
      have hsource :=
        PrimedEvenTerminalStrictRightProp49AtomData.atom_threshold_fixed data
      exact ⟨atom_subset_prefixPairingEvent_xEast_of_threshold_fixed
          hsource.1 hsource.2 data.creation_pairFree,
        atom_subset_directAvoidance_two_of_threshold_two
          data.m_pos hsource.1⟩

/-- At the second source stage (`stageNumber 1 = 2`), the raw creation set
and the terminal endpoint carried by each of the four literal stopped
encodings already determine the ordered creation tuple.  No complement
coordinate hypothesis is needed. -/
theorem ConcreteStoppedProp49AtomData.fullComplementOrderedCreationDetermined_stageOne_xEast
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : ConcreteStoppedProp49AtomData m 2 A alpha screen)
    (c : Fin 2 → Site) :
    ConcreteStoppedProp49AtomData.FullComplementOrderedCreationDetermined
      (r := (1 : StageIndex)) D c := by
  cases D with
  | unprimedEvenLeft data =>
      let activeBases :=
        unprimedEvenLeftWinnerBases data.labels data.candidateBases
      have hsource :=
        Erdos1166.HLOZStoppedFullComplement.UnprimedEvenLeftWinnerProp49AtomData.atom_threshold_fixed
          data
      apply
        eventDeterminedByOn_orderedCreationSitesEvent_two_of_fixed_source_last
          data.atom
          (unprimedEvenFullComplementPath m 2 data.C data.labels activeBases)
          m data.C (stoppedTerminalBase data.labels) c data.m_pos
          hsource.1 hsource.2
      rintro s ⟨omega, homega, rfl⟩
      exact
        levelCreationSite_eq_stoppedTerminalBase_of_mem_actualStoppedVectorEvent
          homega.1
  | primedOddStrictRight data =>
      let activeBases :=
        primedOddStrictRightWinnerBases data.first data.labels
          data.candidateBases
      have hsource :=
        Erdos1166.HLOZStoppedFullComplement.PrimedOddStrictRightWinnerProp49AtomData.atom_threshold_fixed
          data
      apply
        eventDeterminedByOn_orderedCreationSitesEvent_two_of_fixed_source_last
          data.atom
          (primedOddFullComplementPath m 2 data.C data.first data.labels
          activeBases)
          m data.C (primedStoppedTerminalSite data.first data.labels) c
          data.m_pos hsource.1 hsource.2
      rintro s ⟨omega, homega, rfl⟩
      exact
        levelCreationSite_eq_primedStoppedTerminalSite_of_mem_actualPrimedStoppedVectorEvent
          homega.1
  | unprimedOddTerminalTieLeft data =>
      let activeBases := unprimedOddTieLeftWinnerBases data.labels
        (unprimedOddTerminalExternalRight data.labels data.terminal)
          data.candidateBases
      have hsource :=
        Erdos1166.HLOZStoppedFullComplement.UnprimedOddTerminalTieLeftProp49AtomData.atom_threshold_fixed
          data
      apply
        eventDeterminedByOn_orderedCreationSitesEvent_two_of_fixed_source_last
          data.atom
          (unprimedOddTerminalFullComplementPath m 2 data.C data.labels
            data.terminal activeBases)
          m data.C
          (stoppedTerminalBase data.labels + directionStep (data.terminal 0))
          c data.m_pos hsource.1 hsource.2
      rintro s ⟨omega, homega, rfl⟩
      exact
        levelCreationSite_eq_unprimedOddTerminal_of_mem_actualOddStoppedVectorEvent
          homega.1
  | primedEvenTerminalStrictRight data =>
      let activeBases := primedEvenStrictRightWinnerBases data.first
        data.labels
          (primedEvenTerminalExternalLeft data.first data.labels data.terminal)
            data.candidateBases
      have hsource :=
        Erdos1166.HLOZStoppedFullComplement.PrimedEvenTerminalStrictRightProp49AtomData.atom_threshold_fixed
          data
      apply
        eventDeterminedByOn_orderedCreationSitesEvent_two_of_fixed_source_last
          data.atom
          (primedEvenTerminalFullComplementPath m 2 data.C data.first
            data.labels data.terminal activeBases)
          m data.C
          (primedStoppedTerminalSite data.first data.labels +
            directionStep (data.terminal 0))
          c data.m_pos hsource.1 hsource.2
      rintro s ⟨omega, homega, rfl⟩
      exact
        levelCreationSite_eq_primedEvenTerminal_of_mem_actualPrimedTerminalVectorEvent
          homega.1

/-- On a two-site threshold atom, fibrewise determination of every exact
ordered creation tuple implies determination of the first distance bin. -/
theorem eventDeterminedByOn_distanceBinEvent_one_of_ordered_two
    {Z : Type*} (atom : Set Path) (z : Path → Z) (m : ℕ) (beta : ℝ)
    (hthreshold : atom ⊆ hlozThresholdTimeEventK m 2)
    (hordered : ∀ c : Fin 2 → Site,
      EventDeterminedByOn atom (orderedCreationSitesEvent m 2 c) z) :
    EventDeterminedByOn atom (distanceBinEvent m 1 beta) z := by
  intro s hs t ht hz
  have htuple : orderedCreationSites m 2 s =
      orderedCreationSites m 2 t := by
    let c := orderedCreationSites m 2 s
    have hiff := hordered c s hs t ht hz
    have hsMem : s ∈ orderedCreationSitesEvent m 2 c := by
      exact rfl
    have htMem := hiff.mp hsMem
    change orderedCreationSites m 2 t = c at htMem
    exact htMem.symm
  have hsiteOne : levelCreationSite s m 1 = levelCreationSite t m 1 := by
    have h := congrFun htuple (0 : Fin 2)
    norm_num [orderedCreationSites] at h
    exact h
  have hsiteTwo : levelCreationSite s m 2 = levelCreationSite t m 2 := by
    have h := congrFun htuple (1 : Fin 2)
    norm_num [orderedCreationSites] at h
    exact h
  have htwoS : firstKSitesReachLevel m 2 s ≠ ⊤ :=
    ne_top_of_lt (hthreshold hs)
  have htwoT : firstKSitesReachLevel m 2 t ≠ ⊤ :=
    ne_top_of_lt (hthreshold ht)
  have honeS : firstKSitesReachLevel m 1 s ≠ ⊤ :=
    by
      intro hone
      have hle := firstKSitesReachLevel_mono_k s m (show 1 ≤ 2 by omega)
      apply htwoS
      exact top_unique (by simpa only [hone] using hle)
  have honeT : firstKSitesReachLevel m 1 t ≠ ⊤ :=
    by
      intro hone
      have hle := firstKSitesReachLevel_mono_k t m (show 1 ≤ 2 by omega)
      apply htwoT
      exact top_unique (by simpa only [hone] using hle)
  simp only [distanceBinEvent, Set.mem_ofPred_eq, honeS, htwoS, honeT,
    htwoT, ne_eq, not_false_eq_true, true_and, hsiteOne, hsiteTwo]

/-- The first distance-bin event is therefore determined on every literal
two-site branch without any probabilistic input. -/
theorem ConcreteStoppedProp49AtomData.fullComplementDistanceBinDetermined_stageOne_xEast
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : ConcreteStoppedProp49AtomData m 2 A alpha screen) (beta : ℝ) :
    match D with
    | .unprimedEvenLeft data =>
        EventDeterminedByOn data.atom (distanceBinEvent m 1 beta)
          (unprimedEvenFullComplementPath m 2 data.C data.labels
            (unprimedEvenLeftWinnerBases data.labels data.candidateBases))
    | .primedOddStrictRight data =>
        EventDeterminedByOn data.atom (distanceBinEvent m 1 beta)
          (primedOddFullComplementPath m 2 data.C data.first data.labels
            (primedOddStrictRightWinnerBases data.first data.labels
              data.candidateBases))
    | .unprimedOddTerminalTieLeft data =>
        EventDeterminedByOn data.atom (distanceBinEvent m 1 beta)
          (unprimedOddTerminalFullComplementPath m 2 data.C data.labels
            data.terminal
            (unprimedOddTieLeftWinnerBases data.labels
              (unprimedOddTerminalExternalRight data.labels data.terminal)
                data.candidateBases))
    | .primedEvenTerminalStrictRight data =>
        EventDeterminedByOn data.atom (distanceBinEvent m 1 beta)
          (primedEvenTerminalFullComplementPath m 2 data.C data.first
            data.labels data.terminal
            (primedEvenStrictRightWinnerBases data.first data.labels
              (primedEvenTerminalExternalLeft data.first data.labels
                data.terminal) data.candidateBases)) := by
  cases D with
  | unprimedEvenLeft data =>
      apply eventDeterminedByOn_distanceBinEvent_one_of_ordered_two
        data.atom _ m beta
          (UnprimedEvenLeftWinnerProp49AtomData.atom_threshold_fixed data).1
      intro c
      simpa [ConcreteStoppedProp49AtomData.FullComplementOrderedCreationDetermined,
        stageNumber] using
        ConcreteStoppedProp49AtomData.fullComplementOrderedCreationDetermined_stageOne_xEast
          (.unprimedEvenLeft data) c
  | primedOddStrictRight data =>
      apply eventDeterminedByOn_distanceBinEvent_one_of_ordered_two
        data.atom _ m beta
          (PrimedOddStrictRightWinnerProp49AtomData.atom_threshold_fixed data).1
      intro c
      simpa [ConcreteStoppedProp49AtomData.FullComplementOrderedCreationDetermined,
        stageNumber] using
        ConcreteStoppedProp49AtomData.fullComplementOrderedCreationDetermined_stageOne_xEast
          (.primedOddStrictRight data) c
  | unprimedOddTerminalTieLeft data =>
      apply eventDeterminedByOn_distanceBinEvent_one_of_ordered_two
        data.atom _ m beta
          (UnprimedOddTerminalTieLeftProp49AtomData.atom_threshold_fixed data).1
      intro c
      simpa [ConcreteStoppedProp49AtomData.FullComplementOrderedCreationDetermined,
        stageNumber] using
        ConcreteStoppedProp49AtomData.fullComplementOrderedCreationDetermined_stageOne_xEast
          (.unprimedOddTerminalTieLeft data) c
  | primedEvenTerminalStrictRight data =>
      apply eventDeterminedByOn_distanceBinEvent_one_of_ordered_two
        data.atom _ m beta
          (PrimedEvenTerminalStrictRightProp49AtomData.atom_threshold_fixed data).1
      intro c
      simpa [ConcreteStoppedProp49AtomData.FullComplementOrderedCreationDetermined,
        stageNumber] using
        ConcreteStoppedProp49AtomData.fullComplementOrderedCreationDetermined_stageOne_xEast
          (.primedEvenTerminalStrictRight data) c

theorem eventDeterminedByOn_prop47StageEvent_zero_of_lowScaleResidual
    {Z : Type*} (atom : Set Path) (z : Path → Z)
    (profiles : Fin 6 → HLOZProp47SourceObjects.ExternalProfilePair)
    (cStar : Fin 6 → ℝ) (m : ℕ) (a : AlphaTriple)
    (hprefix : atom ⊆ prefixPairingEvent m (xIndex east) 2)
    (havoid : atom ⊆ hlozDirectAvoidanceEvent m 2)
    (hdistance : EventDeterminedByOn atom
      (distanceBinEvent m 1 (alphaValue (tripleAlphaIndex a 0))) z)
    (hresidual : alphaValue (tripleAlphaIndex a 0) ≤ kappaTwo →
      EventDeterminedByOn atom
        (stageZeroLowScaleResidualEvent profiles cStar m a) z) :
    EventDeterminedByOn atom
      (prop47StageEvent profiles cStar (xIndex east) m 0
        (alphaValue (tripleAlphaIndex a 0))) z := by
  rw [prop47StageEvent]
  apply (EventDeterminedByOn.of_subset hprefix).inter
  by_cases halpha : alphaValue (tripleAlphaIndex a 0) ≤ kappaTwo
  · rw [if_pos halpha]
    have hfixed := (EventDeterminedByOn.of_subset havoid).inter hdistance
    have hall := hfixed.inter (hresidual halpha)
    simpa [stageNumber, lowScaleStageEvent,
      stageZeroLowScaleResidualEvent, Set.inter_assoc] using hall
  · rw [if_neg halpha]
    exact (EventDeterminedByOn.of_subset havoid).inter hdistance

/-- At stage one, high-scale stage-zero histories are completely automatic.
In the low-scale case only the candidate/`Theta`/cardinality residual event
must be shown to factor through the chronological complement. -/
theorem ConcreteStoppedProp49AtomData.fullComplementStageZeroDetermined_stageOne_xEast_of_lowScaleResidual
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    {profiles : Fin 6 → HLOZProp47SourceObjects.ExternalProfilePair}
    {cStar : Fin 6 → ℝ} {a : AlphaTriple}
    (D : ConcreteStoppedProp49AtomData m 2 A alpha screen)
    (hresidual : alphaValue (tripleAlphaIndex a 0) ≤ kappaTwo →
      ConcreteStoppedProp49AtomData.FullComplementStageZeroLowScaleDetermined
        (profiles := profiles) (cStar := cStar) (a := a)
          (r := (1 : StageIndex)) D) :
    ConcreteStoppedProp49AtomData.FullComplementStageZeroDetermined
      (profiles := profiles) (cStar := cStar) (a := a)
        (r := (1 : StageIndex)) D := by
  have hfixed :=
    ConcreteStoppedProp49AtomData.atom_subset_stageZero_fixed_events_xEast D
  have hdistance :=
    ConcreteStoppedProp49AtomData.fullComplementDistanceBinDetermined_stageOne_xEast
      D (alphaValue (tripleAlphaIndex a 0))
  cases D with
  | unprimedEvenLeft data =>
      simpa [ConcreteStoppedProp49AtomData.FullComplementStageZeroDetermined,
        stageNumber] using
        eventDeterminedByOn_prop47StageEvent_zero_of_lowScaleResidual
          data.atom _ profiles cStar m a hfixed.1 hfixed.2 hdistance
          (fun ha ↦ by
            simpa [ConcreteStoppedProp49AtomData.FullComplementStageZeroLowScaleDetermined,
              stageNumber] using
              hresidual ha)
  | primedOddStrictRight data =>
      simpa [ConcreteStoppedProp49AtomData.FullComplementStageZeroDetermined,
        stageNumber] using
        eventDeterminedByOn_prop47StageEvent_zero_of_lowScaleResidual
          data.atom _ profiles cStar m a hfixed.1 hfixed.2 hdistance
          (fun ha ↦ by
            simpa [ConcreteStoppedProp49AtomData.FullComplementStageZeroLowScaleDetermined,
              stageNumber] using
              hresidual ha)
  | unprimedOddTerminalTieLeft data =>
      simpa [ConcreteStoppedProp49AtomData.FullComplementStageZeroDetermined,
        stageNumber] using
        eventDeterminedByOn_prop47StageEvent_zero_of_lowScaleResidual
          data.atom _ profiles cStar m a hfixed.1 hfixed.2 hdistance
          (fun ha ↦ by
            simpa [ConcreteStoppedProp49AtomData.FullComplementStageZeroLowScaleDetermined,
              stageNumber] using
              hresidual ha)
  | primedEvenTerminalStrictRight data =>
      simpa [ConcreteStoppedProp49AtomData.FullComplementStageZeroDetermined,
        stageNumber] using
        eventDeterminedByOn_prop47StageEvent_zero_of_lowScaleResidual
          data.atom _ profiles cStar m a hfixed.1 hfixed.2 hdistance
          (fun ha ↦ by
            simpa [ConcreteStoppedProp49AtomData.FullComplementStageZeroLowScaleDetermined,
              stageNumber] using
              hresidual ha)

/-- Consequently, at stage one the only nonautomatic part of the
full-complement history criterion is determination of the preceding stage-0
screen.  The ordered two-site tuple and the initial X-east pairing event are
both supplied by the literal stopped atom itself. -/
theorem ConcreteStoppedProp49AtomData.fullComplementHistoryDetermined_stageOne_xEast_of_priorStages
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    {profiles : Fin 6 → HLOZProp47SourceObjects.ExternalProfilePair}
    {cStar : Fin 6 → ℝ} {a : AlphaTriple}
    (D : ConcreteStoppedProp49AtomData m 2 A alpha screen)
    (c : Fin 2 → Site)
    (hstage :
      ConcreteStoppedProp49AtomData.FullComplementPriorStagesDetermined
        (profiles := profiles) (cStar := cStar) (i := xIndex east)
          (a := a) (r := (1 : StageIndex)) D) :
    ConcreteStoppedProp49AtomData.FullComplementHistoryDetermined D
      (profiles := profiles) (cStar := cStar) (i := xIndex east)
        (a := a) (r := (1 : StageIndex)) c := by
  exact
    ConcreteStoppedProp49AtomData.fullComplementHistoryDetermined_of_stages
      (profiles := profiles) (cStar := cStar) (i := xIndex east)
      (a := a) (r := (1 : StageIndex)) D c
      (ConcreteStoppedProp49AtomData.fullComplementOrderedCreationDetermined_stageOne_xEast
        D c)
      (ConcreteStoppedProp49AtomData.fullComplementBasePairingDetermined_xEast
        (r := (1 : StageIndex)) D)
      hstage

theorem ConcreteStoppedProp49AtomData.fullComplementHistoryDetermined_stageOne_xEast_of_stageZero
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    {profiles : Fin 6 → HLOZProp47SourceObjects.ExternalProfilePair}
    {cStar : Fin 6 → ℝ} {a : AlphaTriple}
    (D : ConcreteStoppedProp49AtomData m 2 A alpha screen)
    (c : Fin 2 → Site)
    (hzero : ConcreteStoppedProp49AtomData.FullComplementStageZeroDetermined
      (profiles := profiles) (cStar := cStar) (a := a)
        (r := (1 : StageIndex)) D) :
    ConcreteStoppedProp49AtomData.FullComplementHistoryDetermined D
      (profiles := profiles) (cStar := cStar) (i := xIndex east)
        (a := a) (r := (1 : StageIndex)) c := by
  apply
    ConcreteStoppedProp49AtomData.fullComplementHistoryDetermined_stageOne_xEast_of_priorStages
      D c
  exact
    ConcreteStoppedProp49AtomData.fullComplementPriorStagesDetermined_stageOne_of_stageZero
      D hzero

theorem unprimedEvenLeftWinnerProp49_fullComplement_stageZero_screenEstimate
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    {profiles : Fin 6 → HLOZProp47SourceObjects.ExternalProfilePair}
    {cStar : Fin 6 → ℝ} {a : AlphaTriple}
    (D : UnprimedEvenLeftWinnerProp49AtomData m 1 A alpha screen)
    (c : Fin 1 → Site) :
    RefinedAtomScreenEstimate
      (orderedProfileHistoryPathAtom profiles cStar m
        (HLOZPairing.xIndex HLOZPairing.east) a 0 c D.atom)
      screen (sourceProp49ScreenRate m A alpha) := by
  let activeBases := unprimedEvenLeftWinnerBases D.labels D.candidateBases
  let z := unprimedEvenFullComplementPath m 1 D.C D.labels activeBases
  have hsource :=
    Erdos1166.HLOZStoppedFullComplement.UnprimedEvenLeftWinnerProp49AtomData.atom_threshold_fixed D
  have hdet : EventDeterminedByOn D.atom
      (orderedProfileHistoryEvent profiles cStar m
        (HLOZPairing.xIndex HLOZPairing.east) a 0 c) z := by
    apply eventDeterminedByOn_orderedProfileHistoryEvent_zero_of_fixed_source
      D.atom z profiles cStar m (HLOZPairing.xIndex HLOZPairing.east) a
        D.C c hsource.1 hsource.2
    simpa using D.creation_pairFree
  simpa only [stageNumber] using
    unprimedEvenLeftWinnerProp49_fullComplement_orderedProfileHistory_screenEstimate_of_fiberwise
      (profiles := profiles) (cStar := cStar)
      (i := HLOZPairing.xIndex HLOZPairing.east) (a := a)
      (r := (0 : StageIndex)) D c hdet

theorem primedOddStrictRightWinnerProp49_fullComplement_stageZero_screenEstimate
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    {profiles : Fin 6 → HLOZProp47SourceObjects.ExternalProfilePair}
    {cStar : Fin 6 → ℝ} {a : AlphaTriple}
    (D : PrimedOddStrictRightWinnerProp49AtomData m 1 A alpha screen)
    (c : Fin 1 → Site) :
    RefinedAtomScreenEstimate
      (orderedProfileHistoryPathAtom profiles cStar m
        (HLOZPairing.xIndex HLOZPairing.east) a 0 c D.atom)
      screen (sourceProp49ScreenRate m A alpha) := by
  let activeBases :=
    primedOddStrictRightWinnerBases D.first D.labels D.candidateBases
  let z := primedOddFullComplementPath
    m 1 D.C D.first D.labels activeBases
  have hsource :=
    Erdos1166.HLOZStoppedFullComplement.PrimedOddStrictRightWinnerProp49AtomData.atom_threshold_fixed D
  have hdet : EventDeterminedByOn D.atom
      (orderedProfileHistoryEvent profiles cStar m
        (HLOZPairing.xIndex HLOZPairing.east) a 0 c) z := by
    apply eventDeterminedByOn_orderedProfileHistoryEvent_zero_of_fixed_source
      D.atom z profiles cStar m (HLOZPairing.xIndex HLOZPairing.east) a
        D.C c hsource.1 hsource.2
    simpa using D.creation_pairFree
  simpa only [stageNumber] using
    primedOddStrictRightWinnerProp49_fullComplement_orderedProfileHistory_screenEstimate_of_fiberwise
      (profiles := profiles) (cStar := cStar)
      (i := HLOZPairing.xIndex HLOZPairing.east) (a := a)
      (r := (0 : StageIndex)) D c hdet

theorem unprimedOddTerminalTieLeftProp49_fullComplement_stageZero_screenEstimate
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    {profiles : Fin 6 → HLOZProp47SourceObjects.ExternalProfilePair}
    {cStar : Fin 6 → ℝ} {a : AlphaTriple}
    (D : UnprimedOddTerminalTieLeftProp49AtomData m 1 A alpha screen)
    (c : Fin 1 → Site) :
    RefinedAtomScreenEstimate
      (orderedProfileHistoryPathAtom profiles cStar m
        (HLOZPairing.xIndex HLOZPairing.east) a 0 c D.atom)
      screen (sourceProp49ScreenRate m A alpha) := by
  let externalRight :=
    unprimedOddTerminalExternalRight D.labels D.terminal
  let activeBases := unprimedOddTieLeftWinnerBases D.labels
    externalRight D.candidateBases
  let z := unprimedOddTerminalFullComplementPath
    m 1 D.C D.labels D.terminal activeBases
  have hsource :=
    Erdos1166.HLOZStoppedFullComplement.UnprimedOddTerminalTieLeftProp49AtomData.atom_threshold_fixed D
  have hdet : EventDeterminedByOn D.atom
      (orderedProfileHistoryEvent profiles cStar m
        (HLOZPairing.xIndex HLOZPairing.east) a 0 c) z := by
    apply eventDeterminedByOn_orderedProfileHistoryEvent_zero_of_fixed_source
      D.atom z profiles cStar m (HLOZPairing.xIndex HLOZPairing.east) a
        D.C c hsource.1 hsource.2
    simpa using D.creation_pairFree
  simpa only [stageNumber] using
    unprimedOddTerminalTieLeftProp49_fullComplement_orderedProfileHistory_screenEstimate_of_fiberwise
      (profiles := profiles) (cStar := cStar)
      (i := HLOZPairing.xIndex HLOZPairing.east) (a := a)
      (r := (0 : StageIndex)) D c hdet

theorem primedEvenTerminalStrictRightProp49_fullComplement_stageZero_screenEstimate
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    {profiles : Fin 6 → HLOZProp47SourceObjects.ExternalProfilePair}
    {cStar : Fin 6 → ℝ} {a : AlphaTriple}
    (D : PrimedEvenTerminalStrictRightProp49AtomData m 1 A alpha screen)
    (c : Fin 1 → Site) :
    RefinedAtomScreenEstimate
      (orderedProfileHistoryPathAtom profiles cStar m
        (HLOZPairing.xIndex HLOZPairing.east) a 0 c D.atom)
      screen (sourceProp49ScreenRate m A alpha) := by
  let externalLeft :=
    primedEvenTerminalExternalLeft D.first D.labels D.terminal
  let activeBases := primedEvenStrictRightWinnerBases D.first D.labels
    externalLeft D.candidateBases
  let z := primedEvenTerminalFullComplementPath
    m 1 D.C D.first D.labels D.terminal activeBases
  have hsource :=
    Erdos1166.HLOZStoppedFullComplement.PrimedEvenTerminalStrictRightProp49AtomData.atom_threshold_fixed D
  have hdet : EventDeterminedByOn D.atom
      (orderedProfileHistoryEvent profiles cStar m
        (HLOZPairing.xIndex HLOZPairing.east) a 0 c) z := by
    apply eventDeterminedByOn_orderedProfileHistoryEvent_zero_of_fixed_source
      D.atom z profiles cStar m (HLOZPairing.xIndex HLOZPairing.east) a
        D.C c hsource.1 hsource.2
    simpa using D.creation_pairFree
  simpa only [stageNumber] using
    primedEvenTerminalStrictRightProp49_fullComplement_orderedProfileHistory_screenEstimate_of_fiberwise
      (profiles := profiles) (cStar := cStar)
      (i := HLOZPairing.xIndex HLOZPairing.east) (a := a)
      (r := (0 : StageIndex)) D c hdet

/-- The four literal X-east stopped source atoms at the first screening
stage.  Their stopped laws and their complete ordered-history tower are
both internal to this sum type. -/
inductive XEastStageZeroProp49AtomData
    (m A : ℕ) (alpha : ℝ) (screen : Set Path) where
  | unprimedEven
      (data : UnprimedEvenLeftWinnerProp49AtomData m 1 A alpha screen)
  | primedOdd
      (data : PrimedOddStrictRightWinnerProp49AtomData m 1 A alpha screen)
  | unprimedOddTerminal
      (data : UnprimedOddTerminalTieLeftProp49AtomData m 1 A alpha screen)
  | primedEvenTerminal
      (data : PrimedEvenTerminalStrictRightProp49AtomData m 1 A alpha screen)

noncomputable def XEastStageZeroProp49AtomData.atom
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : XEastStageZeroProp49AtomData m A alpha screen) : Set Path :=
  match D with
  | .unprimedEven data => data.atom
  | .primedOdd data => data.atom
  | .unprimedOddTerminal data => data.atom
  | .primedEvenTerminal data => data.atom

theorem XEastStageZeroProp49AtomData.m_pos
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : XEastStageZeroProp49AtomData m A alpha screen) : 0 < m := by
  cases D with
  | unprimedEven data => exact data.m_pos
  | primedOdd data => exact data.m_pos
  | unprimedOddTerminal data => exact data.m_pos
  | primedEvenTerminal data => exact data.m_pos

theorem XEastStageZeroProp49AtomData.measurableSet_atom
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    (D : XEastStageZeroProp49AtomData m A alpha screen) :
    MeasurableSet D.atom := by
  cases D with
  | unprimedEven data => exact data.toInput.measurable_atom
  | primedOdd data => exact data.toInput.measurable_atom
  | unprimedOddTerminal data => exact data.toInput.measurable_atom
  | primedEvenTerminal data => exact data.toInput.measurable_atom

/-- A first-stage literal atom has the uniform narrow-band estimate after
refinement by its unique ordered creation site and the complete zero-stage
history, for any profile family. -/
theorem XEastStageZeroProp49AtomData.screenEstimate
    {m A : ℕ} {alpha : ℝ} {screen : Set Path}
    {profiles : Fin 6 → HLOZProp47SourceObjects.ExternalProfilePair}
    {cStar : Fin 6 → ℝ} {a : AlphaTriple}
    (D : XEastStageZeroProp49AtomData m A alpha screen)
    (c : Fin 1 → Site) :
    RefinedAtomScreenEstimate
      (orderedProfileHistoryPathAtom profiles cStar m
        (HLOZPairing.xIndex HLOZPairing.east) a 0 c D.atom)
      screen (sourceProp49ScreenRate m A alpha) := by
  cases D with
  | unprimedEven data =>
      exact
        unprimedEvenLeftWinnerProp49_fullComplement_stageZero_screenEstimate
          data c
  | primedOdd data =>
      exact
        primedOddStrictRightWinnerProp49_fullComplement_stageZero_screenEstimate
          data c
  | unprimedOddTerminal data =>
      exact
        unprimedOddTerminalTieLeftProp49_fullComplement_stageZero_screenEstimate
          data c
  | primedEvenTerminal data =>
      exact
        primedEvenTerminalStrictRightProp49_fullComplement_stageZero_screenEstimate
          data c

end Erdos1166.HLOZStoppedFullComplement
